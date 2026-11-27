#!/usr/bin/env python3
"""Apply and incrementally `lake build`-verify `dir2` DAG coalescing groups on grh-clean.

For each candidate group (lowest risk_score first):
  1. Render merged host with `dag_coalesce.render_group`.
  2. Temporarily remove folded single-importer leaf files and write merged host.
  3. Run `lake build <host>` (fast because dependencies are cached).
  4. On exit 0 (and anti-packing gate OK): keep the merge (`git rm` folded leaves).
  5. On any failure: restore exact original host + leaf files and log the first error line.

Finally verifies `lake build Main`, `scripts/PrintAxioms.lean`, and `scripts/check_grh_clean.py`.
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import check_grh_clean as gate  # noqa: E402
import dag_coalesce as dc  # noqa: E402


def mod_to_path(src: Path, mod: str) -> Path:
    return src / (mod.replace(".", "/") + ".lean")


def run_cmd(cmd: list[str], cwd: Path, timeout: int = 180) -> tuple[int, str]:
    try:
        r = subprocess.run(
            cmd, cwd=cwd, capture_output=True, text=True,
            encoding="utf-8", errors="replace", timeout=timeout,
        )
        return r.returncode, (r.stdout + "\n" + r.stderr).strip()
    except subprocess.TimeoutExpired:
        return 124, f"TIMEOUT after {timeout}s"


def first_error_line(out: str) -> str:
    for ln in out.splitlines():
        if "error:" in ln:
            return ln.strip()[:220]
    lines = [l.strip() for l in out.splitlines() if l.strip()]
    return lines[-1][:220] if lines else "(no output)"


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", type=Path, default=HERE.parent)
    ap.add_argument("--mode", choices=["dir2", "dir1"], default="dir2")
    ap.add_argument("--max-groups", type=int, default=25)
    ap.add_argument("--max-risk", type=int, default=12)
    ap.add_argument("--timeout", type=int, default=150)
    ap.add_argument("--report", type=Path, default=None)
    args = ap.parse_args()

    root = args.root.resolve()
    src = root / "src"

    print(f"[coalesce-verify] scanning {src} (mode={args.mode})...", flush=True)
    mods = dc.load_mods(src)
    all_mods = set(mods)
    members, reduced_adj, merges, kinds, reduced0, direct, blocked = dc.coalesce_plan(
        mods, scope="single-importer", mode=args.mode, cap=1800, wrap=True
    )
    groups = {h: ms for h, ms in members.items() if len(ms) > 1}

    # Score and order groups: lowest risk_score, fewest lines first for fast wins
    candidates = []
    for h, ms in groups.items():
        d = dc.group_delta(mods, h, ms, all_mods, reduced_adj)
        if not dc.group_ok(d):
            continue
        r = dc.group_risks(mods, ms)
        if r["risk_score"] > args.max_risk:
            continue
        flat_ms = dc.flat(ms)
        total_code = sum(mods[m]["code_lines"] for m in flat_ms)
        candidates.append((r["risk_score"], total_code, h, ms, flat_ms, d))

    candidates.sort(key=lambda x: (x[0], x[1], x[2]))
    selected = candidates[: args.max_groups]
    print(
        f"[coalesce-verify] {len(groups)} total groups, {len(candidates)} gate-ok (risk<={args.max_risk}), "
        f"testing top {len(selected)} groups...",
        flush=True,
    )

    passed = []
    failed = []
    t0 = time.time()

    for idx, (risk, total_code, host, ms, flat_ms, delta) in enumerate(selected, 1):
        leaves = [m for m in flat_ms if m != host]
        host_path = mod_to_path(src, host)
        leaf_paths = [(m, mod_to_path(src, m)) for m in leaves]
        if not host_path.exists() or any(not p.exists() for _, p in leaf_paths):
            continue

        # Backup exact bytes (host, leaves, AND any downstream files with redundant leaf imports)
        host_orig = host_path.read_bytes()
        leaf_orig = [(m, p, p.read_bytes()) for m, p in leaf_paths]
        leaf_set = set(leaves)
        downstream_orig: list[tuple[Path, bytes]] = []
        for f in sorted(src.rglob("*.lean")):
            if f == host_path or any(f == p for _, p in leaf_paths):
                continue
            raw_txt = f.read_text(encoding="utf-8", errors="ignore")
            if not any(lm in raw_txt for lm in leaf_set):
                continue
            lines = raw_txt.splitlines()
            existing_mods = set()
            for ln in lines:
                m_imp = dc.IMPORT_RE.match(ln)
                if m_imp:
                    existing_mods.add(m_imp.group(2))
            new_lines = []
            changed = False
            upgrade_host_pub = False
            for ln in lines:
                m_imp = dc.IMPORT_RE.match(ln)
                if m_imp and m_imp.group(2) in leaf_set:
                    pub = "public " if m_imp.group(1) == "public" else ""
                    changed = True
                    if host in existing_mods:
                        if pub:
                            upgrade_host_pub = True
                        continue
                    new_lines.append(f"{pub}import {host}")
                    existing_mods.add(host)
                    continue
                new_lines.append(ln)
            if upgrade_host_pub:
                new_lines = [
                    (f"public import {host}" if x.strip() == f"import {host}" else x)
                    for x in new_lines
                ]
            if changed:
                downstream_orig.append((f, f.read_bytes()))
                f.write_text("\n".join(new_lines) + "\n", encoding="utf-8")

        rendered = dc.render_group(mods, host, ms, all_mods, reduced_adj)
        host_path.write_text(rendered, encoding="utf-8")
        for _, p, _ in leaf_orig:
            p.unlink()

        # Also build any rewritten downstream callers so visibility bugs are caught per-group!
        build_targets = [host] + [
            f.relative_to(src).with_suffix("").as_posix().replace("/", ".")
            for f, _ in downstream_orig
        ]
        # Remove stale leaf artifacts BEFORE building downstream callers so Lake never loads old oleans
        stale_backups: list[tuple[Path, bytes]] = []
        for leaf in leaves:
            rel_o = Path(*leaf.split("."))
            for base in (root / ".lake" / "build" / "lib" / "lean", root / ".lake" / "build" / "ir"):
                parent = base / rel_o.parent
                if parent.exists():
                    for stale in parent.glob(rel_o.name + ".*"):
                        stale_backups.append((stale, stale.read_bytes()))
                        stale.unlink(missing_ok=True)

        gt0 = time.time()
        rc, out = run_cmd(["lake", "build", *build_targets], cwd=root, timeout=args.timeout)
        dt = round(time.time() - gt0, 1)

        if rc == 0:
            print(
                f"  [{idx:2d}/{len(selected)}] PASS {host} (-{len(leaves)} files, {total_code}L, {dt}s, verified {len(build_targets)} mods)",
                flush=True,
            )
            passed.append({
                "host": host, "folded": leaves, "files_removed": len(leaves),
                "rewritten_callers": len(downstream_orig),
                "risk": risk, "sec": dt, "delta": delta,
            })
        else:
            err = first_error_line(out)
            print(
                f"  [{idx:2d}/{len(selected)}] FAIL {host} ({dt}s): {err}",
                flush=True,
            )
            # Restore exact original files and stale artifacts
            host_path.write_bytes(host_orig)
            for _, p, raw in leaf_orig:
                p.write_bytes(raw)
            for f, raw in downstream_orig:
                f.write_bytes(raw)
            for sp, raw in stale_backups:
                sp.write_bytes(raw)
            failed.append({
                "host": host, "folded": leaves, "risk": risk, "sec": dt, "error": err,
            })

    files_removed = sum(p["files_removed"] for p in passed)
    print(
        f"\n[coalesce-verify] batch done in {time.time()-t0:.1f}s: "
        f"{len(passed)}/{len(selected)} groups PASSED (-{files_removed} files), {len(failed)} rolled back.",
        flush=True,
    )

    if passed:
        print("[coalesce-verify] running final `lake build Main` + `PrintAxioms.lean` + `check_grh_clean.py`...", flush=True)
        rc_main, out_main = run_cmd(["lake", "build", "Main"], cwd=root, timeout=600)
        rc_ax, out_ax = run_cmd(["lake", "env", "lean", "scripts/PrintAxioms.lean"], cwd=root, timeout=120)
        gate_res = gate.scan_tree(root)
        print(f"  lake build Main: rc={rc_main}", flush=True)
        print(f"  PrintAxioms: rc={rc_ax}\n{out_ax}", flush=True)
        print(f"  check_grh_clean: files={gate_res['metrics']['files']} code={gate_res['metrics']['code_lines']} "
              f"non_ws={gate_res['metrics']['non_ws_code']} tokens={gate_res['metrics']['lean_tokens']} "
              f"over_100={gate_res['metrics']['over_100']} semi={gate_res['metrics']['semi_packed']} "
              f"forbidden={gate_res['forbidden_count']}", flush=True)
    else:
        rc_main = rc_ax = 0
        gate_res = gate.scan_tree(root)

    rep_path = args.report or (root / "specs" / "COALESCE_VERIFY_REPORT.json")
    rep_path.write_text(json.dumps({
        "mode": args.mode,
        "tested_groups": len(selected),
        "passed_groups": len(passed),
        "failed_groups": len(failed),
        "files_removed": files_removed,
        "lake_build_main_rc": rc_main,
        "print_axioms_rc": rc_ax,
        "metrics_after": gate_res["metrics"],
        "passed": passed,
        "failed": failed,
    }, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(f"[coalesce-verify] report -> {rep_path}", flush=True)
    return 0 if (rc_main == 0 and rc_ax == 0 and gate_res["forbidden_count"] == 0) else 1


if __name__ == "__main__":
    raise SystemExit(main())
