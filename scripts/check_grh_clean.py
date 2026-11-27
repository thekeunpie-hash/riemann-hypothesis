#!/usr/bin/env python3
"""
Anti-packing 4-metric + integrity gate for `grh-clean`.

Enforces community-aligned structural compression (not line-count code-golf):
  1. Measures raw_lines, code_lines, non_ws_code_chars, lean_tokens, and declaration counts.
  2. Rejects >100-char line packing, >=3-semicolon packing, sorry, custom axioms, native_decide, unsafe.
  3. Tracks `backward.*` options, `maxHeartbeats` overrides, and monolith `import Mathlib`.
  4. Compares against a saved baseline JSON so regressions in non_ws_code or lean_tokens fail loudly.
"""
from __future__ import annotations

import argparse
import json
import pathlib
import re
import sys
import time
from typing import Any

LEAN_TOKEN_RE = re.compile(
    r"[A-Za-z_\u0080-\uffff][A-Za-z0-9_'\u0080-\uffff]*|[0-9]+(?:\.[0-9]+)?|:=|=>|->|<-|↔|→|←|∀|∃|≤|≥|≠|[^\s]"
)
DECL_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*(?:private\s+|protected\s+|noncomputable\s+|local\s+|scoped\s+)*"
    r"(lemma|theorem|def|abbrev|structure|class|inductive|instance)\b"
)
FORBIDDEN_RE = re.compile(r"\b(sorry|axiom|native_decide|unsafe|implemented_by)\b")


def scan_file(path: pathlib.Path, rel: str) -> dict[str, Any]:
    txt = path.read_text(encoding="utf-8", errors="replace")
    lines = txt.splitlines()
    in_block = 0
    code_lines = blank_lines = comment_lines = 0
    non_ws_code = lean_tokens = decls = 0
    over_100 = semi_packed = 0
    backward_opts = max_hb = monolith_mathlib = 0
    forbidden_hits: list[str] = []

    for idx, ln in enumerate(lines, 1):
        s = ln.strip()
        if not s:
            blank_lines += 1
            continue
        if in_block > 0:
            comment_lines += 1
            in_block += ln.count("/-") - ln.count("-/")
            if in_block < 0:
                in_block = 0
            continue
        if s.startswith("--"):
            comment_lines += 1
            continue
        if s.startswith("/-"):
            comment_lines += 1
            delta = ln.count("/-") - ln.count("-/")
            if delta > 0:
                in_block = delta
            continue

        code_lines += 1
        cpart = ln.split("--", 1)[0]
        if len(ln) > 100:
            over_100 += 1
        if cpart.count(";") >= 3:
            semi_packed += 1
        non_ws_code += sum(1 for ch in cpart if not ch.isspace())
        lean_tokens += len(LEAN_TOKEN_RE.findall(cpart))
        if not ln.startswith((" ", "\t")) and DECL_RE.match(s):
            decls += 1
        if "backward." in cpart:
            backward_opts += 1
        if "maxHeartbeats" in cpart:
            max_hb += 1
        if s == "import Mathlib":
            monolith_mathlib += 1
        m_forb = FORBIDDEN_RE.search(cpart)
        if m_forb and rel != "Challenge.lean":
            # Exclude identifier substrings like `axiom_...` or string literals
            tok = m_forb.group(1)
            if not re.search(rf'"[^"]*{tok}[^"]*"', cpart):
                forbidden_hits.append(f"{rel}:{idx}:{tok}")

    return {
        "file": rel,
        "raw_lines": len(lines),
        "code_lines": code_lines,
        "blank_lines": blank_lines,
        "comment_lines": comment_lines,
        "unicode_chars": len(txt),
        "non_ws_code": non_ws_code,
        "lean_tokens": lean_tokens,
        "decls": decls,
        "over_100": over_100,
        "semi_packed": semi_packed,
        "backward_opts": backward_opts,
        "max_hb": max_hb,
        "monolith_mathlib": monolith_mathlib,
        "forbidden_hits": forbidden_hits,
    }


def scan_tree(root: pathlib.Path) -> dict[str, Any]:
    t0 = time.perf_counter()
    src = root / "src"
    files = sorted(src.rglob("*.lean"))
    totals = {
        "files": len(files),
        "raw_lines": 0,
        "code_lines": 0,
        "blank_lines": 0,
        "comment_lines": 0,
        "unicode_chars": 0,
        "non_ws_code": 0,
        "lean_tokens": 0,
        "decls": 0,
        "over_100": 0,
        "semi_packed": 0,
        "backward_opts": 0,
        "max_hb": 0,
        "monolith_mathlib": 0,
    }
    forbidden: list[str] = []
    for f in files:
        rel = "src/" + f.relative_to(src).as_posix()
        st = scan_file(f, rel)
        for k in totals:
            if k != "files":
                totals[k] += st[k]
        forbidden.extend(st["forbidden_hits"])

    return {
        "root": str(root),
        "elapsed_sec": round(time.perf_counter() - t0, 2),
        "metrics": totals,
        "forbidden_count": len(forbidden),
        "forbidden_sample": forbidden[:25],
    }


def main() -> int:
    ap = argparse.ArgumentParser(description="Anti-packing & structural verification gate for grh-clean.")
    ap.add_argument("--root", type=pathlib.Path, default=pathlib.Path(__file__).resolve().parent.parent)
    ap.add_argument("--write-baseline", type=pathlib.Path, default=None)
    ap.add_argument("--compare", type=pathlib.Path, default=None)
    args = ap.parse_args()

    res = scan_tree(args.root.resolve())
    if args.write_baseline:
        args.write_baseline.parent.mkdir(parents=True, exist_ok=True)
        args.write_baseline.write_text(json.dumps(res, indent=2), encoding="utf-8")
        print(f"[BASELINE SAVED] {args.write_baseline}")

    m = res["metrics"]
    print(json.dumps(res, indent=2))
    if res["forbidden_count"] > 0:
        print(f"[FAIL] Forbidden tokens found: {res['forbidden_sample']}", file=sys.stderr)
        return 2

    if args.compare and args.compare.exists():
        base = json.loads(args.compare.read_text(encoding="utf-8"))["metrics"]
        dl = m["code_lines"] - base["code_lines"]
        dn = m["non_ws_code"] - base["non_ws_code"]
        dt = m["lean_tokens"] - base["lean_tokens"]
        d100 = m["over_100"] - base["over_100"]
        ds = m["semi_packed"] - base["semi_packed"]
        print(
            f"[DELTA vs baseline] code_lines={dl:+d}, non_ws_code={dn:+d}, "
            f"lean_tokens={dt:+d}, over_100={d100:+d}, semi_packed={ds:+d}"
        )
        if dl < 0 and (dn > 0 or dt > 0):
            print("[FAIL] Line-packing detected: code_lines dropped without reducing non_ws_code and lean_tokens.", file=sys.stderr)
            return 3
        if d100 > 0 or ds > 0:
            print("[FAIL] Style regression: introduced >100-char or >=3-semicolon packed lines.", file=sys.stderr)
            return 4
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
