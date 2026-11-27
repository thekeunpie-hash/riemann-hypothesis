#!/usr/bin/env python3
"""Unwrapped binder-sharing DAG module coalescer (v5) retargeted to grh-clean (Lean v4.35.0).

Ported from downloads/grh-compact-w2/build_dag_coalesce.py (v4/v5 unwrapped design). Changes for grh-clean:
  * package root = this repository (`--root`, default: parent of scripts/), sources under `src/`.
  * `--scope single-importer` (default): a module is folded into its importer only when that
    importer is its ONLY project importer in the transitively reduced import graph. Every other
    module that reached it already imports the host, so contraction can never create a cycle and
    no third file needs an import rewrite.
  * plan mode is the default and never touches `src/`: groups are emitted into a private temp dir,
    scored with `scripts/check_grh_clean.py` (same 4-metric anti-packing rules), and a group whose
    emitted text grows code_lines / non_ws_code / lean_tokens / over_100 / semi_packed versus the
    sum of its members is rejected and re-planned (fixpoint).
  * extra merge guards: duplicate top-level `private` names inside one group, `universe` (re-declared
    universes error in one file), notation/macro/syntax, `export`, eof scope order (`namespace` open
    inside a `noncomputable section` cannot be closed by name before the next member).
  * wrap fallback (default; `--no-wrap` = v4 behaviour): a member that cannot share its top-level
    scope (open scoped / set_option / local instance / attribute [-..] / conflicting variable binders /
    seal mismatch / universe on both sides) is folded as a whole subgroup inside `section ... end`, so
    nothing it declares at top level reaches the host body. Unwrapped merges are always preferred.
  * member module docs (`/-! ... -/`) are kept in front of each member body (readable edition).
  * `--emit DST` writes a full coalesced copy to DST, which must be outside `src/` and empty/new;
    nothing is ever deleted.

Pure Python 3.11+ stdlib. Does not run lean or lake.
"""
from __future__ import annotations

import argparse
import datetime as _dt
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from collections import defaultdict
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import check_grh_clean as gate  # noqa: E402  (anti-packing 4-metric gate, same repo)

VERSION = "v6-grh-clean-lean437-module-aware"
PROTECTED_EXACT = {"Main", "Statements", "New.Main"}

MODULE_RE = re.compile(r"^\s*module\s*$")
IMPORT_RE = re.compile(r"^\s*(?:(public)\s+)?import\s+([A-Za-z0-9_.']+)\s*$")
PUB_SECTION_RE = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)*public\s+section\b", re.M)
SYNTAX_HAZARD_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:(?:local|scoped)\s+)?(?:notation|infixl|infixr|infix|prefix|postfix|macro|macro_rules|syntax|elab|elab_rules|declare_)\b",
    re.M,
)
ATTR_ERASE_RE = re.compile(r"^\s*attribute\s+\[-", re.M)
SET_OPT_NO_IN_RE = re.compile(r"^\s*set_option\s+(?!.*\bin\s*$)", re.M)
OPEN_SPECIAL_RE = re.compile(r"^\s*open\s+(?:scoped\b|.*\bhiding\b|.*\bin\s*$)", re.M)
EXPORT_RE = re.compile(r"^\s*export\s+", re.M)
UNIVERSE_RE = re.compile(r"^\s*universe\s+", re.M)
PRIVATE_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*private\s+(?:noncomputable\s+|partial\s+|nonrec\s+)*"
    r"(?:def|theorem|lemma|abbrev|instance|structure|inductive|class)\s+([^\s:({\[]+)",
    re.M,
)
LOCAL_SIMP_RE = re.compile(r"^attribute\s+\[local\s+simp\]", re.M)
def _n(name: str) -> str:
    """Compare Lean names modulo «» escaping (`end «GL»` closes `namespace New.GL`'s last part)."""
    return name.replace("«", "").replace("»", "")


IDENT_RE = re.compile(r"[A-Za-z_\u0080-￿][A-Za-z0-9_'\u0080-￿.]*")


# ---------------------------------------------------------------- parsing (from v4/v5)

def split_var_binders(s: str) -> list[str]:
    out = []
    i, n = 0, len(s)
    while i < n:
        while i < n and s[i].isspace():
            i += 1
        if i >= n:
            break
        ch = s[i]
        if ch in "{([⦃":
            close = {"{": "}", "(": ")", "[": "]", "⦃": "⦄"}[ch]
            depth, j = 0, i
            while j < n:
                if s[j] == ch:
                    depth += 1
                elif s[j] == close:
                    depth -= 1
                    if depth == 0:
                        j += 1
                        break
                j += 1
            out.append(" ".join(s[i:j].split()))
            i = j
        else:
            j = i
            while j < n and not s[j].isspace():
                j += 1
            out.append(s[i:j])
            i = j
    return out


def binder_names(binder: str) -> list[str]:
    if not binder:
        return []
    if binder[0] == "[":
        inner = binder[1:-1].strip()
        if ":" in inner:
            lhs = inner.split(":", 1)[0].strip()
            return lhs.split() if lhs else [binder]
        return [binder]
    if binder[0] in "{(⦃":
        inner = binder[1:-1].strip()
        lhs = inner.split(":", 1)[0].strip()
        return [t for t in lhs.split() if t]
    return [binder]


def header_end(lines: list[str]) -> int:
    body_start = 0
    for idx, l in enumerate(lines):
        if MODULE_RE.match(l) or IMPORT_RE.match(l):
            body_start = idx + 1
        elif l.strip() == "" and idx == body_start:
            body_start = idx + 1
        else:
            break
    return body_start


def code_only(lines: list[str]) -> list[str]:
    out, in_c = [], 0
    for ln in lines:
        s = ln.strip()
        if not s:
            continue
        if in_c > 0:
            in_c += ln.count("/-") - ln.count("-/")
            continue
        if s.startswith("/-"):
            d = ln.count("/-") - ln.count("-/")
            if d > 0:
                in_c = d
            continue
        if s.startswith("--"):
            continue
        out.append(ln.split("--", 1)[0])
    return out


def parse_file(path: Path, rel: str) -> dict:
    txt = path.read_text(encoding="utf-8")
    lines = txt.splitlines()
    body_start = header_end(lines)
    has_module = any(MODULE_RE.match(l) for l in lines[:body_start])
    imps: list[str] = []
    pub_imps: set[str] = set()
    for l in lines[:body_start]:
        m = IMPORT_RE.match(l)
        if m:
            mod_name = m.group(2)
            imps.append(mod_name)
            if m.group(1) == "public":
                pub_imps.add(mod_name)

    body_lines = lines[body_start:]
    while body_lines and not body_lines[0].strip():
        body_lines.pop(0)
    while body_lines and not body_lines[-1].strip():
        body_lines.pop()

    mod_doc: list[str] = []
    if body_lines and body_lines[0].lstrip().startswith("/-!"):
        depth, j = 0, 0
        while j < len(body_lines):
            ln = body_lines[j]
            depth += ln.count("/-") - ln.count("-/")
            mod_doc.append(ln)
            j += 1
            if depth <= 0:
                break
        body_lines = body_lines[j:]
        while body_lines and not body_lines[0].strip():
            body_lines.pop(0)

    body_txt = "\n".join(body_lines)
    code = code_only(body_lines)
    code_txt = "\n".join(code)

    # Scope walk. Each code line remembers the ids of its enclosing scopes; a line "leaks" into the
    # next member only when every enclosing scope is still open at EOF (Lean drops everything a
    # closed `namespace`/`section` declared: open, variable, set_option, local attributes, include).
    stack3: list[tuple[str, str, int]] = []
    snaps: list[tuple[int, ...]] = []
    sid = 0
    for s in (c.strip() for c in code):
        snaps.append(tuple(x[2] for x in stack3))
        if s.startswith("namespace "):
            sid += 1
            stack3.append(("ns", s.split()[1], sid))
        elif s == "noncomputable section":
            sid += 1
            stack3.append(("noncomp", "", sid))
        elif re.match(r"^(?:@\[[^\]]*\]\s*)*public\s+section(?:\s|$)", s):
            sid += 1
            stack3.append(("pubsec", "", sid))
        elif s == "section" or s.startswith("section "):
            sid += 1
            stack3.append(("sec", s.split()[1] if len(s.split()) > 1 else "", sid))
        elif s == "end":
            if stack3:
                stack3.pop()
        elif s.startswith("end "):
            nm = s.split()[1]
            if stack3 and stack3[-1][0] == "ns" and _n(stack3[-1][1]).endswith("." + _n(nm)):
                k_, n_, i_ = stack3[-1]
                stack3[-1] = (k_, ".".join(n_.split(".")[: -len(nm.split("."))]), i_)  # partial close
                continue
            for k in range(len(stack3) - 1, -1, -1):
                if _n(stack3[k][1]) == _n(nm):
                    del stack3[k:]
                    break
    stack = [(k, nm) for k, nm, _ in stack3]
    eof_ids = {x[2] for x in stack3}
    leak_code = [c for c, sn in zip(code, snaps) if all(i in eof_ids for i in sn)]
    leak_txt = "\n".join(leak_code)

    active_includes: set[str] = set()
    for s in (c.strip() for c in leak_code):
        if s.startswith("include ") and not s.endswith(" in") and " in " not in s:
            active_includes.update(s.split()[1:])
        elif s.startswith("omit ") and not s.endswith(" in") and " in " not in s:
            for t in s.split()[1:]:
                active_includes.discard(t)
    code_txt_all = code_txt
    code_txt = leak_txt  # header facts below describe only what reaches the next member

    opens: set[str] = set()
    for m in re.finditer(r"^open\s+([^\n]+(?:\n  [^\n]+)*)", code_txt, re.M):
        toks = m.group(1).split()
        if not any(x in ("in", "hiding", "scoped") for x in toks) and "(" not in m.group(1):
            opens.update(toks)

    seals: set[str] = set()
    for m in re.finditer(r"^seal\s+([^\n]+)", code_txt, re.M):
        s = m.group(1).strip()
        if not s.endswith(" in"):
            seals.update(s.split())

    var_map: dict[str, set[str]] = defaultdict(set)
    for m in re.finditer(r"^variable\s+([^\n]+(?:\n  [^\n]+)*)", code_txt, re.M):
        blk = " ".join(m.group(1).split())
        if not blk.endswith(" in"):
            for b in split_var_binders(blk):
                for nm in binder_names(b):
                    var_map[nm].add(b)

    has_local_inst = bool(re.search(r"^attribute\s+\[local\s+instance", code_txt, re.M))
    has_local_irred = bool(re.search(r"^attribute\s+\[local\s+irreducible", code_txt, re.M))
    has_attr_erase = bool(ATTR_ERASE_RE.search(code_txt))
    has_setopt = bool(SET_OPT_NO_IN_RE.search(code_txt))
    has_open_special = bool(OPEN_SPECIAL_RE.search(code_txt))
    has_pub_section = bool(PUB_SECTION_RE.search(code_txt_all))

    first_ns = None
    for c in code:
        s = c.strip()
        if s.startswith("namespace "):
            first_ns = s.split()[1]
        break

    kinds = [k for k, _ in stack]
    # Allowed eof scopes: [], [ns], [noncomp], [noncomp, ns]. An `ns` opened before an unclosed
    # `noncomputable section` cannot be closed by name ahead of the next member.
    simple_eof = kinds in ([], ["ns"], ["noncomp"], ["noncomp", "ns"])
    shareable_prefix = simple_eof and not (
        has_attr_erase or has_setopt or has_open_special or bool(active_includes)
        or has_local_inst or has_local_irred or has_pub_section
    )

    return {
        "rel": rel,
        "path": path,
        "has_module": has_module,
        "imps": imps,
        "pub_imps": pub_imps,
        "mod_doc": mod_doc,
        "body_lines": body_lines,
        "eof_stack": stack,
        "eof_ns": next((nm for k, nm in reversed(stack) if k == "ns"), None),
        "first_ns": first_ns,
        "opens": opens,
        "seals": seals,
        "var_map": dict(var_map),
        "privates": set(PRIVATE_RE.findall(code_txt_all)),
        "idents": set(IDENT_RE.findall(code_txt_all)),
        "code_lines": len(code),
        "has_syntax": bool(SYNTAX_HAZARD_RE.search(code_txt_all)),
        "has_export": bool(EXPORT_RE.search(code_txt_all)),
        "has_universe": bool(UNIVERSE_RE.search(code_txt_all)),
        "has_local_simp": bool(LOCAL_SIMP_RE.search(code_txt)),
        "has_attr_erase": has_attr_erase,
        "has_pub_section": has_pub_section,
        "shareable_prefix": shareable_prefix,
        "unshareable_why": [
            w for w, f in (
                ("eof_scope", not simple_eof), ("attr_erase", has_attr_erase),
                ("set_option", has_setopt), ("open_special", has_open_special),
                ("include", bool(active_includes)), ("local_instance", has_local_inst),
                ("local_irreducible", has_local_irred), ("public_section", has_pub_section),
            ) if f
        ],
        "_body_txt_len": len(body_txt),
    }


def vars_compatible(vmap1: dict[str, set[str]], vmap2: dict[str, set[str]]) -> bool:
    return all(not (nm in vmap2 and b1 != vmap2[nm]) for nm, b1 in vmap1.items())


def seals_compatible(s1: set[str], s2: set[str]) -> bool:
    return s1.issubset(s2)


def wrap_cmd(prefix: str, items: list[str], max_len: int = 98) -> list[str]:
    if not items:
        return []
    out: list[str] = []
    cur = prefix
    for it in items:
        cand = f"{cur} {it}"
        if len(cand) <= max_len:
            cur = cand
        else:
            out.append(cur)
            cur = f"  {it}"
    out.append(cur)
    return out


def _block(body: list[str], i: int) -> int:
    j = i + 1
    while j < len(body) and body[j].startswith("  ") and body[j].strip():
        j += 1
    return j


def new_state(inherit: dict | None = None) -> dict:
    """Header-dedup state. `frames` mirrors the dedup-level scopes (noncomputable section / first
    namespace) that are open right now; every recorded open/seal/simp/binder remembers the frame it
    was declared in and is forgotten when that frame closes (Lean drops it there too). Inherited
    tokens (wrapped subgroup) have no owner: the outer scopes stay open for the whole section."""
    st = {"opens": set(), "seals": set(), "simps": set(), "binders": set(),
          "owner": {}, "frames": [], "fid": 0, "ns": None, "noncomp": False}
    if inherit:
        for cat in ("opens", "seals", "simps"):
            st[cat] = set(inherit[cat])
    return st


def _sync(st: dict) -> None:
    st["ns"] = next((n for k, n, _ in reversed(st["frames"]) if k == "ns"), None)
    st["noncomp"] = any(k == "noncomp" for k, _, _ in st["frames"])


def _push(st: dict, kind: str, name: str) -> None:
    st["frames"].append((kind, name, st["fid"]))
    st["fid"] += 1
    _sync(st)


def _pop(st: dict) -> tuple[str, str]:
    kind, name, fid = st["frames"].pop()
    for key in [k for k, v in st["owner"].items() if v == fid]:
        st[key[0]].discard(key[1])
        del st["owner"][key]
    _sync(st)
    return kind, name


def _shrink(st: dict, nm: str) -> None:
    kind, name, fid = st["frames"][-1]
    for key in [k for k, v in st["owner"].items() if v == fid]:
        st[key[0]].discard(key[1])
        del st["owner"][key]
    st["frames"][-1] = (kind, ".".join(name.split(".")[: -len(nm.split("."))]), st["fid"])
    st["fid"] += 1
    _sync(st)


def _own(st: dict, cat: str, toks: list[str]) -> None:
    fid = st["frames"][-1][2] if st["frames"] else -1
    for t in toks:
        st[cat].add(t)
        st["owner"][(cat, t)] = fid


def close_ns_lines(st: dict) -> list[str]:
    """Close frames top-down until the open namespace frame is closed (no-op when none is open)."""
    out: list[str] = []
    while st["ns"] is not None:
        kind, name = _pop(st)
        out.append(f"end {name}" if kind == "ns" else "end")
    if out:
        out.append("")
    return out


def close_all_lines(st: dict) -> list[str]:
    out: list[str] = []
    while st["frames"]:
        kind, name = _pop(st)
        out.append(f"end {name}" if kind == "ns" else "end")
    return out


def dedup_body_headers(body, st):
    """Emit one member body against the running state `st` (see new_state); mutates st."""
    out: list[str] = []
    depth = in_cmt = 0
    i, n = 0, len(body)
    first_code_seen = False
    while i < n:
        ln = body[i]
        s = ln.strip()
        if in_cmt > 0:
            in_cmt += ln.count("/-") - ln.count("-/")
            out.append(ln); i += 1
            continue
        if s.startswith("/-"):
            d = ln.count("/-") - ln.count("-/")
            if d > 0:
                in_cmt = d
            out.append(ln); i += 1
            continue
        if s.startswith("--") or not s:
            out.append(ln); i += 1
            continue

        if not first_code_seen:
            first_code_seen = True
            if st["ns"] is not None:
                top = st["frames"][-1]
                if top[0] == "ns" and s.startswith("namespace ") and _n(s.split()[1]) == _n(top[1]):
                    i += 1  # seamless namespace continuation
                    continue
                out.extend(close_ns_lines(st))

        if s == "noncomputable section" and depth == 0:
            if st["noncomp"]:
                i += 1  # already inside one; this member's closing `end` closes the shared frame
                continue
            _push(st, "noncomp", "")
            out.append(ln); i += 1
            continue
        if s.startswith("namespace "):
            if depth == 0 and st["ns"] is None:
                _push(st, "ns", s.split()[1])
            else:
                depth += len(s.split()[1].split("."))  # `namespace A.B` opens two scopes
            out.append(ln); i += 1
            continue
        if s == "section" or s.startswith("section ") or re.match(r"^(?:@\[[^\]]*\]\s*)*public\s+section(?:\s|$)", s):
            depth += 1
            out.append(ln); i += 1
            continue
        if s == "end":
            if depth > 0:
                depth -= 1
            elif st["frames"]:
                _pop(st)
            out.append(ln); i += 1
            continue
        if s.startswith("end "):
            nm = s.split()[1]
            top = st["frames"][-1] if st["frames"] else None
            if depth == 0 and top and top[0] == "ns" and _n(top[1]) == _n(nm):
                _pop(st)
            elif depth == 0 and top and top[0] == "ns" and _n(top[1]).endswith("." + _n(nm)):
                _shrink(st, nm)  # `namespace A.B` ... `end B` leaves `A` open
            else:
                depth = max(0, depth - len(nm.split(".")))
            out.append(ln); i += 1
            continue

        if depth == 0:
            if ln.startswith("open ") and not any(x in ln for x in (" in", "hiding", "scoped", "(")):
                j = _block(body, i)
                blk = body[i:j]
                if not any(any(x in b for x in (" in", "hiding", "scoped", "(")) for b in blk):
                    uniq = list(dict.fromkeys(t for t in " ".join(blk)[len("open "):].split() if t not in st["opens"]))
                    _own(st, "opens", uniq)
                    out.extend(wrap_cmd("open", uniq))
                    i = j
                    continue
            if ln.startswith("seal ") and not s.endswith(" in"):
                j = _block(body, i)
                blk = body[i:j]
                if not any(b.strip().endswith(" in") for b in blk):
                    uniq = list(dict.fromkeys(t for t in " ".join(blk)[len("seal "):].split() if t not in st["seals"]))
                    _own(st, "seals", uniq)
                    out.extend(wrap_cmd("seal", uniq))
                    i = j
                    continue
            if ln.startswith("attribute [local simp] "):
                j = _block(body, i)
                blk = body[i:j]
                uniq = list(dict.fromkeys(
                    t for t in " ".join(blk)[len("attribute [local simp] "):].split() if t not in st["simps"]))
                _own(st, "simps", uniq)
                out.extend(wrap_cmd("attribute [local simp]", uniq))
                i = j
                continue
            if ln.startswith("variable ") and not s.endswith(" in"):
                j = _block(body, i)
                blk = body[i:j]
                joined = " ".join(x.strip() for x in blk)
                if not joined.endswith(" in"):
                    binders = split_var_binders(joined[len("variable "):])
                    new_b = list(dict.fromkeys(b for b in binders if b not in st["binders"]))
                    _own(st, "binders", new_b)
                    if new_b:
                        out.extend(blk if len(new_b) == len(binders) else wrap_cmd("variable", new_b))
                    i = j
                    continue
        out.append(ln); i += 1

    cleaned: list[str] = []
    for ln in out:
        if not ln.strip() and (not cleaned or not cleaned[-1].strip()):
            continue
        cleaned.append(ln)
    while cleaned and not cleaned[-1].strip():
        cleaned.pop()
    return cleaned


# ---------------------------------------------------------------- graph
# A group is an ordered list of items. An item is a module name (str, merged unwrapped: its top-level
# scope flows into the following items) or ("wrap", [items]) - a whole folded subgroup emitted inside
# `section ... end`, so its opens / variables / set_option / local instances / universes stay local.

def flat(items) -> list[str]:
    out: list[str] = []
    for it in items:
        if isinstance(it, str):
            out.append(it)
        else:
            out.extend(flat(it[1]))
    return out


def transitive_reduction(adj: dict[str, set[str]]) -> dict[str, list[str]]:
    reach: dict[str, set[str]] = {}

    def get_r(g: str) -> set[str]:
        if g in reach:
            return reach[g]
        r: set[str] = set()
        for d in adj[g]:
            r.add(d)
            r |= get_r(d)
        reach[g] = r
        return r

    sys.setrecursionlimit(max(10000, sys.getrecursionlimit()))
    return {g: [d for d in sorted(adj[g]) if not any(d in get_r(d2) for d2 in adj[g] if d2 != d)] for g in adj}


def coalesce_plan(mods, scope="single-importer", mode="dir1", cap=1800, allow_var_shadow=False,
                  exclude_edges=None, frozen=None, wrap=True):
    exclude_edges = exclude_edges or set()
    frozen = frozen or set()
    all_mods = set(mods)
    direct = {m: {i for i in info["imps"] if i in all_mods} for m, info in mods.items()}
    reduced0 = transitive_reduction(direct)
    adj = {m: set(reduced0[m]) for m in all_mods}
    rev: dict[str, set[str]] = defaultdict(set)
    for u, vs in adj.items():
        for v in vs:
            rev[v].add(u)

    def mergeable(m):
        info = mods[m]
        return m not in PROTECTED_EXACT and m not in frozen and not (info["has_syntax"] or info["has_export"])

    members: dict[str, list] = {m: [m] for m in all_mods}
    g_code = {m: mods[m]["code_lines"] for m in all_mods}
    g_opens = {m: set(mods[m]["opens"]) for m in all_mods}
    g_seals = {m: set(mods[m]["seals"]) for m in all_mods}
    g_vmap = {m: {k: set(v) for k, v in mods[m]["var_map"].items()} for m in all_mods}
    g_priv = {m: set(mods[m]["privates"]) for m in all_mods}
    g_share = {m: mods[m]["shareable_prefix"] for m in all_mods}
    g_univ = {m: mods[m]["has_universe"] for m in all_mods}

    def same_bucket(u, v):
        if mode == "dir2":
            return u.split(".")[:2] == v.split(".")[:2]
        if mode == "dir1":
            return u.split(".")[0] == v.split(".")[0]
        return True

    def has_alt_path(start, target):
        seen, stack = set(), [x for x in adj[start] if x != target]
        while stack:
            cur = stack.pop()
            if cur == target:
                return True
            if cur in seen:
                continue
            seen.add(cur)
            stack.extend(adj[cur])
        return False

    def hard_block(u, v):
        if not mergeable(u):
            return "host_protected_or_hazard"
        if not mergeable(v):
            info = mods[v]
            if v in PROTECTED_EXACT or v in frozen:
                return "member_protected_or_frozen"
            return "member_" + ("syntax" if info["has_syntax"] else "export")
        if scope == "single-importer" and rev[v] != {u}:
            return "multi_importer"
        if not same_bucket(u, v):
            return "cross_bucket"
        if g_code[u] + g_code[v] > cap:
            return "cap"
        if (u, v) in exclude_edges:
            return "excluded"
        if g_priv[u] & g_priv[v]:
            return "private_name_collision"
        if has_alt_path(u, v):
            return "alt_path"
        return None

    def unwrap_block(u, v):
        if not g_share[v]:
            return "member_unshareable"
        if g_univ[v] and g_univ[u]:
            return "universe_both"
        if not allow_var_shadow and not vars_compatible(g_vmap[v], g_vmap[u]):
            return "variable_binder_conflict"
        if not seals_compatible(g_seals[v], g_seals[u]):
            return "seal_conflict"
        return None

    def decide(u, v):
        """-> (kind, reason) kind in {'unwrap','wrap',None}."""
        hb = hard_block(u, v)
        if hb:
            return None, hb
        ub = unwrap_block(u, v)
        if not ub:
            return "unwrap", None
        if wrap:
            return "wrap", ub
        return None, ub

    merges = 0
    kinds = defaultdict(int)
    while True:
        best = None
        for u in list(members):
            for v in list(adj[u]):
                kind, _ = decide(u, v)
                if kind is None:
                    continue
                s3 = int(u.split(".")[:3] == v.split(".")[:3])
                s2 = int(u.split(".")[:2] == v.split(".")[:2])
                last_v = flat(members[v])[-1]
                eof_ns = mods[last_v]["eof_ns"]
                first_u = members[u][0]
                same_ns = int(kind == "unwrap" and isinstance(first_u, str) and bool(eof_ns)
                              and eof_ns == mods[first_u]["first_ns"])
                ov = len(g_opens[u] & g_opens[v]) + len(set(g_vmap[u]) & set(g_vmap[v]))
                score = (int(kind == "wrap"), -same_ns, -s3, -s2, -ov, g_code[u] + g_code[v], u, v, kind)
                if best is None or score < best:
                    best = score
        if best is None:
            break
        u, v, kind = best[-3], best[-2], best[-1]
        if kind == "unwrap":
            members[u] = members[v] + members[u]
            g_opens[u] |= g_opens[v]
            g_seals[u] |= g_seals[v]
            g_share[u] = g_share[u] and g_share[v]
            g_univ[u] = g_univ[u] or g_univ[v]
        else:
            members[u] = [("wrap", members[v])] + members[u]
        # variable names: conservative union for both kinds (later unwrapped prefixes must agree)
        for k, bs in g_vmap[v].items():
            g_vmap[u].setdefault(k, set()).update(bs)
        g_code[u] += g_code[v]
        g_priv[u] |= g_priv[v]
        for dct in (members, g_code, g_opens, g_seals, g_vmap, g_priv, g_share, g_univ):
            del dct[v]
        adj[u].discard(v)
        rev[v].discard(u)
        for w in list(adj[v]):
            if w != u:
                adj[u].add(w)
                rev[w].add(u)
            rev[w].discard(v)
        for p in list(rev[v]):
            if p != u:
                adj[p].add(u)
                rev[u].add(p)
            adj[p].discard(v)
        del adj[v], rev[v]
        merges += 1
        kinds[kind] += 1

    indeg = {g: 0 for g in members}
    for vs in adj.values():
        for v in vs:
            indeg[v] += 1
    q = [g for g, d in indeg.items() if d == 0]
    vis = 0
    while q:
        cur = q.pop()
        vis += 1
        for nxt in adj[cur]:
            indeg[nxt] -= 1
            if indeg[nxt] == 0:
                q.append(nxt)
    assert vis == len(members), f"CYCLE! vis={vis} != {len(members)}"

    rev0: dict[str, set[str]] = defaultdict(set)
    for u, vs in reduced0.items():
        for v in vs:
            rev0[v].add(u)
    host_of = {m: h for h, ms in members.items() for m in flat(ms)}
    blocked: dict[str, list[str]] = defaultdict(list)
    for v, imps in rev0.items():
        if len(imps) != 1 or host_of[v] != v:
            continue
        (u,) = tuple(imps)
        hu = host_of[u]
        why = "unknown"
        if not mergeable(hu):
            why = "host_protected_or_hazard"
        elif hu in adj and v in adj[hu]:
            why = decide(hu, v)[1] or "unknown"
        blocked[why].append(v)

    return members, transitive_reduction(adj), merges, dict(kinds), reduced0, direct, dict(blocked)


# ---------------------------------------------------------------- emit

def close_scopes(stack) -> list[str]:
    out = []
    for k, nm in reversed(stack):
        out.append(f"end {nm}" if (k == "ns" or (k == "sec" and nm)) else "end")
    return out


def render_items(mods, items, st, top_level: bool) -> list[str]:
    out: list[str] = []
    for idx, it in enumerate(items):
        last = idx == len(items) - 1
        if isinstance(it, str):
            info = mods[it]
            body = (info["mod_doc"] + [""] if info["mod_doc"] else []) + list(info["body_lines"])
            if last and not top_level:
                # last module of a wrapped subgroup: emit verbatim and close exactly what it left open
                out += close_ns_lines(st)
                out += body
                out += close_scopes(info["eof_stack"])
            else:
                out += dedup_body_headers(body, st)
        else:
            out += close_ns_lines(st)
            sub = new_state(st)
            out.append("section")
            out += render_items(mods, it[1], sub, top_level=False)
            out += close_all_lines(sub)
            out.append("end")
        if not last:
            out.append("")
    cleaned: list[str] = []
    for ln in out:
        if not ln.strip() and (not cleaned or not cleaned[-1].strip()):
            continue
        cleaned.append(ln)
    return cleaned


def render_group(mods, host, ms, all_mods, reduced_adj) -> str:
    if len(ms) == 1:
        info = mods[host]
        # Preserve exact Lean 4.37 module header & public/private imports unchanged for unmerged files!
        return info["path"].read_text(encoding="utf-8")
    flat_ms = flat(ms)
    folded_set = set(flat_ms)
    has_mod = any(mods[m]["has_module"] for m in flat_ms)
    # In Lean 4.37 module mode, private imports are NOT transitive, so keep all direct non-folded
    # imports across merged members (deduplicated; `public import` dominates private `import`).
    imp_order: list[str] = []
    imp_pub: dict[str, bool] = {}
    for m in flat_ms:
        info = mods[m]
        for i in info["imps"]:
            if i in folded_set:
                continue
            is_pub = i in info["pub_imps"]
            if i not in imp_pub:
                imp_order.append(i)
                imp_pub[i] = is_pub
            elif is_pub:
                imp_pub[i] = True
    out: list[str] = []
    if has_mod:
        out.extend(["module", ""])
    for i in imp_order:
        out.append(f"public import {i}" if (has_mod and imp_pub[i]) else f"import {i}")
    out.append("")
    st = new_state()
    out += render_items(mods, ms, st, top_level=True)
    while out and not out[-1].strip():
        out.pop()
    return "\n".join(out) + "\n"


def load_mods(src_dir: Path) -> dict[str, dict]:
    mods = {}
    for p in sorted(src_dir.rglob("*.lean")):
        rel = p.relative_to(src_dir).as_posix()
        mods[rel[:-5].replace("/", ".")] = parse_file(p, rel)
    return mods


def write_tree(root: Path, dst: Path, mods, members, reduced_adj) -> None:
    all_mods = set(mods)
    for fn in os.listdir(root):
        p = root / fn
        if p.is_file():
            shutil.copy2(p, dst / fn)
    for host, ms in members.items():
        op = dst / "src" / (host.replace(".", "/") + ".lean")
        op.parent.mkdir(parents=True, exist_ok=True)
        op.write_text(render_group(mods, host, ms, all_mods, reduced_adj), encoding="utf-8")


def scan_text(txt: str, rel: str) -> dict:
    with tempfile.TemporaryDirectory(prefix="dagc_") as td:
        p = Path(td) / "x.lean"
        p.write_text(txt, encoding="utf-8")
        return gate.scan_file(p, rel)


GATE_KEYS = ("raw_lines", "code_lines", "non_ws_code", "lean_tokens", "over_100", "semi_packed", "decls")


def group_delta(mods, host, ms, all_mods, reduced_adj) -> dict:
    new = scan_text(render_group(mods, host, ms, all_mods, reduced_adj), "src/" + mods[host]["rel"])
    old = {k: 0 for k in GATE_KEYS}
    for m in flat(ms):
        st = gate.scan_file(mods[m]["path"], "src/" + mods[m]["rel"])
        for k in GATE_KEYS:
            old[k] += st[k]
    return {k: new[k] - old[k] for k in GATE_KEYS} | {"forbidden": len(new["forbidden_hits"])}


def group_ok(d: dict) -> bool:
    return (d["code_lines"] <= 0 and d["non_ws_code"] <= 0 and d["lean_tokens"] <= 0
            and d["over_100"] <= 0 and d["semi_packed"] <= 0 and d["decls"] == 0 and d["forbidden"] == 0)


def group_risks(mods, ms) -> dict:
    """Heuristic leak risks: an unwrapped item's top-level scope reaches every later item (wrapped ones too)."""
    opens_leak, var_leak, simp_leak = set(), set(), False
    acc_opens: set[str] = set()
    acc_vars: set[str] = set()
    acc_simp = False
    n_wrapped = 0
    for idx, it in enumerate(ms):
        mods_here = flat([it])
        if idx:
            for m in mods_here:
                info = mods[m]
                opens_leak |= acc_opens - info["opens"]
                var_leak |= {v for v in acc_vars if v in info["idents"] and v not in info["var_map"]}
                simp_leak |= acc_simp
        if isinstance(it, str):
            info = mods[it]
            acc_opens |= info["opens"]
            acc_vars |= {k for k in info["var_map"] if not k.startswith("[")}
            acc_simp |= info["has_local_simp"]
        else:
            n_wrapped += 1
    fm = flat(ms)
    ns_bridges = sum(1 for a, b in zip(ms, ms[1:]) if isinstance(a, str) and isinstance(b, str)
                     and mods[a]["eof_ns"] and mods[a]["eof_ns"] == mods[b]["first_ns"])
    score = len(var_leak) * 3 + len(opens_leak) + (4 if simp_leak else 0) + (len(fm) - 1)
    return {"wrapped_subgroups": n_wrapped, "open_leak": sorted(opens_leak), "variable_name_leak": sorted(var_leak),
            "local_simp_leak": simp_leak, "namespace_bridges": ns_bridges, "risk_score": score}


def structure(ms):
    return [it if isinstance(it, str) else {"wrap": structure(it[1])} for it in ms]


def git(root: Path, *a: str) -> str:
    try:
        return subprocess.run(["git", "-C", str(root), *a], capture_output=True, text=True, timeout=30).stdout.strip()
    except Exception:
        return ""


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--root", type=Path, default=HERE.parent)
    ap.add_argument("--scope", choices=["single-importer", "all"], default="single-importer")
    ap.add_argument("--mode", choices=["dir2", "dir1", "none"], default="dir1")
    ap.add_argument("--cap", type=int, default=1800, help="max code lines per merged group")
    ap.add_argument("--no-wrap", action="store_true", help="unwrapped merges only (v4 behaviour)")
    ap.add_argument("--allow-var-shadow", action="store_true")
    ap.add_argument("--exclude-json", type=Path, default=None,
                    help='JSON list of ["host","member"] edges or plain module names to keep unmerged')
    ap.add_argument("--plan-out", type=Path, default=None, help="default: <root>/specs/DAG_COALESCE_PLAN.json")
    ap.add_argument("--emit", type=Path, default=None,
                    help="write the coalesced tree here (new/empty dir outside <root>/src); default: plan only")
    ap.add_argument("--max-rounds", type=int, default=8)
    args = ap.parse_args()

    root = args.root.resolve()
    src = root / "src"
    excl_edges, frozen = set(), set()
    if args.exclude_json and args.exclude_json.exists():
        for x in json.loads(args.exclude_json.read_text(encoding="utf-8")):
            if isinstance(x, str):
                frozen.add(x)
            else:
                excl_edges.add(tuple(x))

    mods = load_mods(src)
    all_mods = set(mods)

    rejected: list[dict] = []
    for rnd in range(1, args.max_rounds + 1):
        members, reduced_adj, merges, kinds, reduced0, direct, blocked = coalesce_plan(
            mods, args.scope, args.mode, args.cap, args.allow_var_shadow, excl_edges, frozen, wrap=not args.no_wrap)
        groups = {h: ms for h, ms in members.items() if len(ms) > 1}
        deltas = {h: group_delta(mods, h, ms, all_mods, reduced_adj) for h, ms in groups.items()}
        bad = [h for h, d in deltas.items() if not group_ok(d)]
        if not bad:
            break
        for h in bad:
            rejected.append({"round": rnd, "host": h, "members": flat(groups[h]), "delta": deltas[h]})
            # keep the host's direct folded members as separate files next round; the host itself may
            # still absorb a smaller set, so freeze only the members (not the host)
            frozen.update(m for m in flat(groups[h]) if m != h)
    else:
        print("[WARN] max rounds reached with rejected groups still present", file=sys.stderr)

    base = gate.scan_tree(root)
    with tempfile.TemporaryDirectory(prefix="grh_dag_plan_") as td:
        tdp = Path(td)
        write_tree(root, tdp, mods, members, reduced_adj)
        pred = gate.scan_tree(tdp)
    bm, pm = base["metrics"], pred["metrics"]
    delta = {k: pm[k] - bm[k] for k in bm}
    gate_fail = []
    if pred["forbidden_count"] > base["forbidden_count"]:
        gate_fail.append("forbidden_tokens_increase")
    if delta["code_lines"] < 0 and (delta["non_ws_code"] > 0 or delta["lean_tokens"] > 0):
        gate_fail.append("line_packing")
    if delta["over_100"] > 0 or delta["semi_packed"] > 0:
        gate_fail.append("style_regression")

    def si_stats(graph):
        rv: dict[str, set[str]] = defaultdict(set)
        for u, vs in graph.items():
            for v in vs:
                rv[v].add(u)
        si = [m for m in all_mods if len(rv.get(m, ())) == 1]
        return {"modules": len(si), "code_lines": sum(mods[m]["code_lines"] for m in si),
                "raw_lines": sum(len(mods[m]["path"].read_text(encoding="utf-8").splitlines()) for m in si)}

    host_of = {m: h for h, ms in members.items() for m in flat(ms)}
    rv0: dict[str, set[str]] = defaultdict(set)
    for u, vs in reduced0.items():
        for v in vs:
            rv0[v].add(u)
    si_reduced = [m for m in all_mods if len(rv0.get(m, ())) == 1]
    folded = [m for m in si_reduced if host_of[m] != m]

    group_rows = []
    for h, ms in sorted(groups.items(), key=lambda kv: -len(flat(kv[1]))):
        r = group_risks(mods, ms)
        group_rows.append({"host": h, "members": flat(ms), "structure": structure(ms),
                           "member_code_lines": sum(mods[m]["code_lines"] for m in flat(ms)),
                           "delta": deltas[h], **r})
    risky = sorted(group_rows, key=lambda g: -g["risk_score"])[:15]
    import_only = sum(1 for h, ms in members.items() if len(ms) == 1
                      and set(reduced_adj[h]) != {i for i in mods[h]["imps"] if i in all_mods})

    plan = {
        "tool": f"scripts/dag_coalesce.py {VERSION}",
        "generated_at": _dt.datetime.now(_dt.timezone.utc).isoformat(timespec="seconds"),
        "dry_run": args.emit is None,
        "repo": {"branch": git(root, "rev-parse", "--abbrev-ref", "HEAD"), "head": git(root, "rev-parse", "--short", "HEAD"),
                 "src_dirty_files": len([l for l in git(root, "status", "--porcelain", "--", "src").splitlines() if l])},
        "params": {"scope": args.scope, "mode": args.mode, "cap": args.cap, "wrap_fallback": not args.no_wrap,
                   "allow_var_shadow": args.allow_var_shadow, "excluded_edges": len(excl_edges),
                   "frozen_after_reject": len(frozen)},
        "single_importer_universe": {
            "direct_imports": si_stats(direct),
            "transitively_reduced_imports": si_stats(reduced0),
            "folded_by_plan": len(folded),
            "folded_code_lines": sum(mods[m]["code_lines"] for m in folded),
            "blocked_reasons": {k: len(v) for k, v in sorted(blocked.items(), key=lambda kv: -len(kv[1]))},
            "blocked_samples": {k: sorted(v)[:8] for k, v in blocked.items()},
        },
        "prediction": {
            "files_before": bm["files"], "files_after": pm["files"], "merges": merges, "merge_kinds": kinds,
            "groups": len(groups), "files_import_reduction_only": import_only,
            "metrics_before": bm, "metrics_after": pm, "delta": delta,
            "anti_packing_gate": "PASS" if not gate_fail else "FAIL:" + ",".join(gate_fail),
        },
        "rejected_groups_anti_packing": rejected,
        "risky_groups": [{"host": g["host"], "members": len(g["members"]), "wrapped": g["wrapped_subgroups"],
                          "risk_score": g["risk_score"], "variable_name_leak": g["variable_name_leak"][:6],
                          "open_leak": g["open_leak"][:6], "local_simp_leak": g["local_simp_leak"]} for g in risky],
        "groups": group_rows,
        "next_steps": [
            "verify: python scripts/dag_coalesce.py --emit <out-of-repo dir> then "
            "python scripts/verify_dag_coalesce.py --dag-root <dir> --workers 1 (one lean worker on this PC)",
            "failing hosts/members go into --exclude-json as module names and the plan is regenerated",
            "only after per-group PASS: lake build on the emitted tree + leanchecker before touching src/",
        ],
    }
    out = args.plan_out or (root / "specs" / "DAG_COALESCE_PLAN.json")
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(plan, indent=1, ensure_ascii=False) + "\n", encoding="utf-8")

    if args.emit is not None:
        dst = args.emit.resolve()
        if dst == src or src in dst.parents or dst == root:
            print("[REFUSE] --emit must be outside the source tree", file=sys.stderr)
            return 2
        if dst.exists() and any(dst.iterdir()):
            print(f"[REFUSE] {dst} exists and is not empty (nothing is deleted)", file=sys.stderr)
            return 2
        dst.mkdir(parents=True, exist_ok=True)
        write_tree(root, dst, mods, members, reduced_adj)
        (dst / "coalesce_manifest.json").write_text(json.dumps(
            {"version": VERSION, "source_root": str(root), "source_head": plan["repo"]["head"],
             "orig_files": len(mods), "new_files": len(members), "merges": merges,
             "groups": {h: flat(ms) for h, ms in groups.items()}}, indent=1), encoding="utf-8")
        print(f"[EMIT] {dst}")

    p = plan["prediction"]
    print(f"files {p['files_before']} -> {p['files_after']} ({p['merges']} merges {kinds}, {p['groups']} groups); "
          f"raw {delta['raw_lines']:+d}, code {delta['code_lines']:+d}, non_ws {delta['non_ws_code']:+d}, "
          f"tokens {delta['lean_tokens']:+d}; gate {p['anti_packing_gate']}; rejected {len(rejected)}; plan -> {out}")
    return 0 if not gate_fail else 3


if __name__ == "__main__":
    raise SystemExit(main())
