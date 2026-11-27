# Audit Record — `grh-clean-v2`

This branch (`grh-clean-v2`) is a readable, structurally flattened derivative of
[`leanprover-community/riemann-hypothesis`](https://github.com/leanprover-community/riemann-hypothesis)
at commit `2c2835a3` (Lean `v4.37.0-rc1` with `TauCeti`, derived from Luke Sernau & Anthropic's
Apache-2.0 readable `grh/` edition of Levent Alpöge's GRH proof).

## Frozen Specification Files (Bit-for-Bit Unchanged)

The following files have a 0-byte diff relative to upstream `main@2c2835a3`:

- `Challenge.lean`
- `src/Statements.lean`
- `src/Main.lean`
- `comparator.json`
- `lean-toolchain` (`leanprover/lean4:v4.37.0-rc1`)
- `lake-manifest.json`
- `lakefile.toml`

## Verified Structural Reduction (Zero Line-Packing)

All merges strictly enforce an anti-packing gate (`scripts/check_grh_clean.py`): no increase in
`>100`-char lines, no increase in semicolon-packed lines, and zero forbidden constructs (`sorry`,
custom `axiom`, `native_decide`, `unsafe`, `implemented_by`, `CSimp`, etc.). Every merged group
and every rewritten downstream caller was individually verified with `lake build`, followed by a
full end-to-end `lake build Main` and `scripts/PrintAxioms.lean` check on a 12-vCPU / 96 GiB Linux
VM.

| Metric | Upstream `main@2c2835a3` | `grh-clean-v2` | Delta |
|---|---:|---:|---:|
| `.lean` files (`src/`) | `802` | **`668`** | **`-134` (`-16.7%`)** |
| Raw lines | `479,436` | `478,677` | `-759` |
| Code lines (no comments/blanks) | `305,476` | `305,017` | `-459` |
| Non-whitespace code chars | `14,042,010` | `14,011,179` | `-30,831` |
| Lean tokens | `5,051,024` | `5,043,880` | `-7,144` |
| Lines > 100 chars | `46` | `46` | `+0` |
| Semicolon-packed lines | `11` | `11` | `+0` |
| Forbidden constructs | `0` | `0` | `0` |

### Breakdown of the `-134` Removed Files

1. **3 zero-importer orphan modules** (`-347` raw lines, verified with `lake build Main` + `PrintAxioms.lean`):
   - `src/Lib/ClassField/GreenbergWiles/RelationClasses.lean`
   - `src/Lib/ClassField/Places/AbsoluteValues.lean`
   - `src/New/Congruences/Selmer/TiedClassCounts.lean`
2. **131 same-pillar (`dir2`) single-importer module merges** (`10` in Batch 1 + `121` across `71/91` passing groups in the Spot verification sweep; full per-group log in `specs/COALESCE_VERIFY_SPOT.json`).

### Tooling Included

- `scripts/fetch-artifacts.py` & `scripts/tauceti-cache-get.py`: Windows compatibility fixes (optional Unix `resource` module, POSIX curl config paths, 200-module batching to avoid `WinError 206` and transient file locks).
- `scripts/dag_coalesce.py` (`v6`): Lean `v4.37.0-rc1` module-system-aware (`module`, `public import`, `public section`) DAG single-importer coalescer.
- `scripts/apply_verified_coalesce.py`: incremental per-group `lake build` verifier with 2-pass `public import` promotion for downstream callers and automatic rollback on failure.
- `scripts/check_grh_clean.py`: 4-metric anti-packing gate.

## Verification Receipts

- `lake build Main`: **exit code 0** (`Build completed successfully`, 0 `sorry`).
- `scripts/PrintAxioms.lean`: **exit code 0**, verbatim output:

```text
'riemannHypothesis' depends on axioms: [propext, Classical.choice, Quot.sound]
'riemannZeta_eq_zero_re' depends on axioms: [propext, Classical.choice, Quot.sound]
'LFunction_ne_zero_of_half_lt_re' depends on axioms: [propext, Classical.choice, Quot.sound]
'LFunction_eq_zero_re' depends on axioms: [propext, Classical.choice, Quot.sound]
'LFunction_eq_zero_re_of_isPrimitive' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## How to Reproduce

```sh
lake exe cache get
lake build Main
lake env lean scripts/PrintAxioms.lean
python3 scripts/check_grh_clean.py
```
