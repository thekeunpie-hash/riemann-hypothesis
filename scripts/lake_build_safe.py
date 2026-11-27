#!/usr/bin/env python3
"""Windows OOM-safe Lake builder for grh-clean.

Stock `lake build Main` spawns one `lean.exe` per logical CPU (up to 24 workers),
exceeding the Windows commit limit (~7.7 GB virtual memory per Lean 4.37 worker).
This driver uses `lake build --no-build <target>` to find only out-of-date modules
and compiles them strictly one at a time until `<target>` is 100% up-to-date.
"""
from __future__ import annotations

import re
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
STALE_RE = re.compile(r"Building\s+([A-Za-z0-9_.'-]+)")


def run(cmd: list[str]) -> tuple[int, str]:
    r = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True, encoding="utf-8", errors="replace")
    return r.returncode, (r.stdout + "\n" + r.stderr)


def main() -> int:
    target = sys.argv[1] if len(sys.argv) > 1 else "Main"
    t0 = time.time()
    built = 0
    seen_fail: dict[str, int] = {}

    for wave in range(1, 30):
        rc, out = run(["lake", "build", "--no-build", target])
        if rc == 0:
            print(f"[lake-safe] {target} is 100% UP-TO-DATE! (built {built} modules in {time.time()-t0:.1f}s)", flush=True)
            return 0
        # Collect unique stale project modules reported in this wave
        stale = []
        for m in STALE_RE.finditer(out):
            mod = m.group(1)
            if mod not in stale and (mod in ("Main", "Statements") or mod.startswith(("Lib.", "New."))):
                stale.append(mod)
        if not stale:
            print(f"[lake-safe] --no-build failed with no stale project modules:\n{out[-1200:]}", flush=True)
            return 1
        print(f"[lake-safe] wave {wave}: {len(stale)} stale module(s) ready -> building 1 at a time", flush=True)
        for idx, mod in enumerate(stale, 1):
            mt0 = time.time()
            rc_m, out_m = run(["lake", "build", mod])
            dt = time.time() - mt0
            if rc_m == 0:
                built += 1
                print(f"  [{idx}/{len(stale)}] OK {mod} ({dt:.1f}s)", flush=True)
            else:
                seen_fail[mod] = seen_fail.get(mod, 0) + 1
                if "failed to allocate" in out_m and seen_fail[mod] <= 2:
                    print(f"  [{idx}/{len(stale)}] OOM-retry {mod} ({dt:.1f}s)", flush=True)
                    rc_m, out_m = run(["lake", "build", mod])
                if rc_m != 0:
                    print(f"  [{idx}/{len(stale)}] FAIL {mod} ({dt:.1f}s):\n{out_m[-1200:]}", flush=True)
                    return 1
    print("[lake-safe] exceeded max waves", flush=True)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
