#!/usr/bin/env python3
"""Download every artifact named in a Lake map that is missing from a local Lake cache.

Copied from scripts/rh-buildq/fetch-artifacts.py of leanprover-community/riemann-hypothesis
(main); only the default URL differs.

usage: fetch-artifacts.py <map.jsonl> <cache-dir> [--sha256 <file> [--verify-existing]]
                          [--base-url <url>] [--user-agent <agent>] [--report <file>]
Stock Lake 4.37 does not download artifacts lazily during `lake build`: a mapped module whose
artifact is absent locally is simply compiled. So restores must prefetch. One curl process
downloads up to 500 files at a time (fd soft limit raised to match) and retries transport
errors and CDN 5xx. Files land in <cache-dir>/artifacts/<hash16>.ltar atomically, so a file
there is always complete. Objects are content-addressed and write-once (If-None-Match) in R2.
--sha256 names a JSON object {"<hash16>.ltar": "<sha256>"} (e.g. from a CI module manifest):
those downloads are verified before they are moved into the cache, and a mismatch is discarded
and downloaded again. With --verify-existing, artifacts already in the cache are checked too
(a symlink or mismatch is removed and downloaded again). Up to three passes; exit 1 if anything
is still missing. curl's error lines (one per failed attempt, retries included) are grouped by
error code and printed once per pass. --report writes the last pass's curl exit code, those
groups and its SHA-256 failure count as JSON. scripts/ci-cache-get.py (`lake exe cache get`)
uses this with its own --user-agent and puts the report in its final error.
"""
import hashlib, json, os, re, subprocess, sys, tempfile
try:
    import resource
except ImportError:
    resource = None
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

PUBLIC = "https://rh-cache.taucetiproject.org/artifacts/leanprover-community/riemann-hypothesis-grh-lean/grh/"
PARALLEL = 500
CURL_ERROR = re.compile(r"curl: \((\d+)\)")


def curl_errors(stderr):
    """[[count, first line], ...] for curl's error output, most frequent first.

    Lines with an error code also name a file or byte counts, so they are grouped by the code;
    other lines (an unknown option, for example) are grouped as they are."""
    groups = {}
    for line in stderr.splitlines():
        line = line.strip()
        if not line or line.startswith("curl: try "):
            continue
        match = CURL_ERROR.match(line)
        key = match.group(1) if match else line
        groups.setdefault(key, [0, line[:300]])[0] += 1
    return sorted(groups.values(), key=lambda group: -group[0])


def sha256(path):
    with open(path, "rb") as f:
        return hashlib.file_digest(f, "sha256").hexdigest()


def option(args, name, default=None):
    if name not in args:
        return default
    i = args.index(name)
    value = args[i + 1]
    del args[i:i + 2]
    return value


def main():
    args = sys.argv[1:]
    digests = option(args, "--sha256")
    digests = json.loads(Path(digests).read_text()) if digests else {}
    base = option(args, "--base-url", PUBLIC)
    agent = option(args, "--user-agent", "rh-buildq/1")
    report = option(args, "--report")
    verify_existing = "--verify-existing" in args
    if verify_existing:
        args.remove("--verify-existing")
    mapping, cache = Path(args[0]), Path(args[1]) / "artifacts"
    cache.mkdir(parents=True, exist_ok=True)
    if resource is not None:
        soft, hard = resource.getrlimit(resource.RLIMIT_NOFILE)
        want = 65536 if hard == resource.RLIM_INFINITY else min(hard, 65536)
        if soft != resource.RLIM_INFINITY and soft < want:
            resource.setrlimit(resource.RLIMIT_NOFILE, (want, hard))
    lines = mapping.read_text().splitlines()[1:]
    names = sorted({json.loads(l)[1] for l in lines if l})

    def present(n):
        p = cache / n
        if not verify_existing:
            return p.exists()
        if p.is_symlink() or (p.exists() and n in digests and sha256(p) != digests[n]):
            print(f"fetch-artifacts: discarding corrupt local {n}", flush=True)
            p.unlink()
            return False
        return p.is_file()

    with ThreadPoolExecutor(32) as pool:
        missing = [n for n, ok in zip(names, pool.map(present, names)) if not ok]
    print(f"fetch-artifacts: {len(names)} mapped, {len(missing)} missing locally", flush=True)
    code, errors, corrupt = 0, [], []
    for attempt in range(1, 4):
        if not missing:
            break
        with tempfile.TemporaryDirectory(prefix="fetch-", dir=cache.parent) as t:
            conf = Path(t) / "curl.conf"
            t_posix = Path(t).as_posix()
            conf.write_text("".join(f'url = "{base}{n[:-5]}.art"\noutput = "{t_posix}/{n}"\n' for n in missing))
            r = subprocess.run(["curl", "--disable", "--fail", "--silent", "--show-error", "--location",
                                "--user-agent", agent, "--retry", "5", "--retry-all-errors",
                                "--connect-timeout", "30", "--max-time", "600",
                                "--parallel", "--parallel-max", str(PARALLEL), "--config", str(conf)],
                               stderr=subprocess.PIPE, text=True, errors="replace")
            code, errors = r.returncode, curl_errors(r.stderr)

            def settle(n):
                p = Path(t) / n
                if not (p.is_file() and p.stat().st_size):
                    return "missing"
                if n in digests and sha256(p) != digests[n]:
                    p.unlink()
                    return "corrupt"
                if os.name != "nt":
                    os.chmod(p, 0o444)
                os.replace(p, cache / n)
                return "ok"

            with ThreadPoolExecutor(32) as pool:
                results = list(pool.map(settle, missing))
        corrupt = [n for n, s in zip(missing, results) if s == "corrupt"]
        missing = [n for n, s in zip(missing, results) if s != "ok"]
        print(f"fetch-artifacts: pass {attempt}: downloaded {len(results) - len(missing)}/{len(results)}"
              f" (curl exit {code}; {len(corrupt)} failed SHA-256 verification)", flush=True)
        for count, line in errors[:5]:
            print(f"fetch-artifacts: {line}" + (f" (reported {count} times)" if count > 1 else ""), flush=True)
        for n in corrupt[:10]:
            print(f"fetch-artifacts: SHA-256 mismatch for {n}", flush=True)
    if report:
        Path(report).write_text(json.dumps({"curl_exit": code, "curl_errors": errors,
                                            "sha256_mismatches": len(corrupt)}))
    sys.exit(1 if missing else 0)


if __name__ == "__main__":
    main()
