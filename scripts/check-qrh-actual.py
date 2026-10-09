#!/usr/bin/env python3
"""Build selected actual QRH modules and their local dependency closure.

Uses the pinned mathlib cache read-only and the pinned, patched local dependencies.
Caches only successful builds with hashes of source and direct local dependencies.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / "lean"
STATE = LEAN / ".lake/actual-check"
BUILD = STATE / "lib/lean"
REL = LEAN / ".lake/packages/rellich-kondrachov"
PNT = LEAN / ".lake/packages/PrimeNumberTheoremAnd"
REV = "d13f23b723b8a846827a245b89c10fc7d3f11612"
REL_REV = "70f85d4c1bf99c6e7d61e8be4daa6f3664d08d23"
PNT_REV = "c39a751132c88b6e8080b74c74023fd95b3d8be0"


def digest(data):
    return hashlib.sha256(data).hexdigest()


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--mathlib-project", type=Path, required=True)
    p.add_argument("--jobs", type=int, default=3)
    p.add_argument("--lean-threads", type=int, default=1,
                   help="Threads per compiler process (default: 1, to limit memory use)")
    p.add_argument("--plan", action="store_true", help="Validate dependencies and show build counts without compiling")
    p.add_argument("--trust-declaration", action="append", default=[],
                   help="After building, check this declaration's transitive axioms")
    p.add_argument("modules", nargs="+")
    args = p.parse_args()
    if args.jobs < 1:
        p.error("--jobs must be positive")
    if args.lean_threads < 1:
        p.error("--lean-threads must be positive")
    for name in args.trust_declaration:
        if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'.]*", name):
            p.error(f"Invalid declaration name: {name}")
    packages = args.mathlib_project.resolve() / ".lake/packages"
    manifest = json.loads((LEAN / "parameter-audit/lake-manifest.json").read_text())
    toolchain = (LEAN / "lean-toolchain").read_text().strip()
    paths = [BUILD]
    for pkg in manifest["packages"]:
        checkout = packages / pkg["name"]
        rev = subprocess.check_output(["git", "-C", str(checkout), "rev-parse", "HEAD"], text=True).strip()
        if rev != pkg["rev"]:
            sys.exit(f"Revision mismatch: {pkg['name']}: {rev}")
        paths.append(checkout / ".lake/build/lib/lean")
    if not any(pkg["name"] == "mathlib" and pkg["rev"] == REV for pkg in manifest["packages"]):
        sys.exit("Unexpected mathlib lockfile revision")
    sources, deps = {}, {}

    def source_for(name):
        if name.startswith("RellichKondrachov."):
            base = REL
        elif name.startswith("PrimeNumberTheoremAnd."):
            base = PNT
        else:
            base = LEAN
        src = base / (name.replace(".", "/") + ".lean")
        return src if src.is_file() else None

    visiting = set()

    def visit(name):
        if name in visiting:
            sys.exit(f"Import cycle at {name}")
        if name in sources:
            return
        src = source_for(name)
        if src is None:
            if name.startswith(("OAI.", "QRHParameterAudit.", "RellichKondrachov.",
                                "PrimeNumberTheoremAnd.")):
                sys.exit(f"Missing local source {name}")
            return
        visiting.add(name)
        imports = []
        for line in src.read_text().splitlines():
            match = re.match(r"^(?:public )?import\s+(.+)$", line)
            if match:
                imports.extend(match[1].split("--", 1)[0].split())
        for dep in imports:
            visit(dep)
        visiting.remove(name)
        sources[name] = src
        deps[name] = [dep for dep in imports if dep in sources]

    for target in args.modules:
        if source_for(target) is None:
            sys.exit(f"Missing target {target}")
        visit(target)
    for prefix, checkout, expected, patch in [
        ("RellichKondrachov.", REL, REL_REV, "rellich-kondrachov-lean4341.patch"),
        ("PrimeNumberTheoremAnd.", PNT, PNT_REV, "PrimeNumberTheoremAnd-lean4341.patch"),
    ]:
        if any(n.startswith(prefix) for n in sources):
            rev = subprocess.check_output(
                ["git", "-C", str(checkout), "rev-parse", "HEAD"], text=True).strip()
            if rev != expected:
                sys.exit(f"Unexpected {prefix} revision {rev}")
            subprocess.run(["git", "-C", str(checkout), "apply", "--reverse", "--check",
                            str(LEAN / "patches" / patch)], check=True)
    BUILD.mkdir(parents=True, exist_ok=True)
    logs = STATE / "logs"
    logs.mkdir(parents=True, exist_ok=True)
    cache_path = STATE / "successful-builds.json"
    cache = json.loads(cache_path.read_text()) if cache_path.exists() else {}
    signatures, source_hashes = {}, {}
    config = toolchain + json.dumps(manifest, sort_keys=True) + "autoImplicit=false"
    for name, src in sources.items():
        contents = src.read_text()
        source_hashes[name] = digest(contents.encode())
        signatures[name] = digest((config + contents + "\n" +
            "\n".join(signatures[d] for d in deps[name])).encode())
    if args.plan:
        hits = sum(cache.get(n) == signatures[n] and
                   (BUILD / (n.replace(".", "/") + ".olean")).exists() for n in sources)
        print(f"Pinned dependencies validated; local closure: {len(sources)}; "
              f"verified cache hits: {hits}; modules to build: {len(sources)-hits}")
        return 0
    env = os.environ.copy()
    env["LEAN_PATH"] = os.pathsep.join(map(str, paths))
    journal = STATE / "build.log"
    with journal.open("a", buffering=1) as log:
        def record(message):
            print(message, flush=True)
            log.write(message + "\n")

        record(f"Toolchain: {toolchain}; mathlib: {REV}; local closure: {len(sources)}")
        record(f"Targets: {', '.join(args.modules)}")
        record(f"Compiler processes: {args.jobs}; threads per process: {args.lean_threads}")
        record("Scope: compile actual source modules; no new zero-free theorem claimed by this build.")

        def output_for(name):
            return BUILD / (name.replace(".", "/") + ".olean")

        def compile_one(name):
            output = output_for(name)
            output.parent.mkdir(parents=True, exist_ok=True)
            started = time.monotonic()
            if digest(sources[name].read_bytes()) != source_hashes[name]:
                return False, "Source changed after dependency planning; rerun the build.", 0
            cmd = ["elan", "run", toolchain, "lean", f"-j{args.lean_threads}", "-DautoImplicit=false",
                   "-o", str(output), str(sources[name])]
            result = subprocess.run(cmd, cwd=LEAN, env=env, text=True,
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            (logs / (name + ".log")).write_text(result.stdout)
            failed = result.returncode != 0 or "sorryAx" in result.stdout or "declaration uses 'sorry'" in result.stdout
            if digest(sources[name].read_bytes()) != source_hashes[name]:
                failed = True
                result.stdout += "\nSource changed during compilation; rerun the build.\n"
            if failed:
                output.unlink(missing_ok=True)
            return not failed, result.stdout, time.monotonic() - started

        done = {n for n in sources if cache.get(n) == signatures[n] and output_for(n).exists()}
        pending = set(sources) - done
        record(f"Verified cache hits: {len(done)}; modules to build: {len(pending)}")
        failed = []
        stopping = False

        def request_stop(signum, frame):
            nonlocal stopping
            stopping = True
            record("Stop requested; finishing and caching active compiler jobs.")

        signal.signal(signal.SIGINT, request_stop)
        with ThreadPoolExecutor(max_workers=args.jobs) as pool:
            running = {}
            while pending or running:
                if not failed and not stopping:
                    for name in sources:
                        if len(running) >= args.jobs:
                            break
                        if name in pending and all(d in done for d in deps[name]):
                            pending.remove(name)
                            running[pool.submit(compile_one, name)] = name
                            record(f"CHECK {name}")
                if not running:
                    break
                completed, _ = wait(running, return_when=FIRST_COMPLETED)
                for future in completed:
                    name = running.pop(future)
                    ok, output, elapsed = future.result()
                    if ok:
                        done.add(name)
                        cache[name] = signatures[name]
                        cache_path.write_text(json.dumps(cache, indent=2, sort_keys=True) + "\n")
                        record(f"PASS {len(done)}/{len(sources)} {name} ({elapsed:.1f}s)")
                    else:
                        failed.append(name)
                        record(f"FAIL {name} ({elapsed:.1f}s)\n{output[:16000]}")
        if failed:
            record(f"FAILED: {', '.join(failed)}; pending modules: {len(pending)}")
            return 1
        if stopping:
            record(f"Stopped with {len(done)} checked modules; rerun to resume.")
            return 130
        if pending:
            record(f"Unresolved dependency scheduling: {sorted(pending)}")
            return 1
        changed = [n for n, src in sources.items() if digest(src.read_bytes()) != source_hashes[n]]
        if changed:
            record(f"FAIL: source changed during the build: {', '.join(changed)}")
            return 1
        record("PASS: all requested modules and local dependencies compiled.")
        if args.trust_declaration:
            trust = STATE / "TargetTrust.lean"
            trust.write_text("\n".join(
                [f"import {name}" for name in args.modules] +
                [f"#print axioms {name}" for name in args.trust_declaration]) + "\n")
            result = subprocess.run(
                ["elan", "run", toolchain, "lean", f"-j{args.lean_threads}",
                 "-DautoImplicit=false", str(trust)],
                cwd=LEAN, env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            (STATE / "trust.log").write_text(result.stdout)
            record(result.stdout.rstrip())
            axiom_lists = re.findall(r"depends on axioms:\s*\[([^]]*)\]", result.stdout)
            unexpected = {a.strip() for line in axiom_lists for a in line.split(",") if a.strip()}
            unexpected -= {"propext", "Classical.choice", "Quot.sound"}
            if result.returncode or "sorryAx" in result.stdout or unexpected:
                record(f"FAIL: declaration trust check; unexpected axioms: {sorted(unexpected)}")
                return 1
            record("PASS: requested declarations use only foundational axioms.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
