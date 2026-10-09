#!/usr/bin/env python3
"""Compile the audit with a compatible, already cached mathlib project; no downloads.

Usage: python3 scripts/check-parameter-audit.py --mathlib-project /path/to/project
The supplied project must have resolved mathlib and its dependencies under .lake/packages.
This script never writes to that project. Outputs and the trust report go in this repository.
"""
import argparse
import hashlib
import json
import os
import re
from pathlib import Path
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / "lean"
REV = "d13f23b723b8a846827a245b89c10fc7d3f11612"
SOURCE_HASH = "8fe93046f8cf5ef1ba5969c89addc02d76311adc4ee907509ff9cd96f7ec99e7"
MODULES = ["Parameters", "LowArithmetic", "RowArithmetic", "HighCertificate",
           "OtherRegimes", "LateHeight", "Arithmetic", "HeightAbsorption",
           "Continuation", "AnalyticAssembly", "EulerExtension", "EulerProductExtension", "SlotExtension",
           "IdealSummability", "IdealEulerProduct", "WeightedSlotExtension",
           "LowReflectedExtension", "LowNormExtension", "HighRowAssembly", "BaselineImprovement", "PhysicalSlots",
           "CentralExponent", "ExplicitMeshArithmetic"]
SUPPORT_MODULES = ["OAI.NumberTheory.DirichletL.Detector." + name for name in [
    "Euler", "Local", "CorrectionBounds", "EulerCoordinatesScalar", "EulerRegion",
    "EulerHolomorphic", "NormalProduct"]] + [
    "OAI.NumberTheory.DirichletL.PrincipalSlotKernel",
    "OAI.NumberTheory.DirichletL.Inversion.TerminalExponent",
    "OAI.NumberTheory.DirichletL.Detector.LowReflectedExponent",
    "OAI.NumberTheory.DirichletL.Detector.LowReflectedLength",
    "OAI.NumberTheory.DirichletL.Endpoint",
    "OAI.NumberTheory.DirichletL.Parameters",
    "OAI.NumberTheory.DirichletL.ParametersSlotLengths"]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mathlib-project", type=Path, required=True)
    all_modules = SUPPORT_MODULES + [f"QRHParameterAudit.{m}" for m in MODULES] + [
        "OAI.NumberTheory.DirichletL.Improved.FloorScales",
        "OAI.NumberTheory.DirichletL.Improved.ExplicitSlots",
        "QRHParameterAudit", "QRHParameterAudit.TrustReport"]
    parser.add_argument("--module", action="append", choices=all_modules,
                        help="Check selected modules in the given dependency order; default: all")
    parser.add_argument("--log-name", default="verification.log",
                        help="Report filename inside lean/parameter-audit")
    args = parser.parse_args()
    if Path(args.log_name).name != args.log_name:
        parser.error("--log-name must be a filename, not a path")
    packages = args.mathlib_project.resolve() / ".lake/packages"
    actual_rev = subprocess.check_output(
        ["git", "-C", str(packages / "mathlib"), "rev-parse", "HEAD"], text=True).strip()
    if actual_rev != REV:
        sys.exit(f"Expected mathlib {REV}, found {actual_rev}")
    source = ROOT / "preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf"
    if hashlib.sha256(source.read_bytes()).hexdigest() != SOURCE_HASH:
        sys.exit("Source manuscript fingerprint differs from the audited copy")
    toolchain = (LEAN / "lean-toolchain").read_text().strip()
    build = LEAN / ".lake/parameter-audit/lib/lean"
    build.mkdir(parents=True, exist_ok=True)
    manifest = json.loads((LEAN / "parameter-audit/lake-manifest.json").read_text())
    paths = [build]
    for package in manifest["packages"]:
        checkout = packages / package["name"]
        package_rev = subprocess.check_output(
            ["git", "-C", str(checkout), "rev-parse", "HEAD"], text=True).strip()
        if package_rev != package["rev"]:
            sys.exit(f"Lockfile mismatch for {package['name']}: {package_rev}")
        path = checkout / ".lake/build/lib/lean"
        if path.is_dir():
            paths.append(path)
    env = os.environ.copy()
    env["LEAN_PATH"] = os.pathsep.join(map(str, paths))
    report = LEAN / "parameter-audit" / args.log_name
    with report.open("w") as log:
        def record(s):
            print(s, flush=True)
            log.write(s + "\n")
            log.flush()
        record(f"Lean toolchain: {toolchain}")
        record(f"mathlib commit: {actual_rev}")
        record(f"Source manuscript SHA-256: {SOURCE_HASH}")
        audit = ROOT / "preprints/quasi_riemann_parameter_audit.pdf"
        record(f"Parameter audit SHA-256: {hashlib.sha256(audit.read_bytes()).hexdigest()}")
        record(f"All {len(manifest['packages'])} cached package revisions match the lockfile.")
        record("Scope: unconditional parameter arithmetic and partial analytic generalizations (continuation, height absorption, Euler products and slots).")
        record("No improved L-function nonvanishing theorem is asserted by this check.")
        selected = args.module or all_modules
        record(f"Compilation selection ({len(selected)} modules): {', '.join(selected)}")
        for module in selected:
            source_file = LEAN / (module.replace(".", "/") + ".lean")
            output = build / (module.replace(".", "/") + ".olean")
            output.parent.mkdir(parents=True, exist_ok=True)
            record(f"CHECK {module}")
            start = time.monotonic()
            result = subprocess.run(
                ["elan", "run", toolchain, "lean", "-j1", "-DautoImplicit=false",
                 "-o", str(output), str(source_file)],
                cwd=LEAN, env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            if result.stdout:
                record(result.stdout.rstrip())
            unexpected_axioms = set()
            for axiom_list in re.findall(r"depends on axioms:\s*\[([^]]*)\]", result.stdout):
                unexpected_axioms.update(
                    name.strip() for name in axiom_list.split(",") if name.strip())
            unexpected_axioms -= {"propext", "Classical.choice", "Quot.sound"}
            if unexpected_axioms:
                record(f"Unexpected axioms: {sorted(unexpected_axioms)}")
            if (result.returncode or "sorryAx" in result.stdout or
                    "declaration uses 'sorry'" in result.stdout or unexpected_axioms):
                record(f"FAIL {module} (exit {result.returncode})")
                return result.returncode or 1
            record(f"PASS {module} ({time.monotonic()-start:.1f}s)")
        record("PASS: every selected module compiled; only foundational axioms in the requested axiom report.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
