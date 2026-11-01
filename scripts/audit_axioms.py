#!/usr/bin/env python3
"""Audit the exact axioms of the three headline theorems and their wrappers."""
from __future__ import annotations

import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent.parent
NAMES = (
    "FractionalPrimes.Final.primePowerVariation",
    "FractionalPrimes.Final.primeAverageConvergenceWithEnumeration",
    "FractionalPrimes.Final.mobiusLogRate",
    "FractionalPrimes.Final.Palomar.primePowerVariation",
    "FractionalPrimes.Final.Palomar.primeAverageConvergence",
    "FractionalPrimes.Final.Palomar.mobiusAverageTendsToZero",
)
EXPECTED = {"propext", "Classical.choice", "Quot.sound"}


def fail(message: str) -> None:
    print(f"FAIL: {message}", file=sys.stderr)
    raise SystemExit(1)


def run(command: list[str], timeout: int) -> str:
    try:
        result = subprocess.run(command, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, timeout=timeout, check=False)
    except (OSError, subprocess.TimeoutExpired) as error:
        fail(f"{command!r} failed to complete: {error}")
    if result.returncode or re.search(r"(?m)^.*\berror:", result.stdout):
        fail(f"{command!r} failed (exit {result.returncode}):\n{result.stdout}")
    return result.stdout


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def source_snapshot() -> dict[str, str]:
    source_files = sorted(path for path in ROOT.rglob("*.lean")
                          if ".lake" not in path.relative_to(ROOT).parts
                          and ".git" not in path.relative_to(ROOT).parts)
    config_files = [ROOT / name for name in ("lean-toolchain", "lakefile.lean", "lake-manifest.json")]
    return {str(path.relative_to(ROOT)): digest(path) for path in [*source_files, *config_files]}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--already-built", action="store_true",
                        help="skip build; requires a completed build of the same unchanged sources")
    args = parser.parse_args()
    before = source_snapshot()
    build_output = None if args.already_built else run(["lake", "build", "Solution"], 1800)
    module_path = ROOT / ".lake/build/lib/lean/Solution.olean"
    if not module_path.is_file():
        fail(f"required file missing: {module_path}")
    module_hash = digest(module_path)
    probe = "import Solution\n\n" + "\n".join(f"#print axioms {name}" for name in NAMES) + "\n"
    with tempfile.TemporaryDirectory(prefix="headline-axioms-") as directory:
        path = Path(directory) / "HeadlineAxioms.lean"
        path.write_text(probe, encoding="utf-8")
        output = run(["lake", "env", "lean", str(path)], 600)
    if digest(module_path) != module_hash:
        fail("Solution.olean changed during the axiom probe")
    if source_snapshot() != before:
        fail("Lean sources or project configuration changed during the audit")
    names = re.findall(r"(?m)^'([^']+)' depends on axioms:", output)
    if Counter(names) != Counter(NAMES):
        fail(f"expected exactly the six headline results; observed {names}\n{output}")
    results = {}
    for name in NAMES:
        matches = re.findall(re.escape(f"'{name}' depends on axioms:") + r"\s*\[([^\]]*)\]", output, re.DOTALL)
        if len(matches) != 1:
            fail(f"expected one axiom list for {name}; found {len(matches)}\n{output}")
        axioms = [item.strip() for item in matches[0].split(",") if item.strip()]
        if len(axioms) != len(EXPECTED) or set(axioms) != EXPECTED:
            fail(f"unexpected axioms for {name}: {axioms}")
        results[name] = sorted(axioms)
    artifact = {
        "timestamp_utc": datetime.now(timezone.utc).isoformat(),
        "build_skipped": args.already_built,
        "build_output": build_output,
        "probe_source": probe,
        "lean_output": output,
        "axioms": results,
        "sha256": {**before, str(module_path.relative_to(ROOT)): module_hash},
        "limitations": "Stable snapshots do not establish freshness of transitive compiled dependencies; --already-built requires a completed build of the same unchanged sources.",
    }
    destination = ROOT / "audits/headline_axioms.json"
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(json.dumps(artifact, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(f"PASS: all six declarations have exactly the expected axioms; wrote {destination}")


if __name__ == "__main__":
    main()
