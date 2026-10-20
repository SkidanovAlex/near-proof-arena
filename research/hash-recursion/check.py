#!/usr/bin/env python3
"""Build, check examples, and enforce the public-theorem axiom audit."""
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parent
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def run(*args: str) -> str:
    result = subprocess.run(args, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, check=False)
    print(result.stdout, end="", flush=True)
    if result.returncode:
        raise SystemExit(result.returncode)
    return result.stdout


def main() -> None:
    # This package deliberately uses one explicit namespace per module. Fail
    # closed if that convention changes; do not silently skip new theorems.
    declared = set()
    for source in sorted((ROOT / "HashRecursion").glob("*.lean")):
        contents = source.read_text()
        namespaces = re.findall(r"^namespace (\S+)$", contents, re.MULTILINE)
        if len(namespaces) != 1:
            raise SystemExit(f"Update audit discovery for {source.name}: namespace layout changed")
        for name in re.findall(r"^theorem ([\w.]+)", contents, re.MULTILINE):
            declared.add(f"{namespaces[0]}.{name}")
    requested = set(re.findall(r"^#print axioms (\S+)$",
                               (ROOT / "Audit.lean").read_text(), re.MULTILINE))
    if declared != requested:
        raise SystemExit(f"Audit coverage mismatch: missing={declared-requested}, stale={requested-declared}")

    run("lake", "build")
    output = run("lake", "env", "lean", "Audit.lean")
    checked = set()
    for line in output.splitlines():
        match = re.fullmatch(r"'([^']+)' (does not depend on any axioms|depends on axioms: \[(.*)\])", line)
        if match:
            checked.add(match[1])
            axioms = {x.strip() for x in (match[3] or "").split(",") if x.strip()}
            if axioms - ALLOWED_AXIOMS:
                raise SystemExit(f"Unexpected axiom dependencies: {match[1]}: {axioms-ALLOWED_AXIOMS}")
    if checked != requested:
        raise SystemExit("Axiom report incomplete or output format changed")
    run("lake", "env", "lean", "OracleChecks.lean")
    print(f"PASS: {len(checked)} public theorem axiom closures; budget and coherent-oracle examples.")


if __name__ == "__main__":
    main()
