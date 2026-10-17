#!/usr/bin/env python3
"""Build the real-semantics bridge and inspect all theorem axiom closures."""
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parent
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
AXIOM_REPORT = re.compile(
    r"^'([^'\n]+)' (does not depend on any axioms|depends on axioms: \[([^\]]*)\])$",
    re.MULTILINE,
)


def run(*args: str) -> str:
    completed = subprocess.run(args, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                               stderr=subprocess.STDOUT, check=False)
    print(completed.stdout, end="", flush=True)
    if completed.returncode:
        raise SystemExit(completed.returncode)
    return completed.stdout


def main() -> None:
    declared = set()
    for source in (ROOT / "NearCompression").glob("*.lean"):
        text = source.read_text()
        namespaces = re.findall(r"^namespace (\S+)$", text, re.MULTILINE)
        if namespaces != ["NearCompression"]:
            raise SystemExit(f"Update theorem discovery for {source.name}")
        declared.update("NearCompression." + n for n in
                        re.findall(r"^theorem ([\w.]+)", text, re.MULTILINE))
    requested = set(re.findall(r"^#print axioms (\S+)$",
                               (ROOT / "Audit.lean").read_text(), re.MULTILINE))
    if declared != requested:
        raise SystemExit(f"Audit mismatch: missing={declared-requested}, stale={requested-declared}")
    run("lake", "build")
    output = run("lake", "env", "lean", "Audit.lean")
    checked = set()
    for m in AXIOM_REPORT.finditer(output):
        checked.add(m[1])
        axioms = {a.strip() for a in (m[3] or "").split(",") if a.strip()}
        if axioms - ALLOWED:
            raise SystemExit(f"Unexpected axioms: {m[1]}: {axioms-ALLOWED}")
    if checked != requested:
        raise SystemExit("Axiom audit output incomplete")
    run("python3", "host_inventory.py")
    run("python3", "inspect_scope.py")
    print(f"PASS: {len(checked)} actual-semantics bridge theorems and boundary regression examples.")


if __name__ == "__main__":
    main()
