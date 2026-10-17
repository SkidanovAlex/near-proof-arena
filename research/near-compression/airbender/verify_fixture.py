#!/usr/bin/env python3
"""Reproduce acceptance/rejection of pinned Airbender EVM fixtures, not proving."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess

PIN = "129f827003b34acd64a3315a5863eac75bc09fe6"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("repo", type=Path)
    parser.add_argument("--forge", required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    repo = args.repo.resolve()
    sha = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=repo, text=True).strip()
    if sha != PIN:
        raise SystemExit(f"Expected {PIN}; found {sha}")
    subprocess.run(["git", "diff", "--exit-code", "HEAD", "--", "verifier_evm"], cwd=repo, check=True)
    base = repo / "verifier_evm/generated_contracts"
    source = Path(__file__).with_name("NearProofFixtureMutation.t.sol")
    dest = base / "two_tx/test/NearProofFixtureMutation.t.sol"
    if dest.exists() and dest.read_bytes() != source.read_bytes():
        raise SystemExit(f"Refusing to overwrite different test: {dest}")
    dest.write_bytes(source.read_bytes())
    args.output.parent.mkdir(parents=True, exist_ok=True)
    runs = []
    for project, command in [("gkr", ["build"]), ("whir", ["build"]),
                             ("two_tx", ["test", "-vv"])]:
        log = args.output.with_suffix(f".{project}.log").resolve()
        with log.open("w") as stream:
            result = subprocess.run([args.forge, *command], cwd=base / project,
                                    stdout=stream, stderr=subprocess.STDOUT)
        runs.append({"project": project, "command": command,
                     "returncode": result.returncode, "log": str(log)})
        if result.returncode:
            raise SystemExit(f"Failed {project}; see {log}")
    paths = ["verifier_evm/debug_data/gkr_full_calldata.hex",
             "verifier_evm/debug_data/proth120_whir_calldata_from_proof.hex",
             "verifier_evm/generated_contracts/gkr/src/GkrVerifier.sol",
             "verifier_evm/generated_contracts/whir/src/WhirVerifier.sol",
             "verifier_evm/generated_contracts/two_tx/src/GkrWhirRegistry.sol"]
    sizes = {p: len(bytes.fromhex((repo / p).read_text().strip()))
             for p in paths[:2]}
    report = {"commit": sha, "runs": runs,
              "forge_version": subprocess.check_output([args.forge, "--version"], text=True).strip(),
              "fixture_bytes": sizes, "combined_fixture_bytes": sum(sizes.values()),
              "sha256": {p: hashlib.sha256((repo / p).read_bytes()).hexdigest() for p in paths},
              "mutation_test_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
              "scope": "Compiled checked-in Solidity; ran upstream fixture and registry tests plus ten targeted mutation tests.",
              "limitations": ["No Rust verifier regeneration or new proof generation.",
                              "No NEAR execution or 1 Pgas benchmark.",
                              "Not a cryptographic soundness proof or quantum-security certification."]}
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"result": "PASS", "bytes": sum(sizes.values()), "report": str(args.output)}))


if __name__ == "__main__":
    main()
