#!/usr/bin/env python3
"""Run one bounded compression experiment and retain machine-readable evidence."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=["native", "execute", "reject", "succinct", "verify"])
    parser.add_argument("fixture", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--binary", type=Path, default=Path("target/recursion-compress/release/compression-host"))
    parser.add_argument("--receipt", type=Path)
    parser.add_argument("--timeout", type=int, default=600)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    names = ["air.json", "pub.bin", "claim.bin", "proof.bin"]
    inputs = [args.fixture / name for name in names]
    receipt = args.receipt or args.output / "receipt.bin"
    manifest = {}
    for path in inputs[:3] if args.action == "verify" else inputs:
        data = path.read_bytes()
        manifest[path.name] = {"path": str(path.resolve()), "bytes": len(data),
                               "sha256": hashlib.sha256(data).hexdigest()}
    cmd = ["taskset", "-c", "8-15,24-31", "/data/illia/nearproof-deps/bin/heavy",
           "/usr/bin/time", "-v", "timeout", "--kill-after=10s", str(args.timeout),
           str(args.binary.resolve()), args.action, *map(str, inputs), str(receipt)]
    env = dict(os.environ, HEAVY_MEM="16G", RAYON_NUM_THREADS="8", RISC0_DEV_MODE="0")
    with (args.output / "stdout.log").open("w") as stdout, (args.output / "stderr.log").open("w") as stderr:
        proc = subprocess.run(cmd, stdout=stdout, stderr=stderr, env=env, check=False)
    stderr_text = (args.output / "stderr.log").read_text()
    status = "PASS" if proc.returncode == 0 else "FAILED"
    if "Session limit exceeded" in stderr_text:
        status = "CYCLE_LIMIT"
    elif proc.returncode == 124:
        status = "TIME_LIMIT"
    record = {"command": cmd, "inputs": manifest, "exit_code": proc.returncode,
              "binary_sha256": hashlib.sha256(args.binary.read_bytes()).hexdigest(),
              "status": status,
              "cycle_limit": int(env.get("COMPRESSION_MAX_CYCLES", 256 * 1024 * 1024))}
    if proc.returncode == 0:
        lines = (args.output / "stdout.log").read_text().splitlines()
        record["result"] = json.loads(lines[-1])
    for line in stderr_text.splitlines():
        if "Maximum resident set size (kbytes):" in line:
            record["peak_rss_kib"] = int(line.rsplit(":", 1)[1])
    (args.output / "report.json").write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps(record, indent=2))
    raise SystemExit(proc.returncode)


if __name__ == "__main__":
    main()
