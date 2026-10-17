#!/usr/bin/env python3
"""Regenerate Lean source residuals and run bus auxiliary differential checks.

Uses prebuilt canonical dependencies, writes only beside this script, no build.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('lean_project',type=Path)
    ap.add_argument('--heavy',default='/data/illia/nearproof-deps/bin/heavy')
    ap.add_argument('--direct-wasm',type=Path)
    args=ap.parse_args()
    here=Path(__file__).resolve().parent
    project=args.lean_project.resolve()
    command=['taskset','-c','8-15,24-31',args.heavy,'lake','env','lean','--run',str(here/'BusAuxFixture.lean')]
    result=subprocess.run(command,cwd=project,env=dict(os.environ,HEAVY_MEM='8G',LEAN_NUM_THREADS='2'),
                          text=True,capture_output=True)
    if result.returncode:
        raise SystemExit(result.stdout+result.stderr)
    value=json.loads(result.stdout)
    (here/'bus-aux-fixture.json').write_text(json.dumps(value,separators=(',',':'))+'\n')
    test=[sys.executable,str(here/'test_bus_auxiliary.py')]
    if args.direct_wasm:test+=['--direct-wasm',str(args.direct_wasm.resolve())]
    subprocess.run(test,cwd=here,check=True)
    source=project.parents[1]/'zk-formal/ZkFormal/Stark/VerifierDefs.lean'
    provenance={'source':str(source),'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
                'fixture_sha256':hashlib.sha256((here/'bus-aux-fixture.json').read_bytes()).hexdigest(),
                'command':command,'note':'Canonical imports must already be built; no shared build performed.'}
    (here/'bus-aux-provenance.json').write_text(json.dumps(provenance,indent=2)+'\n')


if __name__=='__main__':main()
