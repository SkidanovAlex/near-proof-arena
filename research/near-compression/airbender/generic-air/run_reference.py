#!/usr/bin/env python3
"""Regenerate source fixtures with an already-built canonical Lean environment.

No build is run and no imported dependency is written. Outputs stay beside this
script. Run: python3 run_reference.py /path/to/repo/research/near-compression
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('lean_project', type=Path)
    ap.add_argument('--heavy', default='/data/illia/nearproof-deps/bin/heavy')
    args = ap.parse_args()
    here = Path(__file__).resolve().parent
    project = args.lean_project.resolve()
    repo = project.parents[1]
    env = dict(os.environ, HEAVY_MEM='8G', LEAN_NUM_THREADS='2')
    command = ['taskset','-c','8-15,24-31',args.heavy,'lake','env','lean','--run',str(here/'Fixture.lean')]
    completed = subprocess.run(command,cwd=project,env=env,text=True,capture_output=True,check=True)
    # Reject compiler diagnostics or malformed JSON before replacing the fixture.
    value = json.loads(completed.stdout)
    (here/'fixture.json').write_text(json.dumps(value,separators=(',',':'))+'\n')
    subprocess.run([sys.executable,str(here/'test_reference.py')],check=True,cwd=here)
    source_paths = ['zk-formal/ZkFormal/Air/Basic.lean','zk-formal/ZkFormal/Air/Export.lean',
                    'zk-formal/ZkFormal/V2/Air.lean','zk-formal/ZkFormal/V2/Export.lean',
                    'zk-formal/ZkFormal/Algebra/Fp.lean']
    provenance = {'lean_project':str(project),
                  'dependency_repository_commit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=repo,text=True).strip(),
                  'source_sha256':{p:hashlib.sha256((repo/p).read_bytes()).hexdigest() for p in source_paths},
                  'fixture_sha256':hashlib.sha256((here/'fixture.json').read_bytes()).hexdigest(),
                  'command':command,
                  'note':'Uses prebuilt imports. Caller must first build current canonical dependencies; no build is run here.'}
    (here/'provenance.json').write_text(json.dumps(provenance,indent=2)+'\n')


if __name__ == '__main__': main()
