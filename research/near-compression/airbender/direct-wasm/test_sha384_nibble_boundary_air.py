"""Check private boundary conversion and independent malformed boundary rows."""
import argparse
import hashlib
import json
from pathlib import Path
import sha384_nibble_boundary_air as b
from measure_sha384_block_dag import Probe

ROOT=Path(__file__).resolve().parents[2]


def main():
    p=argparse.ArgumentParser();p.add_argument('--probe-library',required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    padded,states=Probe(a.probe_library).run(bytes(range(129)))
    records=[(states[i],padded[128*i:128*(i+1)],states[i+1]) for i in range(2)]
    air,traces,public,names=b.privatize(*b.phase.compile_air(records))
    assert not public and not air['pubSegs']
    b.l.ref.check(air,traces,public);rejected=[]
    for name,col in [('inactive-boundary',0),('boundary-id',1),('initial-state',2),('message',130),('output-state',386)]:
        old=traces[-1][0][col];traces[-1][0][col]=(old+1)%16
        try:b.l.ref.check(air,traces,public)
        except ValueError:rejected.append(name)
        else:raise AssertionError(name)
        finally:traces[-1][0][col]=old
    report=dict(status='PRIVATE_BOUNDARY_MUTATIONS_REJECTED',blocks=2,negative_cases=rejected,
        scope='Full-witness AIR parity and boundary linkage checks; no application root binding or security claim.',
        sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in [Path(__file__),Path(b.__file__),Path(b.phase.__file__)]})
    a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))


if __name__=='__main__':main()
