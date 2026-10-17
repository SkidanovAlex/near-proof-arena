"""Check Lean-exported use rows and reject a forged sibling compression state."""
import argparse
import copy
import gzip
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile
from merkle_recursive_call_routes import check_routing

ROOT=Path(__file__).resolve().parents[2]


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--capture',type=Path,required=True)
    parser.add_argument('--fixture',type=Path,required=True);args=parser.parse_args()
    out=args.capture.resolve();fixture=args.fixture.resolve()
    example=json.loads((out/'example.json').read_text())
    rows=json.loads((fixture/'source-03-rows.json').read_text())['rows']
    assert rows==example['rows'] and check_routing(example['statement'],rows)
    config=json.loads((out/'chunk-config.json').read_text());bad=copy.deepcopy(config)
    hole=example['program']['private_pairs'][0];row=hole['row'];col=hole['column']-35
    byte=8*(col//4)+2*(3-col%4);bad['nodes'][row][8+byte]^=1
    with tempfile.TemporaryDirectory(prefix='merkle-route-negative-') as temporary:
        temp=Path(temporary);badpath=temp/'config.json';badpath.write_text(json.dumps(bad))
        r=subprocess.run(['lake','env','lean','--run','SHA384NodeChunkImportedFixture.lean',str(badpath),str(temp/'fixture')],cwd=ROOT,capture_output=True,text=True)
    assert r.returncode!=0 and 'actual node compression mismatch' in r.stdout+r.stderr
    (out/'lean-negative.log').write_text(r.stdout+r.stderr)
    (out/'spec.json.gz').write_bytes(gzip.compress((fixture/'spec.json').read_bytes(),mtime=0))
    report=dict(status='LEAN_WITNESS_AND_ROUTING_PARITY_PASS',compression_blocks=config['count'],ordered_uses=len(config['uses']),
        use_rows_match_native_witness=True,routing_on_lean_use_rows=True,
        stale_state_private_sibling_mutation_rejected_by_lean_compression=True,
        fixture_directory=str(fixture),fixture_sha256={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(fixture.glob('*.json'))},
        scope='Existing Lean exporter recomputes actual SHA384 compression and builds canonical AIR witnesses. All use rows match native states and new routing. Executable witness parity, not a formal routing-compiler theorem, PCS proof, or full recursion.')
    (out/'lean-integration.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS Lean use-row parity and forged sibling/state rejection; proof composition pending.')


if __name__=='__main__':main()
