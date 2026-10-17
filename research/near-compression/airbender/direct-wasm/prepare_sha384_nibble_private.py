"""Privatize and independently validate a prepared compression witness."""
import argparse
import gzip
import hashlib
import json
from pathlib import Path
import time
import sha384_nibble_boundary_air as boundary
from run_sha384_nibble_proof import canonical
from run_pq384_gkr_bus import choose_packing
from pq384_ext8_native import Kernel
import pq384_ext8_weighted as pcs
import pq384_ext8_auxiliary as aux


def main():
    p=argparse.ArgumentParser();p.add_argument('--prepared',type=Path,required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--native-library',required=True);a=p.parse_args()
    src=a.prepared.resolve();out=a.output.resolve();out.mkdir(parents=True,exist_ok=True);(out/'source').mkdir(exist_ok=True)
    old=json.loads((src/'preparation.json').read_text());assert old['full_witness_verified']
    for rel,digest in old['files'].items():assert hashlib.sha256((src/rel).read_bytes()).hexdigest()==digest
    statement=json.loads((src/'statement.json').read_text());spec=statement['spec']
    rows=[json.loads((src/'source'/f'source-{i:02d}-rows.json').read_text())['rows'] for i in range(len(spec['air']['tables']))]
    air,rows,public,names=boundary.privatize(spec['air'],rows,spec['public'],old['table_names'])
    print('Checking complete private-boundary AIR',flush=True);started=time.monotonic()
    checked=boundary.l.ref.check(air,rows,public);constraints=sum(len(r) for t in checked['residuals'] for r in t);del checked
    seconds=time.monotonic()-started
    table=air['tables'][-1];n=len(rows[-1]).bit_length()-1
    spec.update(air=air,public=public)
    spec['log_rows'].append(n);spec['source_packings'].append(choose_packing(n,table['width']));spec['aux_packings'].append(choose_packing(n,8*aux.layout(table)['aux_columns']))
    root=pcs.Source(rows[-1],spec['source_packings'][-1],Kernel(a.native_library)).root.hex()
    statement['roots'].append(root);files={}
    for i,rs in enumerate(rows):
        path=out/'source'/f'source-{i:02d}-rows.json';raw=canonical(dict(rows=rs));path.write_bytes(raw);files[str(path.relative_to(out))]=hashlib.sha256(raw).hexdigest()
    raw=canonical(statement);(out/'statement.json').write_bytes(raw);files['statement.json']=hashlib.sha256(raw).hexdigest()
    (out/'statement.json.gz').write_bytes(gzip.compress(raw,mtime=0))
    report=dict(status='PRIVATE_BOUNDARY_FULL_WITNESS_CHECKED',blocks=old['blocks'],full_witness_verified=True,
        source_constraints_evaluated=constraints,canonical_check_seconds=seconds,table_names=names,
        boundary_source_index=len(rows)-1,boundary_root=root,public_field_elements=0,
        source_aux_cells=sum(len(rs)*(t['width']+8*aux.layout(t)['aux_columns']) for rs,t in zip(rows,air['tables'])),
        files=files,source_sha256={str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in [Path(__file__),Path(boundary.__file__)]},
        prior_public_preparation_sha256=hashlib.sha256((src/'preparation.json').read_bytes()).hexdigest(),
        scope='Full compression AIR with proof-committed private state/message/result table. Empty public vector does not bind any application hash claim: boundary root still needs same-root recursive call routing. No zero-knowledge, succinct proof, formal compiler, or PQ128 claim.')
    (out/'preparation.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items() if k not in ('files','source_sha256')},indent=2))


if __name__=='__main__':main()
