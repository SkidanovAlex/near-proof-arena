"""Generate full retained auxiliaries with the base evaluator and commit them.
Compare reference roots/finals when its reduction becomes available.
"""
import argparse
import gzip
import hashlib
import json
from pathlib import Path
import time
import pq384_ext8_auxiliary_base as fast
import pq384_ext8_local as local
import ext8_commitment_profiles as commitments
from pq384_primitives import Transcript
from pq384_ext8_native import Kernel
import pq384_ext8_weighted as pcs

ROOT=Path(__file__).resolve().parents[2]


def main():
    p=argparse.ArgumentParser();p.add_argument('--capture',type=Path,required=True);p.add_argument('--native-library',type=Path,required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--reference-reduction',type=Path);p.add_argument('--reuse',action='store_true');a=p.parse_args()
    sources=[Path(__file__),Path(fast.__file__)]
    if a.reuse:
        report=json.loads(a.output.read_text())
        for rel,digest in report['source_sha256'].items():assert hashlib.sha256((ROOT/rel).read_bytes()).hexdigest()==digest
        for rel,digest in report['input_sha256'].items():assert hashlib.sha256((ROOT/rel).read_bytes()).hexdigest()==digest
    else:
        statement_path=a.capture/'statement.json.gz';st=json.loads(gzip.decompress(statement_path.read_bytes()));spec=st['spec']
        seed=commitments.statement(spec,[bytes.fromhex(r) for r in st['roots']],'separate');alpha,gamma=local.draw(Transcript(seed),2)
        native=Kernel(a.native_library);results=[];paths=[statement_path]
        for i,table in enumerate(spec['air']['tables']):
            path=a.capture/f'source-{i:02d}-rows.json.gz';paths.append(path)
            rows=json.loads(gzip.decompress(path.read_bytes()))['rows'];started=time.monotonic()
            generated=fast.generate(table,rows,spec['public'],alpha,gamma);generation=time.monotonic()-started
            coordinates=[[x for value in row for x in value] for row in generated['aux_rows']]
            finals=generated['finals'];del generated,rows
            started=time.monotonic();cache=pcs.Source(coordinates,spec['aux_packings'][i],native);root=cache.root.hex();commit=time.monotonic()-started
            results.append(dict(table=i,rows=len(coordinates),root=root,finals=finals,generation_seconds=generation,commit_seconds=commit))
            del cache,coordinates
            print(json.dumps({k:v for k,v in results[-1].items() if k not in ('root','finals')}),flush=True)
        report=dict(status='FULL_AUXILIARIES_GENERATED_REFERENCE_COMPARISON_PENDING',tables=results,reference_commitments_and_finals_match=False,
            source_sha256={str(p.resolve().relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sources},
            input_sha256={str(p.resolve().relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
            native_library_sha256=hashlib.sha256(a.native_library.read_bytes()).hexdigest(),
            scope='Full retained source traces, original source-root-derived challenges, same auxiliary coordinate layout and PCS commitments. Matching commitments/finals checks compatibility, not literal full-vector equality or a Lean generator refinement. Verifier and protocol unchanged.')
    if a.reference_reduction:
        raw=a.reference_reduction.read_bytes();reduction=json.loads(gzip.decompress(raw) if a.reference_reduction.suffix=='.gz' else raw)
        assert [t['root'] for t in report['tables']]==reduction['aux_roots']
        assert json.loads(json.dumps([t['finals'] for t in report['tables']]))==reduction['finals']
        report.update(status='FULL_AUXILIARY_COMMITMENTS_AND_FINALS_MATCH',reference_commitments_and_finals_match=True,
                      reference_reduction_sha256=hashlib.sha256(raw).hexdigest())
    a.output.write_text(json.dumps(report,indent=2)+'\n');print(report['status'],flush=True)


if __name__=='__main__':main()
