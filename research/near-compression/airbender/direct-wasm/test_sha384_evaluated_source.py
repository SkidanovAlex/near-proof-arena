#!/usr/bin/env python3
"""Parity of a proved-equal evaluation form of the mutable source model."""
import argparse, hashlib, json, subprocess, sys
from pathlib import Path


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--output-directory',type=Path,required=True)
    a=ap.parse_args()
    from packed_disclosure import prove_disclosure
    from packed_claim_handoff import packing_context
    from pq384_primitives import P,field_words,merkle_tree
    from pq384_batched_fold import source_tree,base
    from test_pq384_packing import pair
    cases=[];expected=[]
    for n,p,width in [(1,0,3),(1,1,3),(2,2,7),(3,1,5)]:
        rows=[[(P-1 if (r+c)%4==0 else (r+1)*31+c*17)%P for c in range(width)] for r in range(1<<n)]
        packing=1<<p;degree=(1<<n)*packing
        omega=pow(440564289,(1<<27)//(4*degree),P)
        ctx=packing_context(n,width,packing)
        coefficients=prove_disclosure(rows,packing)['coefficients']
        root,_,leaves=source_tree([[base(v) for v in lane] for lane in coefficients],ctx)
        # Independent nested interpolation, without the packed Mobius/FFT loop.
        values=[pair(rows,packing,omega,i) for i in range(2*degree)]
        assert [field_words(v) for v in values]==leaves
        assert merkle_tree([field_words(v) for v in values],ctx)[0]==root
        cases.append(dict(n=n,p=p,width=width,rows=rows,omega=omega,context=list(ctx)))
        expected.append(dict(source=values,coefficients=coefficients,root=list(root)))
    out=a.output_directory;out.mkdir(parents=True,exist_ok=True)
    inp=out/'inputs.json';result=out/'lean-results.json'
    inp.write_text(json.dumps(cases))
    subprocess.run(['lake','env','lean','--run','SHA384EvaluatedSourceFixture.lean',str(inp),str(result)],check=True)
    assert json.loads(result.read_text())==expected
    paths=[Path('SHA384EvaluatedSourceFixture.lean'),Path(__file__),Path('NearCompression/SHA384ComputedSource.lean'),Path('NearCompression/SHA384EvaluatedSource.lean'),Path('NearCompression/PackedSourceExecution.lean'),inp,result]
    paths += [Path(__file__).parent/x for x in ['packed_disclosure.py','packed_claim_handoff.py','pq384_primitives.py','pq384_batched_fold.py','test_pq384_packing.py','test_pq384_rs.py']]
    report=dict(status='PASS',cases=len(cases),source_leaves=sum(len(x['source']) for x in expected),partial_final_lanes=3,
      files=[dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in paths],
      limits=['Small deterministic fixtures, not native machine refinement or an adversarial-root extraction proof.','No secure parameter or proof-size certification.'])
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k not in ('files','limits')}))

if __name__=='__main__':main()
