#!/usr/bin/env python3
"""Exact packing-context parity across all supported exponent pairs."""
import hashlib,json,subprocess
from pathlib import Path
from packed_claim_handoff import packing_context

def main():
    cases=[(n,w,p) for n in range(1,26) for p in range(21) if n+p+2<=27 for w in [1,35,1<<20]]
    cases += [(0,1,0),(26,1,0),(1,0,0),(1,(1<<20)+1,0),(1,1,21),(25,1,1)]
    expected=[]
    for n,w,p in cases:
        try:ctx=packing_context(n,w,1<<p)
        except ValueError:expected.append(dict(valid=False,bytes=[]))
        else:expected.append(dict(valid=True,bytes=list(ctx)))
    out=Path('results/sha384-packing-context');out.mkdir(parents=True,exist_ok=True)
    inp=out/'inputs.json';result=out/'lean-results.json'
    # Lean's nested product JSON encoding is a nested pair.
    inp.write_text(json.dumps([[n,[w,p]] for n,w,p in cases]))
    subprocess.run(['lake','env','lean','--run','SHA384PackingContextFixture.lean',str(inp),str(result)],check=True)
    assert json.loads(result.read_text())==expected
    paths=[Path(__file__),Path('SHA384PackingContextFixture.lean'),Path(__file__).parent/'packed_claim_handoff.py',Path(__file__).parent/'pq384_primitives.py',inp,result]
    report=dict(status='PASS',accepted=sum(x['valid'] for x in expected),rejected=sum(not x['valid'] for x in expected),
      files=[dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in paths],
      scope='Every supported n/p exponent pair, three width boundaries, six invalid shapes; exact context bytes and validity.')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k!='files'}))
if __name__=='__main__':main()
