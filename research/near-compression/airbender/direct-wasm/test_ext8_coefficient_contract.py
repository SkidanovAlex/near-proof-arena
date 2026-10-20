import argparse,hashlib,json,random,time
from pathlib import Path
import pq384_ext8_reference as f
import pq384_ext8_input_weights as w
from test_ext8_input_weights import coefficient_claim as reference
from ext8_coefficient_claim_contract import coefficient_claim as contracted


def main():
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True)
    p.add_argument('--source',type=Path);p.add_argument('--opening',type=Path);a=p.parse_args()
    rng=random.Random(91403)
    scalar=lambda:tuple(rng.randrange(f.P) for _ in range(8))
    checks=0
    for log in (0,1,2,3):
        for packing in (1,2,4):
            for width in (1,3,5):
                rows=[[rng.randrange(f.P) for _ in range(width)] for _ in range(1<<log)]
                point=[scalar() for _ in range(log)]
                current,nxt=[scalar() for _ in range(width)],[scalar() for _ in range(width)]
                lanes=[([current[c] if c<width else f.ZERO for c in range(j,j+packing)],
                        [nxt[c] if c<width else f.ZERO for c in range(j,j+packing)]) for j in range(0,width,packing)]
                branch=dict(log_rows=log,width=width,packing=packing,row_point=point,lanes=lanes)
                direct=f.ZERO
                for i,eq in enumerate(w.eqs(point)):
                    for j in range(width):
                        direct=f.add(direct,f.mul(eq,f.add(f.scale(current[j],rows[i][j]),f.scale(nxt[j],rows[(i+1)%len(rows)][j]))))
                assert contracted(rows,branch)==reference(rows,branch)==direct
                checks+=1
    benchmark=None
    if a.source or a.opening:
        assert a.source and a.opening
        raw=a.source.read_bytes();rows=json.loads(raw)['rows']
        branch=json.loads(a.opening.read_text())['branches'][0]
        branch={**branch,'width':branch['packing'],'lanes':branch['lanes'][:1]}
        rows=[row[:branch['packing']] for row in rows]
        start=time.perf_counter();expected=reference(rows,branch);ref_time=time.perf_counter()-start
        start=time.perf_counter();actual=contracted(rows,branch);contract_time=time.perf_counter()-start
        assert actual==expected
        benchmark=dict(rows=len(rows),width=branch['width'],reference_seconds=ref_time,contract_seconds=contract_time,
                       speedup=ref_time/contract_time,source_sha256=hashlib.sha256(raw).hexdigest(),opening_sha256=hashlib.sha256(a.opening.read_bytes()).hexdigest(),
                       scope='One actual source lane; not an end-to-end prover speedup')
    report=dict(status='PASS',three_way_small_cases=checks,benchmark=benchmark,
                scope='Reference tensor and direct cyclic-row parity. Generic contraction identity is Lean proved; Python integer/field refinement remains outside that theorem.')
    a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))

if __name__=='__main__':main()
