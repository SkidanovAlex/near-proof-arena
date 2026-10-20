"""Independent coefficient conversion checks for Ext8 input opening weights."""
import argparse, json, random
from pathlib import Path
import pq384_ext8_reference as f
import pq384_ext8_input_weights as w

def coefficients(rows,start,packing):
    # In-place Boolean Mobius inversion, row bits below column bits.
    width=len(rows[0]);v=[row[c] if c<width else 0 for c in range(start,start+packing) for row in rows]
    bit=1
    while bit<len(v):
        for i in range(len(v)):
            if i&bit:v[i]=(v[i]-v[i^bit])%f.P
        bit*=2
    return v

def coefficient_claim(rows,branch):
    assert len(rows)==1<<branch['log_rows'] and all(len(r)==branch['width'] for r in rows)
    value=f.ZERO
    for j,(a,b) in enumerate(branch['lanes']):
        cs=coefficients(rows,j*branch['packing'],branch['packing'])
        weights=w.lane_weights(branch['row_point'],a,b)
        assert len(cs)==len(weights)
        for c,weight in zip(cs,weights):value=f.add(value,f.scale(weight,c))
    return value

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);args=ap.parse_args();rng=random.Random(82071)
    def scalar():return tuple(rng.randrange(f.P) for _ in range(8))
    checks=0;mles=0
    for n in (1,2,4):
        for packing in (1,2,4):
            for width in (1,3,5):
                rows=[[rng.randrange(f.P) for _ in range(width)] for _ in range(1<<n)]
                point=[scalar() for _ in range(n)];current=[scalar() for _ in range(width)];nxt=[scalar() for _ in range(width)]
                lanes=[([current[c] if c<width else f.ZERO for c in range(j,j+packing)],
                        [nxt[c] if c<width else f.ZERO for c in range(j,j+packing)]) for j in range(0,width,packing)]
                branch=dict(log_rows=n,width=width,packing=packing,row_point=point,lanes=lanes)
                expected=f.ZERO
                eq=w.eqs(point)
                for r in range(len(rows)):
                    for c in range(width):
                        term=f.add(f.scale(current[c],rows[r][c]),f.scale(nxt[c],rows[(r+1)%len(rows)][c]))
                        expected=f.add(expected,f.mul(eq[r],term))
                assert coefficient_claim(rows,branch)==expected;checks+=1
                for a,b in lanes:
                    u=[scalar() for _ in range(n+packing.bit_length()-1)]
                    assert w.mle(w.lane_weights(point,a,b),u)==w.lane_weight_mle(point,a,b,u);mles+=1
    report=dict(status='PASS',direct_row_vs_coefficient_claims=checks,lane_mle_checks=mles,
        scope='Ext8 dual Mobius/shift weights; independent full coefficient conversion and direct cyclic-row evaluation. No authenticated PCS opening or security claim.')
    args.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
if __name__=='__main__':main()
