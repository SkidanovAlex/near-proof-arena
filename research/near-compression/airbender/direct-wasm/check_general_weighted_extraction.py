"""Check the general functional's formula against executable Ext8 folding.
This validates algebra wiring, not extraction probabilities or hash security.
"""
import hashlib,json,random
from pathlib import Path
import pq384_ext8_reference as e

def dot(a,b):
    assert len(a)==len(b)
    out=e.ZERO
    for x,y in zip(a,b):out=e.add(out,e.mul(x,y))
    return out

def run():
    rng=random.Random(1709)
    draw=lambda:tuple(rng.randrange(e.P) for _ in range(8))
    checks=0
    for size in (2,4,8,16,32):
        for _ in range(8):
            cs=[draw() for _ in range(size)];ws=[draw() for _ in range(size)]
            a=dot(ws[::2],cs[::2]);b=dot(ws[::2],cs[1::2])
            c=dot(ws[1::2],cs[::2]);d=dot(ws[1::2],cs[1::2])
            expected=[a,e.sub(e.add(b,c),e.scale(a,2)),e.add(e.sub(e.sub(a,b),c),d)]
            assert e.quadratic(cs,ws)==expected
            for r in (e.ZERO,e.ONE,draw()):
                folded=dot(e.affine_fold(cs,r),e.affine_fold(ws,r))
                assert folded==e.evaluate(expected,r)
                checks+=1
    # Equality weights for point[2,3], plus one monomial injection at z=3.
    # The even/odd rows no longer share a common vector times two scalars.
    old=[2,-4,-3,6];new=[old[i]+3**i for i in range(4)]
    determinant=(new[0]*new[3]-new[1]*new[2])%e.P
    assert determinant==105 and determinant!=0
    return dict(status='PASS',quadratics=40,fold_evaluations=checks,
        nonfactorable_injection=dict(old_weights=old,new_weights=new,determinant=determinant),
        scope='General quadratic and child functional parity, including r=0 and r=1; explicit witness that accumulated weights need not factor.',
        limits=['No runtime probability or extraction theorem established by this check.','No PCS acceptance-to-candidate or rate-shift transfer theorem.'],
        source_sha256={n:hashlib.sha256(Path(__file__).with_name(n).read_bytes()).hexdigest() for n in [Path(__file__).name,'pq384_ext8_reference.py']})
if __name__=='__main__':
    r=run();(Path(__file__).resolve().parents[2]/'results/general-weighted-runtime.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
