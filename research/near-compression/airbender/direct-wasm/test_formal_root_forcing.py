"""Translation and root forcing where polynomial lengths exceed field size."""
import itertools
import json
import random
from test_bivariate_multiplicity import add,mul,compose,shift
from test_bivariate_translation import translate,mixed_order
from test_bivariate_curve_division import equal,nonzero
from test_synthetic_multiplicity import taylor
from test_independent_constraint_mixing import evaluate
from test_trivariate_interpolation import monomials
from test_trivariate_specialization import specialize
from test_jet_center_polynomial import term
from test_bivariate_weighted_degree import kernel_vector


def main():
    rng=random.Random(143031)
    identities=exceeds=0
    for p in (2,3,5,17):
        for _ in range(100):
            a=rng.randrange(p)
            f,g=[[rng.randrange(p) for _ in range(rng.randrange(1,9))] for _ in range(2)]
            product=mul(f,g,p)
            assert equal(taylor(product,a,p,len(product)),mul(shift(f,a,p),shift(g,a,p),p))
            rows=[[rng.randrange(p) for _ in range(rng.randrange(1,9))] for _ in range(rng.randrange(1,6))]
            substituted=compose(rows,f,p)
            left=taylor(substituted,a,p,len(substituted))
            b=evaluate(f,a,p)
            central=add(shift(f,a,p),[-b%p],p)
            right=compose(translate(rows,a,b,p),central,p)
            assert equal(left,right)
            exceeds+=max(len(left),len(right))>p
            identities+=1
    fixtures=[]
    for p,N,DX,height,DZ in ((2,2,4,3,3),(3,3,6,5,5),(5,3,6,5,5)):
        indices=monomials(1,DX,height,DZ);orders=monomials(1,2,2,DZ)
        sources=[(x,(1+2*x)%p,(3+x)%p) for x in range(N)]
        matrix=[]
        for x,u,v in sources:
            for r,s,t in orders:
                polys=[term(i,j,h,r,s,x,u,v,p) for i,j,h in indices]
                matrix.append([q[t] if t<len(q) else 0 for q in polys])
        assert len(matrix)<len(indices)
        vector,rank=kernel_vector(matrix,len(indices),p)
        assert any(vector) and all(sum(a*b for a,b in zip(row,vector))%p==0 for row in matrix)
        values=dict(zip(indices,vector))
        eligible=guard_failures=nonzero_z=0
        for z in range(p):
            rows=specialize(1,DX,height,DZ,indices,values,z,p)
            nz=nonzero(rows);nonzero_z+=nz
            candidates=[]
            for curve in itertools.product(range(p),repeat=2):
                support=[x for x,u,v in sources if evaluate(curve,x,p)==(u+z*v)%p]
                if 2*len(support)<DX:continue
                eligible+=1;candidates.append(curve)
                substituted=compose(rows,curve,p)
                assert not any(substituted)
                for x in support:
                    trans=translate(rows,x,evaluate(curve,x,p),p)
                    assert mixed_order(trans,2)
                    central=add(shift(curve,x,p),[-evaluate(curve,x,p)%p],p)
                    if max(len(substituted),len(compose(trans,central,p)))>p:guard_failures+=1
            if nz:assert len(candidates)<=height-1
        assert eligible>=p and nonzero_z>0
        fixtures.append(dict(prime=p,variables=len(indices),constraints=len(matrix),rank=rank,
            coefficients=vector,eligible=eligible,nonzero_specializations=nonzero_z,
            old_separation_guard_failures=guard_failures))
    assert exceeds>0 and sum(w['old_separation_guard_failures'] for w in fixtures)>0
    print(json.dumps(dict(translation_identity_cases=identities,identities_exceeding_field_size=exceeds,
        fixtures=fixtures,scope='Formal translation, guard-free root forcing and candidate count for nonzero specializations. Full MCA exceptions and protocol soundness remain open.'),indent=2))


if __name__=='__main__':main()
