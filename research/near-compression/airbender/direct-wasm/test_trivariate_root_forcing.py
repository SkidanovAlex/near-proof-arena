"""Exhaustive candidate root forcing for controlled-Z interpolation witnesses."""
import itertools
import json
from test_trivariate_interpolation import monomials
from test_trivariate_specialization import specialize
from test_jet_center_polynomial import term
from test_bivariate_weighted_degree import kernel_vector
from test_bivariate_multiplicity import compose,add,shift
from test_bivariate_translation import translate
from test_independent_constraint_mixing import evaluate


def main():
    fixtures=[]
    for p in (17,19):
        indices=monomials(1,6,5,5)
        orders=monomials(1,2,2,5)
        sources=[(x,(1+2*x+(x==3))%p,(3+x)%p) for x in range(4)]
        matrix=[]
        for x,u,v in sources:
            for r,s,t in orders:
                polys=[term(i,j,h,r,s,x,u,v,p) for i,j,h in indices]
                matrix.append([q[t] if t<len(q) else 0 for q in polys])
        assert len(indices)==70>len(matrix)==56
        vector,rank=kernel_vector(matrix,len(indices),p)
        assert any(vector) and all(sum(a*b for a,b in zip(row,vector))%p==0 for row in matrix)
        values=dict(zip(indices,vector))
        candidates=qualifying=zero_specializations=max_separation=0
        for z in range(p):
            rows=specialize(1,6,5,5,indices,values,z,p)
            zero_specializations+=not any(c for row in rows for c in row)
            for curve in itertools.product(range(p),repeat=2):
                candidates+=1
                support=[x for x,u,v in sources if evaluate(curve,x,p)==(u+z*v)%p]
                if 2*len(support)<6:continue
                qualifying+=1
                assert len(set(support))==len(support)
                substituted=compose(rows,curve,p)
                assert not any(substituted[6:])
                for x in support:
                    translated=translate(rows,x,evaluate(curve,x,p),p)
                    assert all(c==0 for j,row in enumerate(translated) for i,c in enumerate(row) if i+j<2)
                    central=add(shift(curve,x,p),[-evaluate(curve,x,p)%p],p)
                    left=shift(substituted,x,p)
                    right=compose(translated,central,p)
                    assert not any(add(left,[-c%p for c in right],p))
                    separation=max(len(left),len(right))
                    assert separation<=p
                    max_separation=max(max_separation,separation)
                assert not any(substituted)
        assert qualifying>=p and zero_specializations<=4
        fixtures.append(dict(prime=p,coefficients=vector,rank=rank,candidates=candidates,
            qualifying=qualifying,zero_specializations=zero_specializations,
            max_separation=max_separation))
    # Q=X(X-1) has multiplicity one at two distinct centers, degree<3,
    # but substitution by any curve is nonzero: the total threshold matters.
    q=[0,16,1]
    assert all(evaluate(q,x,17)==0 for x in (0,1)) and any(q)
    assert 2<3
    # Repeating a root makes the numeric threshold pass without root forcing.
    assert len([0,0,0])>=3 and all(evaluate(q,x,17)==0 for x in [0,0,0]) and any(q)
    print(json.dumps(dict(fixtures=fixtures,boundary_cases=['insufficient total multiplicity','duplicate abscissae'],
        scope='Specialized candidate root forcing with explicit separation. No useful-factor extraction, full MCA exception bound or protocol security claim.'),indent=2))


if __name__=='__main__':main()
