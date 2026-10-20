"""Check polynomial-in-center jets and coefficient constraints along affine lines."""
import functools
import itertools
import json
import math
from test_bivariate_multiplicity import add,compose,trim
from test_bivariate_translation import translate
from test_bivariate_weighted_degree import kernel_vector
from test_synthetic_multiplicity import taylor
from test_independent_constraint_mixing import evaluate


@functools.lru_cache(None)
def center(cs,r,p):
    if not cs:return ()
    if r==0:return cs
    return tuple(add(list(center(cs[1:],r-1,p)),[0]+list(center(cs[1:],r,p)),p))


def term(i,j,h,r,s,x,u,v,p):
    ypoly=center(tuple([0]*j+[1]),s,p)
    line=compose([[c] for c in ypoly],[u,v],p)
    factor=taylor([0]*i+[1],x,p,r+1)[r]
    return [0]*h+[factor*c%p for c in line]


def main():
    checks=0
    for p in (2,3,5,17):
        for j in range(11):
            for s in range(13):
                actual=list(center(tuple([0]*j+[1]),s,p))
                expected=([0]*(j-s)+[math.comb(j,s)%p]) if s<=j else []
                assert trim(actual)==trim(expected)
                for u,v in itertools.product(range(min(p,3)),repeat=2):
                    poly=term(3,j,2,1,s,2%p,u,v,p)
                    assert not any(poly[max(j+3-s,0):])
                    for z in range(p):
                        independent=(3*pow(2,2,p)*pow(z,2,p)*math.comb(j,s)*pow((u+v*z)%p,j-s,p))%p if s<=j else 0
                        assert evaluate(poly,z,p)==independent
                    checks+=1
    witnesses=[]
    for p in (3,5,17):
        k,DX,height,Zcap,m=1,6,5,5,2
        indices=[(i,j,h) for j in range(height) for i in range(DX-k*j) for h in range(Zcap-j)]
        sources=[(x,(x*x+1)%p,(x+2)%p) for x in range(3)]
        constraints=[(x,u,v,r,s,t) for x,u,v in sources for s in range(m)
            for r in range(m-s) for t in range(Zcap-s)]
        matrix=[]
        for x,u,v,r,s,t in constraints:
            polys=[term(i,j,h,r,s,x,u,v,p) for i,j,h in indices]
            matrix.append([q[t] if t<len(q) else 0 for q in polys])
        assert len(indices)==70 and len(matrix)==42
        vector,rank=kernel_vector(matrix,len(indices),p)
        assert any(vector)
        for x,u,v in sources:
            for s in range(m):
                for r in range(m-s):
                    polynomial=[]
                    for value,(i,j,h) in zip(vector,indices):
                        polynomial=add(polynomial,[value*c%p for c in term(i,j,h,r,s,x,u,v,p)],p)
                    assert not any(polynomial)
            # Independent specialization of Q followed by bivariate translation.
            for z in range(p):
                rows=[[0]*(DX-k*j) for j in range(height)]
                for value,(i,j,h) in zip(vector,indices):rows[j][i]=(rows[j][i]+value*pow(z,h,p))%p
                translated=translate(rows,x,(u+v*z)%p,p)
                for s in range(m):
                    for r in range(m-s):
                        assert (translated[s][r] if s<len(translated) and r<len(translated[s]) else 0)==0
        witnesses.append(dict(prime=p,sources=sources,variables=70,equations=42,rank=rank,
            monomials=indices,coefficients=vector))
    print(json.dumps(dict(center_line_cases=checks,trivariate_witnesses=witnesses,
        scope='Formal term and sum Z-degree/coefficient bounds. General trivariate interpolation existence and formal specialization bridge remain open; these are concrete witness checks.'),indent=2))


if __name__=='__main__':main()
