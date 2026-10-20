"""Weighted-degree tests plus independently checked small GS interpolants.
The solver constructs witnesses; its general existence is not yet Lean-proved.
"""
import itertools
import json
import math
import random
from test_bivariate_multiplicity import add,compose,trim,bivariate_shift
from test_independent_constraint_mixing import evaluate
from test_bivariate_translation import translate
from test_synthetic_multiplicity import taylor


def kernel_vector(matrix,n,p):
    a=[row[:] for row in matrix]
    pivots=[]
    for col in range(n):
        at=next((i for i in range(len(pivots),len(a)) if a[i][col]),None)
        if at is None:continue
        rank=len(pivots)
        a[rank],a[at]=a[at],a[rank]
        inv=pow(a[rank][col],-1,p)
        a[rank]=[x*inv%p for x in a[rank]]
        for i in range(len(a)):
            if i!=rank:
                factor=a[i][col]
                a[i]=[(x-factor*y)%p for x,y in zip(a[i],a[rank])]
        pivots.append(col)
    free=next(i for i in range(n) if i not in pivots)
    v=[0]*n
    v[free]=1
    for i,col in enumerate(pivots):v[col]=-a[i][free]%p
    return v,len(pivots)


def interpolate(p,received,k,m,D):
    monomials=[(i,j) for j in range((D-1)//k+1) for i in range(D-k*j)]
    matrix=[]
    for x,y in enumerate(received):
        for r in range(m):
            for s in range(m-r):
                matrix.append([math.comb(i,r)*math.comb(j,s)*pow(x,i-r,p)*pow(y,j-s,p)%p
                    if i>=r and j>=s else 0 for i,j in monomials])
    assert len(monomials)>len(matrix)
    v,rank=kernel_vector(matrix,len(monomials),p)
    assert any(v) and all(sum(x*y for x,y in zip(row,v))%p==0 for row in matrix)
    rows=[[0]*(D-k*j) for j in range((D-1)//k+1)]
    for (i,j),value in zip(monomials,v):rows[j][i]=value
    # Check via translated coefficients, independently of matrix construction.
    for x,y in enumerate(received):
        translated=bivariate_shift(rows,x,y,p)
        assert all(c==0 for j,row in enumerate(translated) for i,c in enumerate(row) if i+j<m)
    return rows,len(monomials),len(matrix),rank


def main():
    rng=random.Random(92_999)
    degree_cases=0
    for p in (2,3,5,17):
        for k in range(4):
            for D in range(9):
                curve=[rng.randrange(p) for _ in range(k+1)]
                rows=[[rng.randrange(p) if i+k*j<D else 0 for i in range(10)] for j in range(6)]
                result=compose(rows,curve,p)
                assert not any(result[D:])
                degree_cases+=1
    witnesses=[]
    for p in (17,31):
        for _ in range(3):
            curve=[rng.randrange(p) for _ in range(3)]
            received=[evaluate(curve,x,p) for x in range(8)]
            for x in (6,7):received[x]=(received[x]+rng.randrange(1,p))%p
            k,m,D=2,2,12
            rows,variables,equations,rank=interpolate(p,received,k,m,D)
            decoded=[]
            for candidate in itertools.product(range(p),repeat=k+1):
                agreement=sum(evaluate(candidate,x,p)==y for x,y in enumerate(received))
                if m*agreement>=D:
                    substitution=compose(rows,candidate,p)
                    assert not any(substitution[D:])
                    assert not any(substitution)
                    for a in range(8):
                        if evaluate(candidate,a,p)!=received[a]:continue
                        b=received[a]
                        central=add(taylor(candidate,a,p,len(candidate)),[-b%p],p)
                        right=compose(translate(rows,a,b,p),central,p)
                        left=taylor(substitution,a,p,len(substitution))
                        assert max(len(left),len(right))<=p
                    decoded.append(list(candidate))
            assert curve in decoded
            witnesses.append(dict(prime=p,received=received,degree_weight=k,multiplicity=m,
                weighted_degree_bound=D,variables=variables,equations=equations,rank=rank,
                rows=rows,distinct_sample_size_guard_checked=True,exhaustive_qualifying_candidates=decoded))
    # Both degree guards matter: Q=Y^2 and degree-2 curve X^2 have degree4,
    # despite the invalid weight1/bound3 claim for that curve.
    assert trim(compose([[],[],[1]],[0,0,1],5))==[0,0,0,0,1]
    print(json.dumps(dict(weighted_degree_cases=degree_cases,interpolation_witnesses=witnesses,
        scope='Concrete checked GS witnesses and exhaustive small-field candidate checks. General interpolation existence and MCA exceptional-set bound are not proved.'),indent=2))


if __name__=='__main__':main()
