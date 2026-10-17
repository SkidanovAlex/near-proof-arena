"""Check the newly formal mixed-jet matrix with synthetic entries and direct translation."""
import json
import random
from test_bivariate_translation import translate
from test_synthetic_multiplicity import taylor
from test_bivariate_weighted_degree import kernel_vector
from test_gs_monomial_space import monomials,encode


def jet_monomial(n,a,r,p):
    return taylor([0]*n+[1],a,p,r+1)[r]


def coefficient(rows,r,s):
    return rows[s][r] if s<len(rows) and r<len(rows[s]) else 0


def matrix_row(indices,a,b,r,s,p):
    return [jet_monomial(i,a,r,p)*jet_monomial(j,b,s,p)%p for i,j in indices]


def main():
    rng=random.Random(6618218)
    checks=0
    for p in (2,3,5,17):
        for _ in range(80):
            k,D,height=rng.randrange(4),rng.randrange(8),rng.randrange(6)
            indices=monomials(k,D,height)
            values={i:rng.randrange(p) for i in indices}
            rows=encode(k,D,height,values)
            a,b=rng.randrange(p),rng.randrange(p)
            translated=translate(rows,a,b,p)
            for r in range(5):
                for s in range(5):
                    entry=sum(c*values[i] for c,i in zip(matrix_row(indices,a,b,r,s,p),indices))%p
                    assert entry==coefficient(translated,r,s)
                    checks+=1
    witnesses=[]
    configs=[(2,3,1,1,3,3),(3,3,2,1,6,3),(5,2,2,0,3,3),
             (17,8,2,2,12,6),(31,8,2,2,12,6),(3,4,0,1,1,1)]
    for p,N,m,k,D,height in configs:
        for _ in range(3):
            points=[(rng.randrange(p),rng.randrange(p)) for _ in range(N)]
            indices=monomials(k,D,height)
            orders=[(r,t-r) for t in range(m) for r in range(t+1)]
            matrix=[matrix_row(indices,a,b,r,s,p) for a,b in points for r,s in orders]
            assert len(matrix)<len(indices)
            assert 2*len(matrix)==N*m*(m+1)
            vector,rank=kernel_vector(matrix,len(indices),p)
            rows=encode(k,D,height,dict(zip(indices,vector)))
            assert any(c for row in rows for c in row)
            for a,b in points:
                translated=translate(rows,a,b,p)
                assert all(coefficient(translated,r,s)==0 for r,s in orders)
            witnesses.append(dict(prime=p,points=points,multiplicity=m,weight=k,
                weighted_degree_bound=D,height=height,variables=len(indices),constraints=len(matrix),
                rank=rank,rows=rows))
    assert len(monomials(0,0,3))==0  # dimension premise cannot pass
    print(json.dumps(dict(mixed_matrix_checks=checks,interpolation_witnesses=witnesses,
        scope='General mixed-jet interpolation existence is Lean-proved under the exact dimension inequality. Solver refinement, MCA exceptions and protocol soundness are not claimed.'),indent=2))


if __name__=='__main__':main()
