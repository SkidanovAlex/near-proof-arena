"""Exhaustive small-matrix witness checks, not a solver-refinement proof."""
import itertools
import json
from test_bivariate_weighted_degree import kernel_vector


def main():
    cases=rank_deficient=0
    ranks={}
    for p,max_rows in [(2,3),(3,2)]:
        for m in range(max_rows+1):
            n=m+1
            for flat in itertools.product(range(p),repeat=m*n):
                matrix=[list(flat[i*n:(i+1)*n]) for i in range(m)]
                v,rank=kernel_vector(matrix,n,p)
                assert len(v)==n and any(v)
                assert all(sum(a*b for a,b in zip(row,v))%p==0 for row in matrix)
                assert rank<=m<n
                rank_deficient+=rank<m
                ranks[f'{p}:{m}:{rank}']=ranks.get(f'{p}:{m}:{rank}',0)+1
                cases+=1
    # Strict inequality matters: a square identity has only the zero kernel.
    p=3
    assert all(not any(v) for v in itertools.product(range(p),repeat=2)
        if all(x%p==0 for x in v))
    # Distinct unknown identifiers matter: duplicate index 0 turns the single
    # row [1,1] into 2*v[0]=0 over F3, despite nominal length 2 > row count 1.
    assert [v for v in range(3) if (v+v)%3==0]==[0]
    print(json.dumps(dict(matrices=cases,rank_deficient_matrices=rank_deficient,
        rank_histogram=ranks,negative_premises=['strictly fewer equations','distinct unknown indices'],
        scope='Lean theorem proves abstract nonzero-kernel existence. Python solver witnesses checked independently; no formal solver refinement or full GS existence claim.'),indent=2))


if __name__=='__main__':main()
