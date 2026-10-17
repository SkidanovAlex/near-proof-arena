"""Compare smooth Hensel reconstruction with exhaustive polynomial candidates."""
import itertools
import json
import random
from test_bivariate_multiplicity import compose
from test_bivariate_curve_division import factor,equal
from test_hensel_coefficient_step import coeff,slope,perturb,order


def lift(rows,a,n,p):
    f=[a]
    assert coeff(compose(rows,f,p),0)==0 and slope(rows,f,p)!=0
    for i in range(1,n+1):
        residual=compose(rows,f,p)
        assert order(residual,i)
        f=perturb(f,i,-coeff(residual,i)*pow(slope(rows,f,p),-1,p)%p,p)
    return f


def weighted_bound(rows,k):
    return max((i+k*j+1 for j,row in enumerate(rows) for i,c in enumerate(row) if c),default=0)


def main():
    rng=random.Random(7_997)
    fixtures=candidate_checks=smooth_roots=singular_roots=branches=rejections=certificates=0
    for p in (2,3,5,17):
        for k in range(2 if p==17 else 3):
            for trial in range(20):
                if trial%2:
                    rows=[[1]]
                    for _ in range(rng.randrange(1,4)):
                        rows=factor(rows,[rng.randrange(p) for _ in range(k+1)],p)
                else:
                    rows=[[rng.randrange(p) for _ in range(rng.randrange(1,4))] for _ in range(rng.randrange(2,5))]
                all_roots=[]
                for c in itertools.product(range(p),repeat=k+1):
                    candidate_checks+=1
                    if not any(compose(rows,c,p)):all_roots.append(c)
                smooth=[c for c in all_roots if slope(rows,c,p)!=0]
                singular_roots+=len(all_roots)-len(smooth)
                smooth_roots+=len(smooth)
                extracted=[]
                D=weighted_bound(rows,k);n=max(k,D-1)
                for a in range(p):
                    if coeff(compose(rows,[a],p),0)!=0 or slope(rows,[a],p)==0:continue
                    branches+=1
                    short=lift(rows,a,k,p)
                    exact=not any(compose(rows,short,p))
                    matching=[c for c in smooth if c[0]==a]
                    assert len(matching)<=1 and exact==bool(matching)
                    if exact:
                        assert equal(short,matching[0])
                        extracted.append(tuple(short))
                    else:rejections+=1
                    long=lift(rows,a,n,p)
                    tail_zero=not any(long[k+1:])
                    assert tail_zero==bool(matching)
                    if tail_zero:assert not any(compose(rows,long,p))
                    if matching:assert equal(long,matching[0])
                    certificates+=1
                assert set(extracted)==set(smooth)
                fixtures+=1
    # Insufficient residual precision: Y-X^2 has lift0 through degree1,
    # but its residual is not zero; weighted bound D=3 exceeds precision2.
    rows=[[0,0,4],[1]]
    f=lift(rows,0,1,5)
    assert not any(f[2:]) and order(compose(rows,f,5),2) and any(compose(rows,f,5))
    assert weighted_bound(rows,1)==3
    # Even enough precision does not imply the high-coefficient condition.
    rows=[[0,4],[1],[4]]
    f=lift(rows,0,2,5)
    assert order(compose(rows,f,5),3) and any(f[2:]) and any(compose(rows,f,5))
    assert weighted_bound(rows,1)==3
    assert rejections>0 and smooth_roots>0 and singular_roots>0
    print(json.dumps(dict(fixtures=fixtures,exhaustive_candidates=candidate_checks,
        smooth_exact_roots=smooth_roots,singular_roots_outside_scope=singular_roots,
        smooth_initial_branches=branches,nonterminating_within_bound=rejections,
        high_coefficient_certificates=certificates,insufficient_precision_counterexamples=1,
        missing_tail_condition_counterexamples=1,
        scope='Sound and complete bounded-degree reconstruction through smooth initial values. Singular branches, rational-function specialization, useful factors and full MCA exceptions remain open.'),indent=2))


if __name__=='__main__':main()
