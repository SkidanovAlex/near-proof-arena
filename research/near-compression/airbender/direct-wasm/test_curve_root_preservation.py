"""Coefficient algebra, formal divided differences, and exhaustive curve roots."""
import itertools
import json
import random
from test_bivariate_multiplicity import add,mul,compose
from test_bivariate_curve_division import quotient,factor,equal,nonzero


def sub(a,b,p):return add(a,[-c%p for c in b],p)


def main():
    rng=random.Random(48_808)
    algebra=differences=preserved=root_fixtures=0
    for p in (2,3,5,17):
        for _ in range(150):
            a,b,c=[[rng.randrange(p) for _ in range(rng.randrange(7))] for _ in range(3)]
            assert equal(mul(a,b,p),mul(b,a,p))
            assert equal(mul(mul(a,b,p),c,p),mul(a,mul(b,c,p),p))
            assert equal(mul(add(a,b,p),c,p),add(mul(a,c,p),mul(b,c,p),p))
            assert equal(mul(a,add(b,c,p),p),add(mul(a,b,p),mul(a,c,p),p))
            assert equal(mul(sub(a,b,p),c,p),sub(mul(a,c,p),mul(b,c,p),p))
            assert equal(mul(a+[0,0],b+[0],p),mul(a,b,p))
            algebra+=1
            rows=[[rng.randrange(p) for _ in range(rng.randrange(7))] for _ in range(rng.randrange(7))]
            lhs=sub(compose(rows,b,p),compose(rows,a,p),p)
            rhs=mul(sub(b,a,p),compose(quotient(rows,a,p),b,p),p)
            assert equal(lhs,rhs)
            differences+=1
        curves=[list(c) for c in itertools.product(range(p),repeat=2)]
        for _ in range(25):
            rows=[[1]]
            for _ in range(rng.randrange(1,5)):
                rows=factor(rows,rng.choice(curves),p)
            assert nonzero(rows)
            roots=[c for c in curves if not any(compose(rows,c,p))]
            assert 1<=len(roots)<=len(rows)-1
            root_fixtures+=1
            for f in roots:
                q=quotient(rows,f,p)
                assert nonzero(q) and len(q)==len(rows)-1
                for g in roots:
                    if equal(f,g):continue
                    assert not any(compose(q,g,p))
                    preserved+=1
        # Formally distinct curves can be identical as field-valued functions.
        f=[0]*(p+1);f[1]=-1%p;f[p]=1
        rows=factor(factor([[1]],[0],p),f,p)
        assert not equal(f,[0])
        assert not any(compose(quotient(rows,f,p),[0],p))
    # Structural inequality caused by trailing zeros is insufficient.
    f,g=[1],[1,0]
    rows=factor([[1]],f,5)
    assert f!=g and equal(f,g)
    assert not any(compose(rows,g,5)) and any(compose(quotient(rows,f,5),g,5))
    # Counting duplicate roots would violate the degree bound.
    assert len([f,f])>len(rows)-1
    print(json.dumps(dict(algebra_cases=algebra,divided_difference_cases=differences,
        exhaustive_root_fixtures=root_fixtures,distinct_root_preservations=preserved,
        same_function_distinct_curve_cases=4,padding_distinctness_counterexamples=1,
        duplicate_count_counterexamples=1,
        scope='Formal root preservation and stored Y-degree root count. MCA useful-factor selection, Hensel lifting and complete exceptional set remain open.'),indent=2))


if __name__=='__main__':main()
