"""Common-power normalization and shared pole counting, including Hensel examples."""
from functools import lru_cache
import json
import random
from test_bivariate_multiplicity import add,mul
from test_independent_constraint_mixing import evaluate
from test_rational_specialization import analyze,ev,degree,poly,plus,times,neg,inv
from test_hensel_bounded_reconstruction import lift


def power(s,n,p):
    out=[1]
    for _ in range(n):out=mul(out,s,p)
    return out


@lru_cache(None)
def expand(e,s):
    if e[0]=='r':return inv(poly(s))
    if e[0]=='p':return e
    return (e[0],*(expand(a,s) for a in e[1:]))


@lru_cache(None)
def normalize(e,s,p):
    if e[0]=='p':return list(e[1]),0,max(len(e[1])-1,0)
    if e[0]=='r':return [1],1,0
    an,ae,ab=normalize(e[1],s,p)
    if e[0]=='neg':return [-c%p for c in an],ae,ab
    bn,be,bb=normalize(e[2],s,p)
    if e[0]=='mul':return mul(an,bn,p),ae+be,ab+bb
    m=max(ae,be);d=max(len(s)-1,0)
    return add(mul(an,power(s,m-ae,p),p),mul(bn,power(s,m-be,p),p),p),m,max(ab+d*(m-ae),bb+d*(m-be))


def main():
    rng=random.Random(3_415)
    def expression(depth,p):
        if not depth or rng.randrange(4)==0:
            return ('r',) if rng.randrange(3)==0 else poly([rng.randrange(p) for _ in range(rng.randrange(4))])
        op=rng.choice(('neg','add','mul'));a=expression(depth-1,p)
        return (op,a) if op=='neg' else (op,a,expression(depth-1,p))
    expressions=families=zero_certificates=0
    for p in (2,3,5,17):
        for s in ((1,1),(0,1),(0,-1%p,1),(1,),(0,0,1)):
            excluded=set()
            for _ in range(30):
                e=expression(3,p);expanded=expand(e,s)
                num,n,bound=normalize(e,s,p)
                assert degree(num)<=bound
                safe_zeros=[]
                for z in range(p):
                    value,safe=ev(expanded,z,p);sz=evaluate(s,z,p)
                    if not safe:excluded.add(z)
                    if sz:
                        assert safe and pow(sz,n,p)*value%p==evaluate(num,z,p)
                        if value==0:safe_zeros.append(z)
                if len(safe_zeros)>=bound+1:
                    assert not any(num);zero_certificates+=1
                expressions+=1
            assert len(excluded)<=degree(s)
            families+=1
    # Same Hensel recurrence as the prior raw guard diagnostic.
    coefficients=[poly([0])]
    for n in range(1,6):
        residual=poly([-1]) if n==1 else poly([0])
        for i in range(1,n):residual=plus(residual,times(coefficients[i],coefficients[n-i]))
        coefficients.append(times(neg(residual),('r',)))
    fixtures=[]
    for p in (2,3,5,17):
        raw=[];powers=[];budgets=[];excluded=set();checks=0
        for e in coefficients[1:]:
            expanded=expand(e,(1,1));_,_,_,budget,regular=analyze(expanded,p)
            assert regular
            raw.append(budget[2])
            num,n,bound=normalize(e,(1,1),p);powers.append(n);budgets.append(bound)
            assert degree(num)<=0  # Catalan-number numerators (possibly zero modulo p).
            for z in range(p):
                _,safe=ev(expanded,z,p)
                if not safe:excluded.add(z)
        assert raw==[1,3,9,27,81] and powers==[1,3,5,7,9] and len(excluded)==1
        for z in range(p):
            if (z+1)%p==0:continue
            actual=lift([[0,-1%p],[(z+1)%p],[1]],0,5,p)
            for n,e in enumerate(coefficients):
                num,d,_=normalize(e,(1,1),p)
                assert evaluate(num,z,p)*pow(pow((z+1)%p,d,p),-1,p)%p==actual[n]
                checks+=1
        fixtures.append(dict(prime=p,raw_guard_degree_budgets=raw,normalized_denominator_exponents=powers,
            numerator_degree_budgets=budgets,family_pole_bound=1,actual_excluded_challenges=len(excluded),specialized_coefficients=checks))
    # Unsafe points cannot be counted as zeros: 1/Z has totalized value0 at0.
    e=('r',);s=(0,1);num,_,_=normalize(e,s,5)
    value,safe=ev(expand(e,s),0,5)
    assert value==0 and not safe and any(num)
    # Distinctness matters when inferring a formal zero numerator.
    e=poly([0,1]);assert all(ev(e,z,5)[0]==0 for z in [0,0]) and any(e[1])
    print(json.dumps(dict(random_expressions=expressions,shared_denominator_families=families,
        formal_zero_certificates=zero_certificates,hensel_fixtures=fixtures,
        unsafe_zero_counterexamples=1,duplicate_sample_counterexamples=1,
        scope='Normalized common-power evaluation, numerator degrees and one shared pole set. Generic Hensel expression correspondence, algebraic extension and full MCA exception count remain open.'),indent=2))


if __name__=='__main__':main()
