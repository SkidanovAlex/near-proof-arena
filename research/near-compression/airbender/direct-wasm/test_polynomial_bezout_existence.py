"""Degree-recursive Bezout construction and exhaustive small irreducibles."""
import itertools
import json
import random
from test_bezout_smoothness import divide,egcd,derivative,sub
from test_bivariate_multiplicity import add,mul,trim
from test_bivariate_curve_division import equal


def euclid_first(p,q,prime):
    p=trim(p);q=trim(q);assert p
    t,r=divide(q,p,prime)
    if not r:return p,[1],[],1
    assert len(r)<len(p)
    g,U,V,depth=euclid_first(r,p,prime)
    return g,sub(V,mul(U,t,prime),prime),U,depth+1


def irreducible(q,p):
    n=len(trim(q))-1
    if n<1:return False
    for d in range(1,n//2+1):
        for cs in itertools.product(range(p),repeat=d):
            if not divide(q,list(cs)+[1],p)[1]:return False
    return True


def main():
    rng=random.Random(200_22)
    gcd_cases=constant_cases=zero_seconds=0;max_depth=0
    for p in (2,3,5,17):
        for _ in range(150):
            first=[rng.randrange(p) for _ in range(rng.randrange(1,8))]
            if not any(first):first[0]=1
            second=[rng.randrange(p) for _ in range(rng.randrange(8))]
            first += [0]*rng.randrange(4);second += [0]*rng.randrange(4)
            g,A,B,depth=euclid_first(first,second,p)
            assert any(g) and len(trim(g))<=len(trim(first))
            assert equal(g,add(mul(A,first,p),mul(B,second,p),p))
            assert not divide(first,g,p)[1] and not divide(second,g,p)[1]
            independent,_,_=egcd(first,second,p)
            scale=pow(trim(g)[-1],-1,p)
            assert equal([scale*c%p for c in g],independent)
            if len(trim(g))==1:
                c=pow(g[0],-1,p);AA=[c*x%p for x in A];BB=[c*x%p for x in B]
                assert equal(add(mul(AA,first,p),mul(BB,second,p),p),[1])
                constant_cases+=1
            zero_seconds+=not any(second)
            gcd_cases+=1;max_depth=max(max_depth,depth)
    scanned=certified=0;witnesses=[]
    for p,max_degree in ((2,1),(3,2),(5,3),(17,2)):
        for d in range(1,max_degree+1):
            assert d<p
            for cs in itertools.product(range(p),repeat=d):
                q=list(cs)+[1];scanned+=1
                if not irreducible(q,p):continue
                dq=derivative(q,p);assert any(dq)
                # Match the Lean construction's smaller-degree first argument.
                g,U,V,_=euclid_first(dq,q,p)
                assert len(trim(g))==1
                inv=pow(g[0],-1,p)
                A=[inv*c%p for c in V];B=[inv*c%p for c in U]
                assert equal(add(mul(A,q,p),mul(B,dq,p),p),[1])
                certified+=1
                if d>1 and len(witnesses)<6:witnesses.append(dict(prime=p,polynomial=q,A=A,B=B))
    # Nonzero derivative plus small degree is insufficient without irreducibility.
    q=[1,1,1]  # (Y-1)^2 over F3.
    assert len(q)-1<3 and any(derivative(q,3)) and not irreducible(q,3)
    g,_,_,_=euclid_first(derivative(q,3),q,3);assert len(g)>1
    try:euclid_first([0],[0],5)
    except AssertionError:pass
    else:raise AssertionError('zero first input accepted')
    print(json.dumps(dict(euclidean_witnesses=gcd_cases,unit_certificates=constant_cases,
        zero_second_inputs=zero_seconds,max_euclidean_depth=max_depth,
        monic_polynomials_screened=scanned,irreducible_derivative_certificates=certified,
        reducibility_counterexamples=1,zero_first_input_rejections=1,witnesses=witnesses,
        scope='General Euclidean/Bezout existence and low-degree irreducible derivative certificate existence. Factorization, algebraic extension/root construction and full MCA remain open.'),indent=2))


if __name__=='__main__':main()
