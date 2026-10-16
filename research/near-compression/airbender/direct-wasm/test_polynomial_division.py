"""Check degree-recursive polynomial division against independent long division."""
import json
import random
from test_bivariate_multiplicity import add,mul
from test_bivariate_curve_division import equal
from test_bezout_smoothness import divide,sub


def coeff(a,i):return a[i] if i<len(a) else 0
def deglt(a,d):return not any(a[d:])


def bounded(p,q,d,n,prime):
    assert deglt(q,d+1) and coeff(q,d)!=0 and deglt(p,n+d)
    if not n:return [],p
    index=n-1+d
    c=coeff(p,index)*pow(coeff(q,d),-1,prime)%prime
    correction=[0]*(n-1)+[c]
    smaller=sub(p,mul(correction,q,prime),prime)
    assert deglt(smaller,index)
    a,r=bounded(smaller,q,d,n-1,prime)
    return add(a,correction,prime),r


def main():
    rng=random.Random(472_425)
    cases=constant=zero_inputs=padding=shifts=0
    for prime in (2,3,5,17):
        for n in range(6):
            for d in range(5):
                for _ in range(10):
                    q=[rng.randrange(prime) for _ in range(d)]+[rng.randrange(1,prime)]
                    p=[rng.randrange(prime) for _ in range(n+d)]
                    if rng.randrange(5)==0:p=[0]*len(p)
                    qp,pp=rng.randrange(4),rng.randrange(4)
                    q += [0]*qp;p += [0]*pp
                    a,r=bounded(p,q,d,n,prime)
                    independent,rem=divide(p,q,prime)
                    assert equal(add(mul(a,q,prime),r,prime),p)
                    assert deglt(a,n) and deglt(r,d)
                    assert equal(a,independent) and equal(r,rem)
                    cases+=1;constant+=d==0;zero_inputs+=not any(p);padding+=bool(pp or qp)
                    for shift in range(4):
                        monomial=[0]*shift+[1];product=mul(monomial,q,prime)
                        for i in range(12):
                            assert coeff(product,i)==(0 if i<shift else coeff(q,i-shift))
                            shifts+=1
    # The declared leading coefficient must actually be nonzero.
    rejected=0
    for p,q,d,n in (([1],[1,0],1,1),([1],[0],0,1)):
        try:bounded(p,q,d,n,5)
        except AssertionError:rejected+=1
        else:raise AssertionError('invalid divisor certificate accepted')
    assert rejected==2
    print(json.dumps(dict(bounded_division_cases=cases,constant_divisors=constant,zero_dividends=zero_inputs,
        padded_cases=padding,monomial_shift_coefficient_checks=shifts,invalid_leading_or_zero_divisors_rejected=rejected,
        scope='General formal polynomial division existence and degree bounds. Euclidean/Bezout certificate existence, irreducible factorization and full MCA remain open.'),indent=2))


if __name__=='__main__':main()
