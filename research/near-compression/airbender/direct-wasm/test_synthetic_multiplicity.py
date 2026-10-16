"""Independent binomial-coefficient check of synthetic Taylor/jet arithmetic."""
import itertools
import json
import math
from test_independent_constraint_mixing import evaluate


def quotient(cs,a,p):
    if len(cs)<2:
        return []
    out=[0]*(len(cs)-1)
    carry=cs[-1]
    for i in range(len(cs)-2,-1,-1):
        out[i]=carry
        carry=(cs[i]+a*carry)%p
    assert carry==evaluate(cs,a,p)
    return out


def taylor(cs,a,p,count):
    result=[]
    for _ in range(count):
        result.append(evaluate(cs,a,p))
        cs=quotient(cs,a,p)
    return result


def multiply(a,b,p):
    out=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):out[i+j]=(out[i+j]+x*y)%p
    return out


def main():
    cases=evaluations=certificates=0
    for p in (2,3,5):
        for n in range(5):
            for cs in itertools.product(range(p),repeat=n):
                for a in range(p):
                    jets=taylor(cs,a,p,n+2)
                    expected=[sum(cs[j]*math.comb(j,i)*pow(a,j-i,p)
                                  for j in range(i,n))%p for i in range(n+2)]
                    assert jets==expected
                    for x in range(p):
                        assert evaluate(jets,x,p)==evaluate(cs,(a+x)%p,p)
                        evaluations+=1
                    if any(cs):
                        first=next(i for i,j in enumerate(jets) if j)
                        assert first<n
                    cases+=1
        for length in range(5):
            for nodes in itertools.product(range(p),repeat=length):
                cs=[1,2%p]
                for a in nodes:cs=multiply(cs,[-a%p,1],p)
                current=cs
                for a in nodes:
                    assert evaluate(current,a,p)==0
                    current=quotient(current,a,p)
                assert current==[1,2%p]
                certificates+=1
        # X^p has all positive-order ordinary derivatives identically zero,
        # but its p-th synthetic Taylor coefficient at zero is one.
        frobenius=[0]*p+[1]
        derivative=[i*frobenius[i]%p for i in range(1,len(frobenius))]
        assert not any(derivative)
        assert taylor(frobenius,0,p,p+1)==[0]*p+[1]
        # Checking the same root twice without division is not multiplicity.
        cs=[0,1]
        assert evaluate(cs,0,p)==0 and evaluate(quotient(cs,0,p),0,p)==1
    print(json.dumps(dict(taylor_cases=cases,evaluation_identities=evaluations,
        sequential_root_certificates=certificates,
        characteristic_regressions=['ordinary derivatives miss X^p multiplicity boundary',
                                   'repeated root evaluations without quotient are insufficient'],
        scope='Univariate synthetic multiplicity foundations; multi-point Hasse equivalence, bivariate interpolation and MCA remain open.'),indent=2))


if __name__ == '__main__':
    main()
