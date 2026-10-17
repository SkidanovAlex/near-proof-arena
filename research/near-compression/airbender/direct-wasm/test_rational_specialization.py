"""Guarded rational arithmetic and symbolic smooth Hensel coefficients."""
from functools import lru_cache
import json
import random
from test_bivariate_multiplicity import add,mul
from test_independent_constraint_mixing import evaluate
from test_hensel_bounded_reconstruction import lift


def poly(cs):return ('p',tuple(cs))
def neg(a):return ('neg',a)
def inv(a):return ('inv',a)
def plus(a,b):return ('add',a,b)
def times(a,b):return ('mul',a,b)


@lru_cache(None)
def analyze(e,p):
    op=e[0]
    if op=='p':return list(e[1]),[1],[1],(max(len(e[1])-1,0),0,0),True
    an,ad,ag,(na,da,ga),ar=analyze(e[1],p)
    if op=='neg':return [-c%p for c in an],ad,ag,(na,da,ga),ar
    if op=='inv':return ad,an,mul(ag,an,p),(da,na,ga+na),ar and any(an)
    bn,bd,bg,(nb,db,gb),br=analyze(e[2],p)
    if op=='add':return add(mul(an,bd,p),mul(bn,ad,p),p),mul(ad,bd,p),mul(ag,bg,p),(max(na+db,nb+da),da+db,ga+gb),ar and br
    return mul(an,bn,p),mul(ad,bd,p),mul(ag,bg,p),(na+nb,da+db,ga+gb),ar and br


@lru_cache(None)
def ev(e,z,p):
    if e[0]=='p':return evaluate(e[1],z,p),True
    a,sa=ev(e[1],z,p)
    if e[0]=='neg':return -a%p,sa
    if e[0]=='inv':return (pow(a,-1,p) if a else 0),sa and a!=0
    b,sb=ev(e[2],z,p)
    return ((a+b)%p if e[0]=='add' else a*b%p),sa and sb


def degree(a):return max((i for i,c in enumerate(a) if c),default=-1)


def check(e,p):
    num,den,guard,budgets,regular=analyze(e,p)
    assert all(degree(q)<=b for q,b in zip((num,den,guard),budgets))
    if regular:assert any(guard)
    excluded=0
    for z in range(p):
        value,safe=ev(e,z,p)
        good=evaluate(guard,z,p)!=0
        assert safe==good
        excluded+=not safe
        if good:
            d=evaluate(den,z,p);n=evaluate(num,z,p)
            assert d!=0 and d*value%p==n and value==n*pow(d,-1,p)%p
    if regular:assert excluded<=budgets[2]
    return regular,excluded,budgets


def main():
    rng=random.Random(86_744)
    def expression(depth,p):
        if not depth or rng.randrange(4)==0:return poly([rng.randrange(p) for _ in range(rng.randrange(4))])
        op=rng.choice(('neg','inv','add','mul'))
        a=expression(depth-1,p)
        return (op,a) if op in ('neg','inv') else (op,a,expression(depth-1,p))
    tested=regular=0
    for p in (2,3,5,17):
        for _ in range(150):
            reg,_,_=check(expression(3,p),p)
            tested+=1;regular+=reg
    Z=poly([0,1])
    for e in (times(Z,inv(Z)),inv(inv(Z))):
        reg,excluded,_=check(e,5)
        assert reg and excluded==1 and not ev(e,0,5)[1]
    # A formally nonzero inverse input may vanish at every field challenge.
    for p in (2,3,5,17):
        f=[0]*(p+1);f[1]=-1%p;f[p]=1
        reg,excluded,budget=check(inv(poly(f)),p)
        assert reg and excluded==p==budget[2]
    reg,excluded,budget=check(inv(poly([0])),5)
    assert not reg and excluded==5>budget[2]
    # Q=Y^2+(Z+1)Y-X, initial root Y(0)=0, slope Z+1.
    # Construct coefficient expressions independently by the convolution recurrence.
    coefficients=[poly([0])]
    inverse=inv(poly([1,1]))
    for n in range(1,6):
        residual=poly([-1]) if n==1 else poly([0])
        for i in range(1,n):residual=plus(residual,times(coefficients[i],coefficients[n-i]))
        coefficients.append(times(neg(residual),inverse))
    hensel=[]
    for p in (2,3,5,17):
        checks=0;budgets=[]
        for c in coefficients[1:]:
            reg,excluded,budget=check(c,p)
            assert reg and excluded==1
            budgets.append(budget[2])
        for z in range(p):
            if (z+1)%p==0:continue
            actual=lift([[0,-1%p],[(z+1)%p],[1]],0,5,p)
            for n,c in enumerate(coefficients):
                value,safe=ev(c,z,p)
                assert safe and value==actual[n]
                checks+=1
        hensel.append(dict(prime=p,specialized_coefficients=checks,guard_degree_budgets=budgets,actual_excluded_challenges=1))
    print(json.dumps(dict(random_expressions=tested,regular_expressions=regular,
        cancelled_pole_examples=2,nowhere_defined_regular_examples=4,nonregular_counterexamples=1,
        hensel_fixtures=hensel,
        scope='Guarded rational-expression specialization and syntactic pole bounds. Hensel-to-circuit correspondence is tested here, not Lean-proved; no algebraic extension or full MCA exception bound.'),indent=2))


if __name__=='__main__':main()
