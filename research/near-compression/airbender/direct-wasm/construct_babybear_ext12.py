"""Construct and independently check candidate F_p[X]/(X^12-31).
Requires sympy==1.14.0. Computational evidence, not a Lean irreducibility proof.
"""
from pathlib import Path
import json, random
import sympy as sp
from sympy.polys.galoistools import gf_irreducible_p
from sympy.polys.domains import ZZ
P=2013265921
D=12
ROOT=Path(__file__).resolve().parents[2]
OUT=ROOT/'results/babybear-ext12-construction'
ONE=[1]+[0]*11

def mul(a,b):
    c=[0]*23
    for i,x in enumerate(a):
        for j,y in enumerate(b):c[i+j]+=x*y
    for i in range(22,11,-1):c[i-12]+=31*c[i]
    return [x%P for x in c[:12]]

def power(a,n):
    out=ONE
    while n:
        if n&1:out=mul(out,a)
        a=mul(a,a);n//=2
    return out

def main():
    assert sp.isprime(P)
    # SymPy's polynomial irreducibility algorithm is independent of our
    # coefficient convolution implementation and binomial criterion.
    assert gf_irreducible_p([1]+[0]*11+[-31%P],P,ZZ)
    factors={}
    for d in (1,2,3,4,6,12):
        for q,e in sp.factorint(int(sp.Poly(sp.cyclotomic_poly(d)).eval(P))).items():
            factors[int(q)]=factors.get(int(q),0)+int(e)
    order=P**12-1
    assert sp.prod(q**e for q,e in factors.items())==order
    assert all(sp.isprime(q) for q in factors)
    for k in range(1,256):
        g=[k,1]+[0]*10
        if power(g,order)==ONE and all(power(g,order//q)!=ONE for q in factors):break
    else:raise AssertionError('no generator found')
    x=[0,1]+[0]*10
    roots=[power(x,90),power(x,45)]
    assert power(roots[0],2)==[pow(31,15,P)]+[0]*11
    assert power(roots[1],2)==roots[0]
    for bits,r in zip((28,29),roots):
        assert power(r,2**bits)==ONE and power(r,2**(bits-1))!=ONE
    frobenius=pow(31,(P-1)//12,P)
    assert power(x,P)==[0,frobenius]+[0]*10
    rng=random.Random(120384)
    vectors=[]
    for _ in range(24):
        a=[rng.randrange(P) for _ in range(12)]
        b=[rng.randrange(P) for _ in range(12)]
        inv=power(a,order-1)
        assert mul(a,inv)==ONE
        vectors.append(dict(a=a,b=b,product=mul(a,b),inverse=inv,frobenius=power(a,P)))
    result=dict(prime=P,degree=12,nonresidue=31,polynomial='X^12-31',
                sympy_version=sp.__version__,irreducibility_check='gf_irreducible_p',
                generator=g,multiplicative_order=str(order),order_factorization=factors,
                dth_root=frobenius,two_adic_roots=roots,vectors=vectors,
                lean_irreducibility_proved=False,security_certified=False)
    OUT.mkdir(exist_ok=True)
    (OUT/'construction.json').write_text(json.dumps(result,indent=2)+'\n')
    print('irreducible degree12; generator=',g,'DTH_ROOT=',frobenius,'roots=',roots)

if __name__=='__main__':main()
