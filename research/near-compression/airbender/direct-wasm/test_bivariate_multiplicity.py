"""Coefficient-level substitution checks; random tests do not prove translation."""
import json
import math
import random


def add(a,b,p):
    return [((a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0))%p
            for i in range(max(len(a),len(b)))]


def mul(a,b,p):
    if not a or not b:return []
    out=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):out[i+j]=(out[i+j]+x*y)%p
    return out


def trim(a):
    a=a[:]
    while a and a[-1]==0:a.pop()
    return a


def shift(a,z,p):
    return [sum(a[j]*math.comb(j,i)*pow(z,j-i,p) for j in range(i,len(a)))%p
            for i in range(len(a))]


def compose(rows,curve,p):
    out=[]
    for row in reversed(rows):out=add(row,mul(curve,out,p),p)
    return out


def direct(rows,curve,p):
    out=[]
    power=[1]
    for row in rows:
        for i,c in enumerate(row):out=add(out,[0]*i+[(c*x)%p for x in power],p)
        power=mul(power,curve,p)
    return out


def bivariate_shift(rows,a,b,p):
    # Q(X+a,Y+b), computed via two independent binomial expansions.
    out=[[] for _ in rows]
    for j,row in enumerate(rows):
        translated=shift(row,a,p)
        for k in range(j+1):
            factor=math.comb(j,k)*pow(b,j-k,p)%p
            out[k]=add(out[k],[factor*x%p for x in translated],p)
    return out


def main():
    rng=random.Random(73962798)
    cases=translations=0
    for p in (2,3,5,7):
        for _ in range(250):
            m=rng.randrange(7)
            rows=[[rng.randrange(p) if i+j>=m else 0 for i in range(rng.randrange(6))]
                  for j in range(rng.randrange(6))]
            curve=[0]+[rng.randrange(p) for _ in range(rng.randrange(5))]
            out=compose(rows,curve,p)
            assert trim(out)==trim(direct(rows,curve,p))
            assert not any(out[:m])
            # Numerical evidence for the still-unformalized translation bridge.
            a,b=rng.randrange(p),rng.randrange(p)
            original=bivariate_shift(rows,-a,-b,p)
            original_curve=add([b],shift(curve,-a,p),p)
            translated=shift(compose(original,original_curve,p),a,p)
            assert trim(translated)==trim(out)
            translations+=1
            cases+=1
        # The through-origin premise is necessary: Q=Y has order 1,
        # but substitution Y=1 has order 0.
        assert compose([[],[1]],[1],p)==[1]
        # Pure-axis coefficients miss the mixed XY coefficient of order 2.
        assert trim(compose([[],[0,1]],[0,1],p))==[0,0,1]
    print(json.dumps(dict(centered_substitutions=cases,
        computational_arbitrary_center_checks=translations,
        negative_premises=['curve passes through center','all mixed coefficients below total order vanish'],
        scope='Lean proves centered substitution only. Arbitrary-center tests are evidence, not a formal translation theorem. GS existence and MCA remain open.'),indent=2))


if __name__ == '__main__':
    main()
