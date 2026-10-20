"""Finite Hensel lifting with exhaustive next-coefficient checks."""
import json
import random
from test_bivariate_multiplicity import add,mul,compose
from test_bivariate_curve_division import quotient,equal


def coeff(f,i):return f[i] if i<len(f) else 0
def slope(rows,f,p):return coeff(compose(quotient(rows,f,p),f,p),0)
def perturb(f,n,c,p):return add(f,[0]*n+[c],p)
def order(f,n):return not any(f[:n])


def main():
    rng=random.Random(37_660)
    smooth_cases=singular_cases=steps=coefficient_checks=modulo_checks=0
    for p in (2,3,5,17):
        for _ in range(150):
            rows=[[rng.randrange(p) for _ in range(rng.randrange(1,6))] for _ in range(rng.randrange(2,6))]
            a=rng.randrange(p)
            # Impose the initial root without choosing the slope.
            rows[0][0]=(rows[0][0]-coeff(compose(rows,[a],p),0))%p
            assert coeff(compose(rows,[a],p),0)==0
            initial=slope(rows,[a],p)
            derivative=sum(j*coeff(row,0)*pow(a,j-1,p) for j,row in enumerate(rows) if j)%p
            assert initial==derivative
            if initial==0:
                singular_cases+=1
                continue
            smooth_cases+=1
            f=[a]
            for n in range(1,8):
                residual=compose(rows,f,p)
                assert order(residual,n) and slope(rows,f,p)==initial
                c=-coeff(residual,n)*pow(initial,-1,p)%p
                choices=[]
                for d in range(p):
                    g=perturb(f,n,d,p)
                    rg=compose(rows,g,p)
                    assert order(add(rg,[-x%p for x in residual],p),n)
                    assert coeff(rg,n)==(coeff(residual,n)+d*initial)%p
                    coefficient_checks+=1
                    if order(rg,n+1):choices.append(d)
                assert choices==[c]
                f=perturb(f,n,c,p)
                assert len(f)<=n+1 and f[0]==a and order(compose(rows,f,p),n+1)
                assert slope(rows,f,p)==initial
                steps+=1
                # Arbitrary higher coefficients do not affect uniqueness modulo X^(n+1).
                g=add(f,[0]*(n+1)+[rng.randrange(p) for _ in range(3)],p)
                assert order(compose(rows,g,p),n+1)
                assert order(add(g,[-x%p for x in f],p),n+1)
                modulo_checks+=1
    # Singular initial root may have no next coefficient: Y^2-X over F2.
    impossible=[[0,1],[],[1]]
    assert slope(impossible,[0],2)==0
    assert not any(order(compose(impossible,[0,c],2),2) for c in range(2))
    # Or it may have multiple: Y^2 over F2, modulo X^2.
    ambiguous=[[],[],[1]]
    assert slope(ambiguous,[0],2)==0
    assert all(order(compose(ambiguous,[0,c],2),2) for c in range(2))
    # Finite precision is not exact polynomial-root existence: Y-X-Y^2.
    rows=[[0,4],[1],[4]];f=[0]
    for n in range(1,9):
        residual=compose(rows,f,5)
        f=perturb(f,n,-coeff(residual,n)*pow(slope(rows,f,5),-1,5)%5,5)
    residual=compose(rows,f,5)
    assert order(residual,9) and any(residual)
    print(json.dumps(dict(smooth_initial_roots=smooth_cases,singular_initial_roots=singular_cases,
        lift_steps=steps,exhaustive_coefficient_checks=coefficient_checks,modulo_preservation_checks=modulo_checks,
        singular_no_lift_examples=1,singular_nonunique_examples=1,approximate_not_exact_examples=1,
        scope='Finite smooth Hensel existence and uniqueness over any field. No rational-function extension construction, useful-factor selection, bounded-degree exactness or full MCA exceptions.'),indent=2))


if __name__=='__main__':main()
