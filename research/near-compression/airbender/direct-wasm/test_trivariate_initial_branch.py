"""Derive initial residual and slope from dense trivariate coefficient data."""
import json
import random
from test_bivariate_multiplicity import add,mul,compose
from test_bivariate_curve_division import quotient,equal
from test_hensel_coefficient_step import slope,coeff
from test_hensel_bounded_reconstruction import lift
from test_symbolic_hensel import slift,specialize
from test_rational_specialization import poly
from test_independent_constraint_mixing import evaluate


def derive(rows,a,p):
    initial=[row[0] if row else [] for row in rows]
    return compose(initial,a,p),compose(quotient(initial,a,p),a,p)


def main():
    rng=random.Random(6_0334)
    identities=degree_cases=pole_cases=branches=specializations=0
    for p in (2,3,5,17):
        for _ in range(100):
            w=rng.randrange(3);D=rng.randrange(9)
            a=[rng.randrange(p) for _ in range(w+1)]
            rows=[]
            for j in range(rng.randrange(7)):
                constant=[rng.randrange(p) if i+w*j<D else 0 for i in range(8)]
                rows.append([constant]+[[rng.randrange(p) for _ in range(3)] for _ in range(rng.randrange(3))])
            residual,S=derive(rows,a,p)
            assert not any(S[max(D-w,0):]);degree_cases+=1
            # Independent formal derivative in Y at X=0,Y=a(Z).
            derivative=[];power=[1]
            for j,row in enumerate(rows):
                if j:
                    derivative=add(derivative,[j*c%p for c in mul(row[0],power,p)],p)
                    power=mul(power,a,p)
            assert equal(derivative,S)
            for z in range(p):
                numeric=[[evaluate(c,z,p) for c in row] for row in rows]
                av=evaluate(a,z,p)
                assert evaluate(residual,z,p)==coeff(compose(numeric,[av],p),0)
                assert evaluate(S,z,p)==slope(numeric,[av],p)
                identities+=1
            if any(S):
                assert sum(evaluate(S,z,p)==0 for z in range(p))<=max(D-w-1,0)
                pole_cases+=1
        for _ in range(3):
            A,B,U=[[rng.randrange(p),rng.randrange(p)] for _ in range(3)]
            if not any(add(A,B,p)):B[0]=(B[0]+1)%p
            # Q=(Y-A-UX)*(Y+B), with no hand-supplied slope.
            rows=[[[(-c)%p for c in mul(A,B,p)],[(-c)%p for c in mul(U,B,p)]],
                  [add(B,[-c%p for c in A],p),[-c%p for c in U]],[[1]]]
            residual,S=derive(rows,A,p)
            assert not any(residual) and equal(S,add(A,B,p)) and any(S)
            symbolic=slift([[poly(c) for c in row] for row in rows],poly(A),2)
            for z in range(p):
                if evaluate(S,z,p)==0:continue
                numeric=[[evaluate(c,z,p) for c in row] for row in rows]
                actual=lift(numeric,evaluate(A,z,p),2,p)
                assert equal(specialize(symbolic,S,z,p),actual)
                assert equal(actual,[evaluate(A,z,p),evaluate(U,z,p),0])
                specializations+=1
            branches+=1
    # An initial polynomial root need not have a nonzero slope.
    # Q=(Y-Z)^2 in characteristic2 is a singular branch.
    residual,S=derive([[[0,0,1]],[],[[1]]],[0,1],2)
    assert not any(residual) and not any(S)
    # Being a root at one challenge is not a formal initial-branch identity.
    residual,S=derive([[[0,4]],[[1]]],[0],5)
    assert evaluate(residual,0,5)==0 and any(residual)
    print(json.dumps(dict(initial_residual_and_slope_evaluation_checks=identities,
        weighted_slope_degree_cases=degree_cases,nonzero_slope_pole_counts=pole_cases,
        constructed_initial_branches=branches,matched_lift_specializations=specializations,
        singular_initial_branch_counterexamples=1,sampled_only_initial_root_counterexamples=1,
        scope='Actual dense input residual, slope, degree and polynomial-initial-branch lift. Existence of a common algebraic branch and singular/inseparable factor treatment remain open.'),indent=2))


if __name__=='__main__':main()
