"""Check synthetic/Horner translation against binomial expansion and GS roots."""
import json
import random
from test_bivariate_multiplicity import add,mul,trim,compose,bivariate_shift
from test_synthetic_multiplicity import taylor
from test_independent_constraint_mixing import evaluate


def add_rows(a,b,p):
    return [add(a[i] if i<len(a) else [],b[i] if i<len(b) else [],p)
            for i in range(max(len(a),len(b)))]


def translate(rows,a,b,p):
    out=[]
    for row in reversed(rows):
        scaled=[[b*x%p for x in r] for r in out]
        out=add_rows([taylor(row,a,p,len(row))],add_rows(scaled,[[]]+out,p),p)
    return out


def canonical(rows):
    out=[trim(r) for r in rows]
    while out and not out[-1]:out.pop()
    return out


def mixed_order(rows,m):
    return all(c==0 for j,row in enumerate(rows) for i,c in enumerate(row) if i+j<m)


def main():
    rng=random.Random(2142611)
    translations=root_cases=0
    for p in (2,3,5,17,31):
        for _ in range(100):
            rows=[[rng.randrange(p) for _ in range(rng.randrange(5))]
                  for _ in range(rng.randrange(5))]
            a,b=rng.randrange(p),rng.randrange(p)
            actual=translate(rows,a,b,p)
            assert canonical(actual)==canonical(bivariate_shift(rows,a,b,p))
            curve=[rng.randrange(p) for _ in range(rng.randrange(1,4))]
            b=evaluate(curve,a,p)
            central_curve=add(taylor(curve,a,p,len(curve)),[-b%p],p)
            right=compose(translate(rows,a,b,p),central_curve,p)
            original=compose(rows,curve,p)
            left=taylor(original,a,p,len(original))
            assert trim(left)==trim(right)
            translations+=1
    for p in (17,31):
        for _ in range(100):
            curve=[rng.randrange(p) for _ in range(3)]
            # Q=(Y-curve(X))^2, with multiplicity 2 at all graph points.
            rows=[mul(curve,curve,p),[-2*x%p for x in curve],[1]]
            original=compose(rows,curve,p)
            assert not any(original)
            for a in (0,1,2):
                b=evaluate(curve,a,p)
                translated=translate(rows,a,b,p)
                assert mixed_order(translated,2)
                central_curve=add(taylor(curve,a,p,len(curve)),[-b%p],p)
                right=compose(translated,central_curve,p)
                left=taylor(original,a,p,len(original))
                assert max(len(left),len(right))<=p  # exact theorem guard
                assert not any(left[:2]) and not any(right[:2])
            # Degree bound 6 and total multiplicity 3*2 satisfy root forcing.
            assert not any(original[6:])
            root_cases+=1
    # Zero function is not formal zero; insufficient points must not establish
    # coefficient equality of X^p-X and zero.
    p=3
    ghost=[0,p-1,0,1]
    assert all(evaluate(ghost,x,p)==0 for x in range(p)) and any(ghost)
    assert len(ghost)>p
    print(json.dumps(dict(translation_substitution_cases=translations,
        root_forcing_cases_with_separation=root_cases,
        insufficient_sample_counterexample='X^3-X over F3: zero function, nonzero coefficients, degree-separation guard fails',
        scope='Formal theorem retains explicit distinct-domain size and substitution degree bounds. Interpolant existence and MCA remain open.'),indent=2))


if __name__ == '__main__':
    main()
