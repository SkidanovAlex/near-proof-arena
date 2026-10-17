"""Field completion and actual root construction regressions."""
import itertools
import json
import random
from test_bezout_smoothness import divide, derivative, egcd, sub
from test_bivariate_multiplicity import add, mul, trim
from test_polynomial_bezout_existence import irreducible


def main():
    rng = random.Random(40331)
    moduli = additive_triples = root_checks = smooth_roots = eval_checks = cast_checks = 0
    witnesses = []
    for p, maxd in ((2, 3), (3, 3), (5, 2)):
        for d in range(1, maxd+1):
            for cs in itertools.product(range(p), repeat=d):
                h = list(cs)+[1]
                if not irreducible(h, p):
                    continue
                moduli += 1
                def reduce(a): return divide(a, h, p)[1]
                def plus(a, b): return reduce(add(a, b, p))
                def times(a, b): return reduce(mul(a, b, p))
                def neg(a): return reduce(sub([], a, p))
                def scalar(c): return trim([c % p])
                def inverse(a):
                    if not a: return []
                    g, A, _ = egcd(a, h, p)
                    assert g == [1]
                    return reduce(A)
                def evaluate(poly, x):
                    result = []
                    for c in reversed(poly):
                        result = plus(scalar(c), times(x, result))
                    return result
                assert len({tuple(scalar(c)) for c in range(p)}) == p
                residues = [trim(list(a)) for a in itertools.product(range(p), repeat=d)]
                assert inverse([]) == [] and scalar(1) != []
                for a in residues:
                    assert plus(a, []) == a and plus(neg(a), a) == []
                    assert times(a, scalar(1)) == a and times([], a) == []
                    if a: assert times(a, inverse(a)) == [1]
                    for n in range(-7, 8):
                        assert scalar(-n) == neg(scalar(n))
                        assert times(scalar(-n), a) == neg(times(scalar(n), a))
                        assert scalar(n+1) == plus(scalar(n), scalar(1))
                        cast_checks += 1
                    for b in residues:
                        assert plus(a, b) == plus(b, a)
                        for c in residues:
                            assert plus(plus(a, b), c) == plus(a, plus(b, c))
                            additive_triples += 1
                x = reduce([0, 1])
                assert evaluate(h, x) == []
                root_checks += 1
                if d < p:
                    assert evaluate(derivative(h, p), x) != []
                    smooth_roots += 1
                for _ in range(30):
                    poly = [rng.randrange(p) for _ in range(rng.randrange(12))]+[0, 0]
                    assert evaluate(poly, x) == reduce(poly)
                    assert evaluate(mul(poly, h, p), x) == []
                    assert evaluate(mul(h, h, p), x) == []
                    eval_checks += 1
                if d > 1 and len(witnesses) < 4:
                    assert all(evaluate(h, scalar(c)) != [] for c in range(p))
                    witnesses.append(dict(prime=p, modulus=h, root=x,
                        derivative_at_root=evaluate(derivative(h, p), x)))
    print(json.dumps(dict(constructed_root_fields=moduli, additive_associativity_triples=additive_triples,
        cast_and_scalar_checks=cast_checks, modulus_roots=root_checks,
        below_characteristic_smooth_roots=smooth_roots,
        variable_evaluation_checks=eval_checks, composite_root_checks=eval_checks, witnesses=witnesses,
        scope='Lean Field construction, coefficient map, actual modulus root and degree-bounded smoothness. Rational-function field and full MCA/protocol security remain open.'), indent=2))


if __name__ == '__main__': main()
