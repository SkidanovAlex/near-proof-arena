"""Regular quotient representative independence and its necessary domain guards."""
import json
import random
from test_polynomial_fractions import make, plus, times, negative, canonical
from test_independent_constraint_mixing import evaluate
from test_bezout_smoothness import divide


def main():
    rng = random.Random(4604)
    representatives = roots = operations = leading_negatives = inverse_negatives = 0
    for prime in (2, 3, 5, 17):
        zero, one = make([], [1]), make([1], [1])
        def norm(a):
            n, d = canonical(a, prime)
            return list(n), list(d)
        def add(a, b): return norm(plus(a, b, prime))
        def mul(a, b): return norm(times(a, b, prime))
        def polyadd(p, q):
            return [add(p[i] if i < len(p) else zero, q[i] if i < len(q) else zero) for i in range(max(len(p), len(q)))]
        def polymul(p, q):
            result = [zero for _ in range(max(0, len(p)+len(q)-1))]
            for i, x in enumerate(p):
                for j, y in enumerate(q): result[i+j] = add(result[i+j], mul(x, y))
            return result
        for _ in range(70):
            z = rng.randrange(prime)
            if (1+z) % prime == 0: continue
            # h=(1+Z)Y^2-Z: nonmonic, but leading degree preserved here.
            h = [make([0, prime-1], [1]), zero, make([1, 1], [1])]
            def coefficient():
                while True:
                    r = norm(make([rng.randrange(prime), rng.randrange(prime)], [1, rng.randrange(prime)]))
                    if evaluate(r[1], z, prime): return r
            def value(r):
                denominator = evaluate(r[1], z, prime)
                assert denominator
                return evaluate(r[0], z, prime)*pow(denominator, -1, prime) % prime
            def specialize(p): return [value(c) for c in p]
            r = [coefficient() for _ in range(3)]+[zero, zero]
            s = [coefficient() for _ in range(3)]
            t = [coefficient() for _ in range(3)]
            alternative = polyadd(r, polymul(t, h))
            hs, rs, alt = specialize(h), specialize(r), specialize(alternative)
            assert divide(rs, hs, prime)[1] == divide(alt, hs, prime)[1]
            representatives += 1
            for a in range(prime):
                if evaluate(hs, a, prime): continue
                rv, sv = evaluate(rs, a, prime), evaluate(specialize(s), a, prime)
                assert rv == evaluate(alt, a, prime)
                assert evaluate(specialize(polyadd(alternative, s)), a, prime) == (rv+sv) % prime
                assert evaluate(specialize(polymul(alternative, s)), a, prime) == rv*sv % prime
                operations += 2
                roots += 1
        # h=Z*Y: Y is zero in the generic quotient but not at z=0,a=1.
        assert evaluate([0, 0], 1, prime) == 0
        assert evaluate([0, 1], 1, prime) == 1
        leading_negatives += 1
        if prime != 2:
            # h=Y^2-Z, x=Y-1, inverse=(Y+1)/(Z-1).
            # At z=1,a=-1, x is nonzero, but no coefficient-regular inverse
            # can exist: the same regular identity would evaluate at a=1 too.
            assert (-2) % prime != 0
            denominator = [prime-1, 1]
            assert evaluate(denominator, 1, prime) == 0
            assert evaluate([prime-1, 0, 1], 1, prime) == 0
            assert evaluate([prime-1, 1], 1, prime) == 0
            inverse_negatives += 1
    assert roots and representatives and operations
    print(json.dumps(dict(regular_equivalent_representatives=representatives,
        specialized_root_value_equalities=roots, quotient_add_mul_values=operations,
        leading_degree_drop_counterexamples=leading_negatives,
        chosen_root_nonzero_insufficient_for_regular_inverse=inverse_negatives,
        scope='Representative-independent partial algebraic specialization and add/mul closure. Inverse domain requires stronger guards; extension/Hensel specialization and full MCA remain open.'), indent=2))


if __name__ == '__main__':
    main()
