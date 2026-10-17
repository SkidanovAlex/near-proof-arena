"""Construct selected root fields and lift full sources over those fields."""
import itertools
import json
import random
from test_bezout_smoothness import divide, derivative, egcd, sub
from test_bivariate_multiplicity import add, mul, trim
from test_polynomial_bezout_existence import irreducible


def main():
    rng = random.Random(4593)
    fields = roots = lifted = new_roots = 0
    for prime, maxdegree in ((2, 3), (3, 3), (5, 2)):
        for d in range(1, maxdegree+1):
            for cs in itertools.product(range(prime), repeat=d):
                h = list(cs)+[1]
                if not irreducible(h, prime):
                    continue
                fields += 1
                def reduce(a): return divide(a, h, prime)[1]
                def plus(a, b): return reduce(add(a, b, prime))
                def times(a, b): return reduce(mul(a, b, prime))
                def neg(a): return reduce(sub([], a, prime))
                def inv(a):
                    assert a
                    gcd, u, _ = egcd(a, h, prime)
                    assert gcd == [1]
                    return reduce(u)
                def scalar(c): return trim([c % prime])
                def evaluate(p, a):
                    value = []
                    for c in reversed(p): value = plus(scalar(c), times(a, value))
                    return value
                a = reduce([0, 1])
                assert not evaluate(h, a)
                new_roots += d > 1
                for _ in range(8):
                    g = [rng.randrange(prime) for _ in range(rng.randrange(4))]+[1]
                    source = mul(h, g, prime)
                    gcd, S, T = egcd(source, derivative(source, prime), prime)
                    if gcd != [1]: continue
                    assert len(h) <= len(source) and len(g) <= len(source)
                    assert not evaluate(source, a) and evaluate(g, a)
                    slope = evaluate(derivative(source, prime), a)
                    assert slope
                    U = add(mul(S, g, prime), mul(T, derivative(g, prime), prime), prime)
                    V = mul(T, derivative(h, prime), prime)
                    assert trim(add(mul(U, h, prime), mul(V, g, prime), prime)) == [1]
                    roots += 1
                    precision = 5
                    rows = [[scalar(c), scalar(rng.randrange(prime)), scalar(rng.randrange(prime))] for c in source]
                    def series_add(p, q):
                        return [plus(p[i] if i < len(p) else [], q[i] if i < len(q) else []) for i in range(max(len(p), len(q)))]
                    def series_mul(p, q):
                        result = [[] for _ in range(min(precision+1, len(p)+len(q)-1))]
                        for i, x in enumerate(p):
                            for j, y in enumerate(q):
                                if i+j < len(result): result[i+j] = plus(result[i+j], times(x, y))
                        return result
                    def residual(f):
                        result = []
                        for row in reversed(rows): result = series_add(row, series_mul(f, result))
                        return result
                    f = [a]
                    for n in range(1, precision+1):
                        before = residual(f)
                        assert all(not c for c in before[:n])
                        correction = neg(times(before[n] if n < len(before) else [], inv(slope)))
                        f.append(correction)
                        assert f[0] == a and len(f) == n+1
                        assert all(not c for c in residual(f)[:n+1])
                        lifted += 1
    assert new_roots and roots and lifted
    print(json.dumps(dict(constructed_selected_fields=fields, nonbase_field_roots=new_roots,
        smooth_full_source_roots=roots, extension_field_hensel_steps=lifted,
        scope='Selected-factor existence/certificates with inherited algebraic degree and constructed smooth-root field/Hensel lifting. Parameter-degree control, extension specialization and useful-branch coverage remain open.'), indent=2))


if __name__ == '__main__':
    main()
