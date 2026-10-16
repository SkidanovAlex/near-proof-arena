"""Actual quadratic algebraic lifts compared coefficientwise with numeric lifts."""
import json
import random
from test_polynomial_fractions import make, plus, times, negative, canonical
from test_independent_constraint_mixing import evaluate
from test_hensel_bounded_reconstruction import lift


def main():
    rng = random.Random(4613)
    systems = comparisons = lift_pairs = excluded = 0
    for prime in (2, 3, 5, 17):
        def norm(r):
            n, d = canonical(r, prime)
            return list(n), list(d)
        def ra(x, y): return norm(plus(x, y, prime))
        def rm(x, y): return norm(times(x, y, prime))
        def rn(x): return norm(negative(x, prime))
        def scalar(c): return make([c % prime], [1])
        zero, one, Z = scalar(0), scalar(1), make([0, 1], [1])
        ezero, eone, alpha = (zero, zero), (one, zero), (zero, one)
        for _ in range(9):
            b = 1 if prime == 2 else rng.randrange(prime)
            # alpha^2+b*alpha-Z=0 over F_p(Z).
            def ea(x, y): return ra(x[0], y[0]), ra(x[1], y[1])
            def en(x): return rn(x[0]), rn(x[1])
            def em(x, y):
                cross = rm(x[1], y[1])
                return ra(rm(x[0], y[0]), rm(Z, cross)), ra(ra(rm(x[0], y[1]), rm(x[1], y[0])), rn(rm(scalar(b), cross)))
            disc = [b*b % prime, 4 % prime]
            slope_inverse = (make([b], disc), make([2 % prime], disc))
            assert em((scalar(b), scalar(2)), slope_inverse) == eone
            precision = 4
            rows = [[(rn(Z), zero)], [(scalar(b), zero)], [eone]]
            extras = [[rng.randrange(prime) for _ in range(2)] for _ in rows]
            rows = [row+[(scalar(c), zero) for c in extra] for row, extra in zip(rows, extras)]
            def sa(p, q): return [ea(p[i] if i < len(p) else ezero, q[i] if i < len(q) else ezero) for i in range(max(len(p), len(q)))]
            def sm(p, q):
                out = [ezero for _ in range(min(precision+1, max(0, len(p)+len(q)-1)))]
                for i, x in enumerate(p):
                    for j, y in enumerate(q):
                        if i+j < len(out): out[i+j] = ea(out[i+j], em(x, y))
                return out
            def residual(f):
                out = []
                for row in reversed(rows): out = sa(row, sm(f, out))
                return out
            f = [alpha]
            stages = [f[:]]
            for n in range(1, precision+1):
                result = residual(f)
                assert all(c == ezero for c in result[:n])
                f.append(en(em(result[n] if n < len(result) else ezero, slope_inverse)))
                assert all(c == ezero for c in residual(f)[:n+1])
                stages.append(f[:])
            for z in range(prime):
                if not evaluate(disc, z, prime):
                    excluded += 1
                    continue
                def rv(r):
                    denominator = evaluate(r[1], z, prime)
                    assert denominator
                    return evaluate(r[0], z, prime)*pow(denominator, -1, prime) % prime
                for a in range(prime):
                    if (a*a+b*a-z) % prime: continue
                    numeric_rows = [[-z % prime]+extras[0], [b]+extras[1], [1]+extras[2]]
                    for n, stage in enumerate(stages):
                        numeric = lift(numeric_rows, a, n, prime)
                        for i, c in enumerate(stage):
                            assert (rv(c[0])+a*rv(c[1])) % prime == (numeric[i] if i < len(numeric) else 0)
                            comparisons += 1
                        lift_pairs += 1
            systems += 1
    assert comparisons and excluded
    print(json.dumps(dict(rational_algebraic_source_systems=systems,
        algebraic_numeric_lift_pairs=lift_pairs, coefficient_specialization_comparisons=comparisons,
        excluded_derivative_guard_points=excluded,
        scope='Coefficientwise specialization of the actual finite Hensel recurrence, instantiated by partial algebraic residue specialization with one initial inverse guard. Source-interface discharge and MCA remain open.'), indent=2))


if __name__ == '__main__':
    main()
