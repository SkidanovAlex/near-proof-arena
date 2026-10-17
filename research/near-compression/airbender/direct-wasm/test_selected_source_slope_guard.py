"""Explicit full-source slope determinant protects dense algebraic lifting."""
import json
import random
from test_polynomial_fractions import make, plus, times, negative, canonical
from test_independent_constraint_mixing import evaluate
from test_hensel_bounded_reconstruction import lift
from test_factor_collision_guard import matrix
from test_polynomial_determinant_degree import determinant
from test_bivariate_multiplicity import add, mul, trim


def main():
    rng = random.Random(4626)
    systems = comparisons = lift_pairs = excluded = certificate_entries = degree_drops = 0
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
            complement_root = rng.randrange(prime)
            complement_den = [(-complement_root*complement_root-b*complement_root) % prime, 1]
            complement_inverse = (make([(b+complement_root) % prime], complement_den), make([1], complement_den))
            assert em((scalar(-complement_root), one), complement_inverse) == eone
            slope_inverse = em(slope_inverse, complement_inverse)
            full_slope = em((scalar(b), scalar(2)), (scalar(-complement_root), one))
            assert em(full_slope, slope_inverse) == eone
            precision = 4
            # Full initial source is (Y^2+bY-Z)*(Y-c), with selected modulus h.
            rows = [[(rm(scalar(complement_root), Z), zero)], [(ra(rn(Z), scalar(-b*complement_root)), zero)],
                    [(scalar(b-complement_root), zero)], [eone]]
            initial = [[0, complement_root],
                       [-b*complement_root % prime, prime-1], [(b-complement_root) % prime], [1]]
            derivative = [trim([(i+1)*v % prime for v in initial[i+1]]) for i in range(3)]
            while derivative and not derivative[-1]: derivative.pop()
            derivative_degree = len(derivative)-1
            degree_drops += derivative_degree < 2
            hcoeff = [[0, prime-1], [b], [1]]
            M = matrix(hcoeff, derivative, 2, derivative_degree)
            guard = determinant(M, prime)
            assert guard and len(guard) <= derivative_degree+2+1
            numerators = []
            for r in range(derivative_degree+2):
                changed = [row[:] for row in M]
                changed[r] = [[1]]+[[] for _ in range(derivative_degree+1)]
                numerators.append(determinant(changed, prime))
            for i in range(derivative_degree+2):
                actual = []
                for j in range(derivative_degree+2): actual = add(actual, mul(numerators[j], M[j][i], prime), prime)
                assert trim(actual) == (guard if i == 0 else [])
                certificate_entries += 1
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
                if not evaluate(guard, z, prime):
                    excluded += 1
                    continue
                def rv(r):
                    denominator = evaluate(r[1], z, prime)
                    assert denominator
                    return evaluate(r[0], z, prime)*pow(denominator, -1, prime) % prime
                for a in range(prime):
                    if (a*a+b*a-z) % prime: continue
                    assert (a-complement_root) % prime != 0
                    assert evaluate(disc, z, prime) and evaluate(complement_den, z, prime)
                    inverse_coefficients = [evaluate(v, z, prime)*pow(evaluate(guard, z, prime), -1, prime) % prime for v in numerators[derivative_degree:]]
                    actual_slope = (2*a+b)*(a-complement_root) % prime
                    assert evaluate(inverse_coefficients, a, prime) == pow(actual_slope, -1, prime)
                    numeric_rows = [[rv(row[0][0])]+extra for row, extra in zip(rows, extras)]
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
        excluded_full_source_guard_points=excluded,
        full_source_certificate_coefficients=certificate_entries, characteristic_derivative_degree_drops=degree_drops,
        scope='Single full-source slope guard constructs the modular certificate and protects all finite lift coefficients, with inherited source/factor parameter degree inputs. General parameter-degree factor control and useful-branch forcing remain open.'), indent=2))


if __name__ == '__main__':
    main()
