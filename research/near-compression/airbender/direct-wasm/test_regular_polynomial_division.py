"""Regular rational-function long division versus numeric specialization."""
import json
import random
from test_polynomial_fractions import make, plus, times, negative, inverse, canonical, equiv
from test_bezout_smoothness import divide
from test_independent_constraint_mixing import evaluate


def main():
    rng = random.Random(4599)
    cases = exact = safe_coefficients = constants = 0
    for prime in (2, 3, 5, 17):
        zero, one = make([], [1]), make([1], [1])
        def norm(a):
            n, d = canonical(a, prime)
            return list(n), list(d)
        def add(a, b): return norm(plus(a, b, prime))
        def mul(a, b): return norm(times(a, b, prime))
        def neg(a): return norm(negative(a, prime))
        def trim(p):
            p = p[:]
            while p and not p[-1][0]: p.pop()
            return p
        def product(p, q):
            result = [zero for _ in range(max(0, len(p)+len(q)-1))]
            for i, a in enumerate(p):
                for j, b in enumerate(q): result[i+j] = add(result[i+j], mul(a, b))
            return trim(result)
        def division(p, q):
            r, q = trim(p), trim(q)
            t = [zero for _ in range(max(0, len(r)-len(q)+1))]
            while r and len(r) >= len(q):
                k = len(r)-len(q)
                c = mul(r[-1], inverse(q[-1]))
                t[k] = add(t[k], c)
                for j, b in enumerate(q): r[k+j] = add(r[k+j], neg(mul(c, b)))
                r = trim(r)
            return trim(t), r
        for index in range(55):
            z = rng.randrange(prime)
            def coeff(nonzero=False):
                while True:
                    a = norm(make([rng.randrange(prime), rng.randrange(prime)], [1, rng.randrange(prime)]))
                    if evaluate(a[1], z, prime) and (not nonzero or evaluate(a[0], z, prime)):
                        return a
            def value(a):
                den = evaluate(a[1], z, prime)
                assert den
                return evaluate(a[0], z, prime)*pow(den, -1, prime) % prime
            d = rng.randrange(3)
            q = [coeff() for _ in range(d)]+[coeff(True)]
            p = [coeff() for _ in range(rng.randrange(5))]
            if index % 2 == 0:
                p = product([coeff() for _ in range(rng.randrange(4))], q)
            t, r = division(p+[zero, zero], q+[zero])
            numeric_t, numeric_r = divide([value(a) for a in p], [value(a) for a in q], prime)
            def scalar_trim(a):
                while a and a[-1] == 0: a.pop()
                return a
            assert scalar_trim([value(a) for a in t]) == numeric_t
            assert scalar_trim([value(a) for a in r]) == numeric_r
            recovered = product(t, q)
            recovered += [zero]*max(0, len(r)-len(recovered))
            for i, a in enumerate(r): recovered[i] = add(recovered[i], a)
            recovered = trim(recovered)
            assert len(recovered) == len(trim(p)) and all(equiv(a, b, prime) for a, b in zip(recovered, trim(p)))
            if index % 2 == 0:
                assert not r
                exact += 1
            safe_coefficients += len(t)+len(r)
            constants += d == 0
            cases += 1
        # Degree drop at specialization can force a quotient pole.
        t, r = division([zero, one], [zero, make([0, 1], [1])])
        assert not r and equiv(t[0], make([1], [0, 1]), prime)
        assert evaluate(t[0][1], 0, prime) == 0
    print(json.dumps(dict(regular_divisions=cases, exact_divisions=exact,
        safe_output_coefficients=safe_coefficients, constant_divisors=constants,
        vanishing_leading_coefficient_pole_examples=4,
        scope='Long division and exact quotient preserve coefficient regularity when the specialized leading coefficient is nonzero. Representative-independent extension specialization and full MCA remain open.'), indent=2))


if __name__ == '__main__':
    main()
