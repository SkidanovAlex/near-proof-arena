"""Finite coefficient guards, explicit degree budgets, and singular-root containment."""
import json
import random
from test_bivariate_multiplicity import mul, trim
from test_bezout_smoothness import sub
from test_independent_constraint_mixing import evaluate
from test_polynomial_fractions import make, equiv


def main():
    rng = random.Random(44951)
    families = safe_coefficients = certificate_fixtures = singular_points = good_roots = 0
    def guard(cs, p):
        g, budget = [1], 0
        for _, d in cs:
            assert any(d)
            g = mul(g, d, p)
            budget += max(len(d)-1, 0)
        assert trim(g) and len(trim(g))-1 <= budget
        return g, budget
    for p in (2, 3, 5, 17):
        for _ in range(80):
            cs = []
            for _ in range(rng.randrange(9)):
                n = [rng.randrange(p) for _ in range(rng.randrange(5))]
                d = [rng.randrange(p) for _ in range(rng.randrange(1, 5))]
                if not any(d): d[0] = 1
                cs.append((n+[0], d+[0]*rng.randrange(3)))
            g, budget = guard(cs, p)
            excluded = 0
            for z in range(p):
                bad = not evaluate(g, z, p)
                assert bad == any(not evaluate(d, z, p) for _, d in cs)
                excluded += bad
                if not bad:
                    for n, d in cs:
                        dv = evaluate(d, z, p)
                        value = evaluate(n, z, p)*pow(dv, -1, p) % p
                        assert dv*value % p == evaluate(n, z, p)
                        safe_coefficients += 1
            assert excluded <= budget
            families += 1
        if p == 2: continue
        for _ in range(60):
            b, c = [rng.randrange(p) for _ in range(3)], [rng.randrange(p) for _ in range(3)]
            disc = trim(sub(mul(b, b, p), [4*v % p for v in c], p))
            if not disc: continue
            original = [make(c, [1]), make(b, [1]), make([1], [1]),
                        make([-4 % p], disc), make(b, disc), make([2], disc)]
            presented = []
            for n, d in original:
                factor = [rng.randrange(p), 1]
                scaled = (mul(n, factor, p)+[0], mul(d, factor, p)+[0])
                assert equiv(make(n, d), make(*scaled), p)
                presented.append(scaled)
            g, budget = guard(presented, p)
            singular = 0
            for z in range(p):
                safe = evaluate(g, z, p) != 0
                values = [evaluate(n, z, p)*(pow(evaluate(d, z, p), -1, p) if evaluate(d, z, p) else 0) % p
                          for n, d in presented]
                q, A, B = values[:3], values[3], values[4:]
                has_singular = False
                for a in range(p):
                    qv, dv = evaluate(q, a, p), (q[1]+2*q[2]*a) % p
                    if safe: assert (A*qv+evaluate(B, a, p)*dv) % p == 1
                    if qv == 0:
                        if safe:
                            assert dv != 0
                            good_roots += 1
                        if dv == 0:
                            assert not safe
                            has_singular = True
                singular += has_singular
            assert singular <= sum(evaluate(g, z, p) == 0 for z in range(p)) <= budget
            singular_points += singular
            certificate_fixtures += 1
    print(json.dumps(dict(coefficient_families=families, safe_coefficient_evaluations=safe_coefficients,
        certificate_presentations=certificate_fixtures, singular_points_inside_guard=singular_points,
        smooth_roots_outside_guard=good_roots,
        scope='Constructed presentation-dependent denominator guards and singular-point bounds. Bounds from original interpolation dimensions and full MCA remain open.'), indent=2))


if __name__ == '__main__': main()
