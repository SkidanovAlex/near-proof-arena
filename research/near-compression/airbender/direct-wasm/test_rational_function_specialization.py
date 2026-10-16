"""Connect guarded expressions, formal fractions and partial specialization."""
import json
import random
from test_rational_specialization import poly, times, inv, analyze, ev
from test_independent_constraint_mixing import evaluate
from test_polynomial_fractions import make, equiv, canonical, plus, times as ftimes, inverse


def main():
    rng = random.Random(88309)
    def expression(depth, p):
        if depth == 0 or rng.randrange(4) == 0:
            return poly([rng.randrange(p) for _ in range(rng.randrange(4))])
        op = rng.choice(('neg', 'inv', 'add', 'mul'))
        a = expression(depth-1, p)
        return (op, a) if op in ('neg', 'inv') else (op, a, expression(depth-1, p))
    regular = bridge_checks = identity_checks = disagreements = reciprocal_checks = arithmetic_checks = 0
    for p in (2, 3, 5, 17):
        def value(a, z):
            n, d = evaluate(a[0], z, p), evaluate(a[1], z, p)
            return None if d == 0 else n*pow(d, -1, p) % p
        for _ in range(150):
            e = expression(3, p)
            en, ed, _, eb, er = analyze(e, p)
            if not er: continue
            regular += 1
            a = make(en, ed)
            c = rng.randrange(p)
            linear = poly([(-c) % p, 1])
            f = times(e, times(linear, inv(linear)))
            fn, fd, _, fb, fr = analyze(f, p)
            assert fr
            b = make(fn, fd)
            assert equiv(a, b, p) and canonical(a, p) == canonical(b, p)
            bad = 0
            for z in range(p):
                ve, se = ev(e, z, p)
                vf, sf = ev(f, z, p)
                if se:
                    assert value(a, z) == ve
                    bridge_checks += 1
                if se and sf:
                    assert ve == vf == value(b, z)
                    identity_checks += 1
                if ve != vf:
                    assert not (se and sf)
                    bad += 1
                va, vb = value(a, z), value(b, z)
                if va is not None and vb is not None:
                    assert va == vb
                    assert value(plus(a, b, p), z) == (va+vb) % p
                    assert value(ftimes(a, b, p), z) == va*vb % p
                    arithmetic_checks += 1
                if va is not None and va != 0:
                    assert value(inverse(a), z) == pow(va, -1, p)
                    reciprocal_checks += 1
            assert bad <= eb[2]+fb[2]
            disagreements += bad
    # Cancellation can enlarge the intrinsic rational-function domain while the
    # original expression stays unsafe. A total evaluator would give the wrong value.
    Z = poly([0, 1])
    cancelled = times(Z, inv(Z))
    n, d, _, _, reg = analyze(cancelled, 5)
    assert reg and equiv(make(n, d), make([1], [1]), 5)
    assert ev(cancelled, 0, 5) == (0, False)
    # Nonzero rational Z specializes to zero; reciprocal specialization at zero is invalid.
    assert ev(Z, 0, 5) == (0, True) and ev(inv(Z), 0, 5) == (0, False)
    print(json.dumps(dict(regular_expressions=regular, guarded_function_bridge_checks=bridge_checks,
        safe_identity_checks=identity_checks, pole_only_disagreements=disagreements,
        safe_arithmetic_checks=arithmetic_checks, safe_reciprocal_checks=reciprocal_checks,
        cancellation_domain_negatives=1, reciprocal_zero_value_negatives=1,
        scope='Unique partial specialization, guarded-expression bridge and syntactic-pole identity exception bound; full algebraic branch/MCA exception bounds remain open.'), indent=2))


if __name__ == '__main__': main()
