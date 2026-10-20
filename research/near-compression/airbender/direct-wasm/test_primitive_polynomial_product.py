"""Gauss primitive product: coefficient tests and residue-field reductions."""
import itertools
import json
import random
from test_bivariate_multiplicity import add, mul, trim
from test_bezout_smoothness import divide
from test_polynomial_content_normalization import content
from test_polynomial_bezout_existence import irreducible
from test_independent_constraint_mixing import evaluate


def product(a, b, prime):
    out = [[] for _ in range(max(len(a)+len(b)-1, 0))]
    for i, row in enumerate(a):
        for j, other in enumerate(b):
            out[i+j] = trim(add(out[i+j], mul(row, other, prime), prime))
    return out


def primitive(rows, prime):
    g = content(rows, prime)
    assert g
    return [divide(row, g, prime)[0] for row in rows]


def main():
    rng = random.Random(4647)
    products = reductions = evaluations = rejected = 0
    for prime in (2, 3, 5, 17):
        moduli = []
        for degree in (1, 2):
            for cs in itertools.product(range(prime), repeat=degree):
                h = list(cs)+[1]
                if irreducible(h, prime): moduli.append(h)
        for _ in range(100):
            def family():
                rows = [[rng.randrange(prime) for _ in range(rng.randrange(6))]
                        for _ in range(rng.randrange(1, 7))]
                if not any(any(row) for row in rows): rows[0] = [1]
                return primitive(rows, prime)+[[], [0, 0]]
            a, b = family(), family()
            ab = product(a, b, prime)
            assert content(ab, prime) == [1]
            products += 1
            for h in moduli:
                reduced = lambda rows: [divide(row, h, prime)[1] for row in rows]
                ar, br = reduced(a), reduced(b)
                abr = reduced(ab)
                assert any(ar) and any(br) and any(abr)
                assert abr == reduced(product(ar, br, prime))
                reductions += 1
            for z in range(prime):
                av = [evaluate(row, z, prime) for row in a]
                bv = [evaluate(row, z, prime) for row in b]
                abv = [evaluate(row, z, prime) for row in ab]
                assert trim(abv) == trim(mul(av, bv, prime))
                evaluations += 1
            # Omitting primitiveness of either factor invalidates the conclusion.
            h = [rng.randrange(prime), 1]
            for left, right in (([mul(row, h, prime) for row in a], b),
                                (a, [mul(row, h, prime) for row in b])):
                assert len(content(product(left, right, prime), prime)) > 1
                rejected += 1
        # A reducible residue modulus is not a domain: Z*(Z-1) = 0 modulo h.
        h = [0, prime-1, 1]
        assert divide([0, 1], h, prime)[1] and divide([prime-1, 1], h, prime)[1]
        assert not divide(mul([0, 1], [prime-1, 1], prime), h, prime)[1]
        # Zero as a function on F_p does not mean zero as a formal polynomial.
        vanishing = [0, prime-1]+[0]*(prime-2)+[1]
        assert trim(vanishing) and all(evaluate(vanishing, z, prime) == 0 for z in range(prime))
        assert content([vanishing], prime) != [1]
    # Exhaustive small bivariate factors, beyond random normalization examples.
    exhaustive = 0
    for prime in (2, 3):
        families = [list(map(list, (cs[:2], cs[2:])))
                    for cs in itertools.product(range(prime), repeat=4)]
        families = [rows for rows in families if content(rows, prime) == [1]]
        for a in families:
            for b in families:
                assert content(product(a, b, prime), prime) == [1]
                exhaustive += 1
    print(json.dumps(dict(random_primitive_products=products,
        exhaustive_primitive_products=exhaustive, residue_reduction_checks=reductions,
        parameter_specialization_checks=evaluations, nonprimitive_factor_negatives=rejected,
        reducible_modulus_negatives=4, finite_function_zero_negatives=4,
        scope='Primitive-product Gauss lemma and exact dense product transport. Rational scalar descent, source-degree inheritance, full MCA and PQ128 remain open.'), indent=2))


if __name__ == '__main__':
    main()
