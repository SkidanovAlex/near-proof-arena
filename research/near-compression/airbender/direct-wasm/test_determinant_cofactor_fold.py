"""Signed selection identities and determinant alternation in all test characteristics."""
import json
import random
from test_polynomial_determinant_degree import numeric_det


def fold(cs, f, p):
    if not cs: return 0
    c, tail = cs[0], cs[1:]
    return (f(c, tail)-fold(tail, lambda d, rest: f(d, [c]+rest), p)) % p


def main():
    rng = random.Random(45231)
    folds = double_swaps = symmetric_zeros = row_swaps = equal_rows = char_two = 0
    for p in (2, 3, 5, 17):
        for _ in range(80):
            cs = [rng.randrange(8) for _ in range(rng.randrange(7))]
            a, b, c = [rng.randrange(p) for _ in range(3)]
            def f(j, rest): return (a*j+b*sum((i+1)*v for i, v in enumerate(rest))+c) % p
            indexed = sum((-1)**j*f(v, cs[:j]+cs[j+1:]) for j, v in enumerate(cs)) % p
            assert fold(cs, f, p) == indexed
            def pair(x, y, rest): return (a*x*y+b*x+c*y+sum((i+1)*v for i, v in enumerate(rest))) % p
            direct = fold(cs, lambda x, rest: fold(rest, lambda y, rem: pair(x, y, rem), p), p)
            swapped = fold(cs, lambda x, rest: fold(rest, lambda y, rem: pair(y, x, rem), p), p)
            assert direct == -swapped % p
            def symmetric(x, y, rest): return (pair(x, y, rest)+pair(y, x, rest)) % p
            assert fold(cs, lambda x, rest: fold(rest, lambda y, rem: symmetric(x, y, rem), p), p) == 0
            folds += 1
            double_swaps += 1
            symmetric_zeros += 1
            n = rng.randrange(2, 7)
            matrix = [[rng.randrange(p) for _ in range(n)] for _ in range(n)]
            j = rng.randrange(n-1)
            changed = [r[:] for r in matrix]
            changed[j], changed[j+1] = changed[j+1], changed[j]
            assert numeric_det(changed, p) == -numeric_det(matrix, p) % p
            left, right = sorted(rng.sample(range(n), 2))
            changed = [r[:] for r in matrix]
            changed[right] = changed[left][:]
            assert numeric_det(changed, p) == 0
            row_swaps += 1
            equal_rows += 1
            char_two += p == 2
    # In F2, x=-x does not imply x=0; the zero-row-pair proof must cancel directly.
    assert 1 == -1 % 2 and 1 != 0
    print(json.dumps(dict(indexed_fold_checks=folds, double_selection_swaps=double_swaps,
        symmetric_double_selection_zeros=symmetric_zeros, arbitrary_adjacent_row_swaps=row_swaps,
        separated_equal_row_zeros=equal_rows, characteristic_two_row_cases=char_two,
        divide_by_two_counterexamples=1,
        scope='Lean cofactor/indexed equivalence and determinant alternation, including separated equal rows in characteristic two. Invertibility-to-nonzero and shared-denominator identity remain open.'), indent=2))


if __name__ == '__main__': main()
