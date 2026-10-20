"""Singular row spans, arbitrary selections, and row-inverse nonzeroness."""
import itertools
import json
import random
from test_polynomial_determinant_degree import numeric_det
from test_determinant_row_replacement import solve_transpose


def product(a, b, p):
    n = len(a)
    return [[sum(a[i][k]*b[k][j] for k in range(n)) % p for j in range(n)] for i in range(n)]


def main():
    rng = random.Random(45381)
    permutations = singular_spans = selections = inverse_cases = inverse_entries = empty_cases = 0
    for p in (2, 3, 5, 17):
        for _ in range(100):
            n = rng.randrange(6)
            matrix = [[rng.randrange(p) for _ in range(n)] for _ in range(n)]
            det = numeric_det(matrix, p)
            perm = list(range(n))
            rng.shuffle(perm)
            parity = sum(perm[i] > perm[j] for i in range(n) for j in range(i+1, n)) % 2
            assert numeric_det([matrix[i] for i in perm], p) == ((-1)**parity*det) % p
            permutations += 1
            if det:
                inverse = [solve_transpose(matrix, [int(i == j) for j in range(n)], p) for i in range(n)]
                assert product(inverse, matrix, p) == [[int(i == j) for j in range(n)] for i in range(n)]
                assert numeric_det(matrix, p) != 0
                inverse_cases += 1
                inverse_entries += n*n
                empty_cases += n == 0
            if n:
                singular = [row[:] for row in matrix]
                if n == 1: singular[0] = [0]
                else: singular[-1] = singular[0][:]
                assert numeric_det(singular, p) == 0
                weights = [[rng.randrange(p) for _ in range(n)] for _ in range(n)]
                assert numeric_det(product(weights, singular, p), p) == 0
                singular_spans += 1
                choices = (itertools.product(range(n), repeat=n) if n <= 3 else
                           (tuple(rng.randrange(n) for _ in range(n)) for _ in range(30)))
                for selected in choices:
                    assert numeric_det([singular[i] for i in selected], p) == 0
                    selections += 1
    print(json.dumps(dict(row_permutation_checks=permutations, singular_row_combinations=singular_spans,
        singular_row_selections=selections, constructed_row_inverses=inverse_cases,
        inverse_entries_checked=inverse_entries, empty_identity_cases=empty_cases,
        scope='Lean determinant nonzeroness from a row inverse. The concrete Bezout matrix encoding/orientation and denominator budget integration remain open.'), indent=2))


if __name__ == '__main__': main()
