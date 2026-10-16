"""Row linearity and formal rational-field determinant transport."""
import json
import random
from test_polynomial_determinant_degree import determinant, numeric_det
from test_polynomial_fractions import make, plus, times, negative, equiv, canonical


def fraction_det(matrix, prime):
    if not matrix: return make([1], [1])
    result = make([], [1])
    for j, entry in enumerate(matrix[0]):
        minor = [[v for k, v in enumerate(row) if k != j] for row in matrix[1:]]
        term = times(entry, fraction_det(minor, prime), prime)
        result = plus(result, negative(term, prime) if j % 2 else term, prime)
    return result


def main():
    rng = random.Random(45181)
    row_cases = zero_rows = transports = nonzero_transports = 0
    for p in (2, 3, 5, 17):
        for _ in range(100):
            n = rng.randrange(1, 6)
            matrix = [[rng.randrange(p) for _ in range(n)] for _ in range(n)]
            r = rng.randrange(n)
            u, v = [rng.randrange(p) for _ in range(n)], [rng.randrange(p) for _ in range(n)]
            a, b = rng.randrange(p), rng.randrange(p)
            def replaced(row):
                result = [values[:] for values in matrix]
                result[r] = row
                return result
            lhs = numeric_det(replaced([(a*x+b*y) % p for x, y in zip(u, v)]), p)
            rhs = (a*numeric_det(replaced(u), p)+b*numeric_det(replaced(v), p)) % p
            assert lhs == rhs
            assert numeric_det(replaced([0]*n), p) == 0
            row_cases += 1
            zero_rows += 1
        for _ in range(25):
            n = rng.randrange(5)
            matrix = [[[rng.randrange(p) for _ in range(rng.randrange(4))]+[0] for _ in range(n)] for _ in range(n)]
            polynomial = determinant(matrix, p)
            rational = fraction_det([[make(entry, [1]) for entry in row] for row in matrix], p)
            assert equiv(rational, make(polynomial, [1]), p)
            assert canonical(rational, p) == canonical(make(polynomial, [1]), p)
            assert (not polynomial) == equiv(rational, make([], [1]), p)
            nonzero_transports += bool(polynomial)
            transports += 1
    # A row outside the selected minor cannot satisfy the selected-row theorem:
    # the empty determinant is one, whereas a=b=0 yields RHS zero.
    assert numeric_det([], 5) == 1 and (0*numeric_det([], 5)+0*numeric_det([], 5)) % 5 == 0
    print(json.dumps(dict(row_linearity_cases=row_cases, zero_row_cases=zero_rows,
        rational_determinant_transports=transports, nonzero_transports=nonzero_transports,
        missing_row_membership_counterexamples=1,
        scope='Lean selected-row linearity and formal rational-field determinant transport. Alternation, invertibility-to-nonzero and adjugate identity remain open.'), indent=2))


if __name__ == '__main__': main()
