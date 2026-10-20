"""Cramer row identity against elimination, including singular matrices."""
import json
import random
from test_polynomial_determinant_degree import numeric_det


def solve_transpose(matrix, target, p):
    n = len(matrix)
    a = [[matrix[j][i] for j in range(n)]+[target[i]] for i in range(n)]
    for j in range(n):
        pivot = next(i for i in range(j, n) if a[i][j])
        a[j], a[pivot] = a[pivot], a[j]
        inv = pow(a[j][j], -1, p)
        a[j] = [v*inv % p for v in a[j]]
        for i in range(n):
            if i != j:
                factor = a[i][j]
                a[i] = [(v-factor*w) % p for v, w in zip(a[i], a[j])]
    return [row[-1] for row in a]


def main():
    rng = random.Random(45321)
    cramer = nonsingular = singular = other_rows = denominator_checks = 0
    for p in (2, 3, 5, 17):
        for _ in range(120):
            n = rng.randrange(1, 6)
            matrix = [[rng.randrange(p) for _ in range(n)] for _ in range(n)]
            weights = [rng.randrange(p) for _ in range(n)]
            combination = [sum(weights[i]*matrix[i][j] for i in range(n)) % p for j in range(n)]
            determinant = numeric_det(matrix, p)
            for r in range(n):
                changed = [row[:] for row in matrix]
                changed[r] = combination
                assert numeric_det(changed, p) == weights[r]*determinant % p
                cramer += 1
                if n > 1:
                    changed[r] = matrix[(r+1) % n][:]
                    assert numeric_det(changed, p) == 0
                    other_rows += 1
            if determinant:
                nonsingular += 1
                target = [rng.randrange(p) for _ in range(n)]
                solution = solve_transpose(matrix, target, p)
                assert [sum(solution[i]*matrix[i][j] for i in range(n)) % p for j in range(n)] == target
                for r in range(n):
                    changed = [row[:] for row in matrix]
                    changed[r] = target
                    assert solution[r] == numeric_det(changed, p)*pow(determinant, -1, p) % p
                    denominator_checks += 1
            else:
                singular += 1
        # Deliberately dependent nonzero row combination forces determinant zero.
        matrix = [[1, 2 % p], [1, 2 % p]]
        weights = [1, p-1]
        assert all(sum(weights[i]*matrix[i][j] for i in range(2)) % p == 0 for j in range(2))
        assert weights[0] != 0 and numeric_det(matrix, p) == 0
    assert singular > 0 and nonsingular > 0
    print(json.dumps(dict(row_cramer_identities=cramer, copied_other_row_zeros=other_rows,
        nonsingular_systems=nonsingular, singular_systems=singular,
        independently_solved_denominator_entries=denominator_checks, explicit_row_dependencies=4,
        scope='Lean Cramer row replacement and conditional shared-denominator formula. Determinant nonzeroness from inverse maps and Bezout matrix integration remain open.'), indent=2))


if __name__ == '__main__': main()
