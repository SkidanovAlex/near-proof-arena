"""Exercise actual opening authentication/batching and heterogeneous projection.
Regression evidence only: no commitment-security or extraction theorem.
"""
import json
from pathlib import Path
from pq384_primitives import P, field_words, merkle_tree, merkle_path
from pq384_batched_fold import check_opening
from check_whir_handoff import add, mul


def main():
    cases = negatives = 0
    beta = [(0, 0, 0, 0), (1, 0, 0, 0), (7, 11, 13, 17)]
    def source(lane, x):
        return ((lane+3)*x*x+(lane+5)*x+lane+19) % P
    def weighted(x):
        out = (0, 0, 0, 0)
        for lane, coefficient in enumerate(beta):
            out = add(out, mul(coefficient, (source(lane, x), 0, 0, 0)))
        return out
    for k in range(4):
        for d in [1, 2, 4, 8]:
            D = (1 << k)*d
            omega = pow(440564289, (1 << 27)//(4*D), P)
            eta = pow(omega, 1 << k, P)
            assert pow(omega, 2*D, P) == P-1
            context = f'heterogeneous-pair-regression/{k}/{d}'.encode()
            leaves = []
            for index in range(2*d):
                y = pow(eta, index, P)
                leaves.append([v for lane in range(3)
                               for v in (source(lane, y), source(lane, -y))])
            root, layers = merkle_tree([field_words(v) for v in leaves], context)
            for s in range(4*D):
                index = s % (2*d)
                op = dict(leaf=leaves[index], path=[v.hex() for v in merkle_path(layers, index)])
                pair = check_opening(op, root, context, 2*d, index, True, beta)
                if d < D:
                    pair = (pair[(s % (4*d))//(2*d)],)*2
                x = pow(omega, s % (2*D), P)
                assert pair == (weighted(pow(x, 1 << k, P)),
                                weighted(pow(-x, 1 << k, P)))
                cases += 1
            bad = dict(leaf=leaves[0][:], path=[v.hex() for v in merkle_path(layers, 0)])
            bad['leaf'][0] = (bad['leaf'][0]+1) % P
            try:
                check_opening(bad, root, context, 2*d, 0, True, beta)
            except ValueError:
                negatives += 1
            else:
                raise AssertionError('altered authenticated leaf accepted')
    report = dict(status='PASS', pair_checks=cases, altered_leaf_rejections=negatives,
                  lifts=[0,1,2,3], source_degrees=[1,2,4,8], lanes=3,
                  scope='Actual check_opening plus verifier duplicate-side expression vs independent polynomial evaluation. Mixed Ext4 beta coefficients, including zero and one. Not a cryptographic binding or full-verifier proof.')
    out = Path(__file__).resolve().parents[2]/'results/heterogeneous-source-pair-parity.json'
    out.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
