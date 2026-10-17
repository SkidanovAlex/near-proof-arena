"""Mandatory shared authentication for unchanged joint-opening binary bytes.

All roots, indices, challenges and source weights are verifier-derived.
No authentication bypass is exposed. Joint protocol soundness remains open.
"""
import struct
import pq384_joint_codec as codec
from pq384_primitives import require, field_words, P
from pq384_one_fold import ZERO
from check_whir_handoff import add, sub, mul

joint = codec.joint


def verify(data, arguments):
    n, fixed, maximum = codec.limits(arguments)
    require(type(data) is bytes and fixed <= len(data) <= maximum, 'shared joint size')
    require(data[:len(codec.MAGIC)] == codec.MAGIC, 'shared joint magic')
    offset = len(codec.MAGIC)

    def read(count):
        nonlocal offset
        require(offset+count <= len(data), 'shared joint truncation')
        value = data[offset:offset+count]
        offset += count
        return value

    def words(count):
        values = list(struct.unpack('<'+'I'*count, read(4*count)))
        require(all(v < P for v in values), 'shared joint noncanonical')
        return values

    reduction = [[words(4) for _ in range(3)] for _ in range(n)]
    rounds = [dict(quadratic=[words(4) for _ in range(3)], next_root=read(48).hex()) for _ in range(n)]
    proof = dict(profile=joint.PROFILE, reduction=reduction, rounds=rounds,
                 terminal=dict(profile='near-pq384-terminal-v1', coefficients=[[words(4)]]), queries=[])
    hs, ds, D, powers, betas, roots, contexts, challenges, samples = joint.replay(proof, arguments)
    stages = []
    for h, d in zip(hs, ds):
        stages.append((bytes.fromhex(h['expected_root_hex']), bytes.fromhex(h['context_hex']),
                       2*d, [s % (2*d) for s in samples], 2*len(h['lane_claims'])))
    for j, (root, context) in enumerate(zip(roots, contexts)):
        count = D >> j
        stages.append((root, context, count, [s % count for s in samples], 8))
    expected = fixed+sum(len(set(indices))*4*w+len(codec.mp.boundary(count, indices))*48
                         for _, _, count, indices, w in stages)
    require(len(data) == expected, 'shared joint canonical size')
    opened = []
    for root, context, count, indices, w in stages:
        leaves = [field_words(words(w)) for _ in codec.mp.shape(count, indices)]
        siblings = [read(48) for _ in codec.mp.boundary(count, indices)]
        authenticated, _ = codec.mp.expand(root, context, count, indices,
                                           dict(leaves=leaves, siblings=siblings))
        opened.append([struct.unpack('<'+'I'*w, leaf) for leaf in authenticated])
    require(offset == len(data), 'shared joint trailing bytes')
    for qi, sample in enumerate(samples):
        a = b = ZERO
        for branch, (d, ps, beta) in enumerate(zip(ds, powers, betas)):
            leaf = opened[branch][qi]
            left = right = ZERO
            for lane, power in enumerate(ps):
                left = add(left, tuple(v*leaf[2*lane] % P for v in power))
                right = add(right, tuple(v*leaf[2*lane+1] % P for v in power))
            if d < D:
                left = right = (left, right)[(sample % (4*d))//(2*d)]
            a = add(a, mul(beta, left))
            b = add(b, mul(beta, right))
        degree = D
        for j, challenge in enumerate(challenges):
            leaf = opened[len(ds)+j][qi]
            pair = (tuple(leaf[:4]), tuple(leaf[4:]))
            i = sample % (2*degree)
            omega = pow(440564289, (1 << 27)//(4*degree), P)
            x = pow(omega, i, P)
            even = tuple(v*pow(2, -1, P) % P for v in add(a, b))
            odd = tuple(v*pow(2*x, -1, P) % P for v in sub(a, b))
            require(add(even, mul(challenge, sub(odd, even))) == pair[i//degree],
                    'shared joint fold consistency')
            a, b = pair
            degree //= 2
    return True
