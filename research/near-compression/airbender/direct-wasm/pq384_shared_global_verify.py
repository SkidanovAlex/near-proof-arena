"""Verify the unchanged global-chain binary with one shared DAG check per stage.

The transcript, terminal check and fold relations match the expanded verifier.
Authentication is mandatory here: no caller-supplied authenticated flag or
unchecked leaf callback. Q8/Ext4 remains diagnostic, not certified security.
"""
import struct
import pq384_global_codec as codec
from pq384_primitives import require, field_words, P
from pq384_one_fold import ONE, ZERO, weights
from pq384_terminal import verify_terminal
from check_whir_handoff import add, sub, mul

gc = codec.gc


def verify(data, *, terminal_degree=1, **args):
    count, minimum, maximum = codec.limits(args, terminal_degree)
    require(type(data) is bytes and minimum <= len(data) <= maximum, 'shared codec size')
    require(data[:len(codec.MAGIC)] == codec.MAGIC, 'shared codec magic')
    offset = len(codec.MAGIC)

    def read(n):
        nonlocal offset
        require(offset + n <= len(data), 'shared codec truncation')
        result = data[offset:offset+n]
        offset += n
        return result

    def words(n):
        result = list(struct.unpack('<' + 'I'*n, read(4*n)))
        require(all(v < P for v in result), 'shared codec field')
        return result

    h, transcript, degree, powers, claim = gc.public(args, terminal_degree)
    initial = degree
    roots = [args['expected_root']]
    contexts = [bytes.fromhex(h['context_hex'])]
    challenges = []
    factor = ONE
    for j in range(count):
        quadratic = [words(4) for _ in range(3)]
        challenge, stage, claim = gc.round_start(transcript, quadratic, claim)
        challenges.append(challenge)
        factor = mul(factor, add(ONE, mul(challenge, sub(tuple(h['packed_point'][j]), ONE))))
        degree //= 2
        root = read(48)
        roots.append(root)
        contexts.append(gc.context(stage, degree, terminal_degree))
        transcript.commit(b'next-oracle-root', root)
    terminal = dict(profile='near-pq384-terminal-v1',
                    coefficients=[[words(4) for _ in range(terminal_degree)]])
    gc.disclose(transcript, terminal, terminal_degree)
    terminal_weights = [mul(factor, w) for w in weights(h['packed_point'][count:])]
    verify_terminal(terminal, expected_root=roots[-1], stage_binding=stage,
        degree_bound=degree, domain_size=4*degree, lanes=1,
        weights=[[list(v) for v in terminal_weights]], claim=claim)
    samples = gc.sample(transcript, 4*initial)
    stages = []
    degree = initial
    for j in range(count+1):
        indices = [s % (2*degree) for s in samples]
        word_count = 2*len(powers) if j == 0 else 8
        unique = codec.mp.shape(2*degree, indices)
        needed = codec.mp.boundary(2*degree, indices)
        stages.append((degree, indices, word_count, unique, needed))
        degree //= 2
    expected = minimum + sum(len(unique)*4*w + len(needed)*48
                             for _, _, w, unique, needed in stages)
    require(len(data) == expected, 'shared codec canonical size')
    pairs = []
    for j, (degree, indices, w, unique, needed) in enumerate(stages):
        leaves = [field_words(words(w)) for _ in unique]
        siblings = [read(48) for _ in needed]
        authenticated, _ = codec.mp.expand(roots[j], contexts[j], 2*degree,
            indices, dict(leaves=leaves, siblings=siblings))
        stage_pairs = []
        for leaf in authenticated:
            values = struct.unpack('<' + 'I'*w, leaf)
            if j == 0:
                left = right = ZERO
                for lane, power in enumerate(powers):
                    left = add(left, tuple(v*values[2*lane] % P for v in power))
                    right = add(right, tuple(v*values[2*lane+1] % P for v in power))
                stage_pairs.append((left, right))
            else:
                stage_pairs.append((tuple(values[:4]), tuple(values[4:])))
        pairs.append(stage_pairs)
    require(offset == len(data), 'shared codec trailing bytes')
    inverse_two = pow(2, -1, P)
    for qi, sample in enumerate(samples):
        degree = initial
        for j, challenge in enumerate(challenges):
            i = sample % (2*degree)
            left, right = pairs[j][qi]
            omega = pow(440564289, (1 << 27)//(4*degree), P)
            x = pow(omega, i, P)
            even = tuple(v*inverse_two % P for v in add(left, right))
            odd = tuple(v*pow(2*x, -1, P) % P for v in sub(left, right))
            require(add(even, mul(challenge, sub(odd, even))) == pairs[j+1][qi][i//degree],
                    'shared global chain fold consistency')
            degree //= 2
    return True
