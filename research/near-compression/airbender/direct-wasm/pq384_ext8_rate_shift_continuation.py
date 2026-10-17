"""Reference rate shift with arbitrary-weight authenticated continuation.

Two skipped folds, rate-8 next oracle and full continuation to a constant.
JSON paths are deliberately uncompressed. No QROM or full NEAR claim.
"""
import pq384_ext8_reusable as p
import pq384_ext8_rate_shift as diagnostic
e, h = p.e, p.h
PROFILE = 'near-ext8-rate-shift-continuation-v1'


def start(config, root, continuation_queries):
    h.require(type(continuation_queries) is int and 1 <= continuation_queries <= 4096, 'continuation queries')
    h.require(type(root) is bytes and len(root) == 48, 'expected source root')
    wire = p.config_bytes(config)
    h.require(config['degree'] >= 8, 'two folds and nontrivial continuation')
    return h.Transcript(PROFILE.encode() + h.u64(continuation_queries) + wire + root)


def context(seed, degree):
    return h.hash_parts(b'rate-shift/paired-rate8-context-v1', seed, h.u64(degree), h.u64(8 * degree))


def tree(coeff, ctx):
    n = 8 * len(coeff)
    omega = pow(440564289, (1 << 27) // n, e.P)
    values = e.fft(coeff + [e.ZERO] * (n - len(coeff)), omega)
    leaves = [p.extbytes(values[i]) + p.extbytes(values[i+n//2]) for i in range(n//2)]
    root, layers = h.merkle_tree(leaves, ctx)
    return dict(root=root, layers=layers, leaves=leaves)


def monomial(x, degree):
    out = [e.ONE]
    for _ in range(1, degree):
        out.append(e.mul(out[-1], x))
    return out


def accumulate(weights, claim, points, values, gamma):
    h.require(len(points) == len(values), 'constraint shape')
    out, power = list(weights), gamma
    for x, value in zip(points, values):
        out = [e.add(w, e.mul(power, m)) for w, m in zip(out, monomial(x, len(weights)))]
        claim = e.add(claim, e.mul(power, value))
        power = e.mul(power, gamma)
    return out, claim


def source_value(openings, root, ctx, degree, index, challenges):
    h.require(type(openings) is list and len(openings) == 2, 'source quartet')
    a, c = p.read_opening(openings[0], root, ctx, degree, index, True)
    b, d = p.read_opening(openings[1], root, ctx, degree, index+degree, True)
    omega = pow(440564289, (1 << 27) // (4*degree), e.P)
    x, iota = pow(omega, index, e.P), pow(omega, degree, e.P)
    pieces = []
    for k in range(4):
        value = e.ZERO
        for j, v in enumerate([a, b, c, d]):
            value = e.add(value, e.scale(v, pow(iota, (-j*k) % 4, e.P)))
        pieces.append(e.scale(value, pow(4*pow(x, k, e.P) % e.P, -1, e.P)))
    return e.affine_fold(e.affine_fold(pieces, challenges[0]), challenges[1])[0]


def prove(coeff, config, root, continuation_queries):
    t = start(config, root, continuation_queries)
    src = p.source_tree(coeff, config)
    h.require(src['root'] == root, 'source root')
    cs, ws = [e.base(v) for v in coeff], p.eqweights(config['point'])
    claim, prefix = e.canonical(config['claim']), []
    for _ in range(2):
        wire = [list(v) for v in e.quadratic(cs, ws)]
        r, claim = p.round_start(t, wire, claim)
        prefix.append(wire)
        cs, ws = e.affine_fold(cs, r), e.affine_fold(ws, r)
    nxt = tree(cs, context(t.seed, len(cs)))
    next_root = nxt['root']
    t.commit(b'rate-shift/next-root', next_root)
    z = diagnostic.ood(t)
    y = e.evaluate(cs, z)
    t.commit(b'rate-shift/ood-value', p.extbytes(y))
    indices = p.sample(t, config['degree'], config['queries'])
    draw, _ = t.draw(b'rate-shift/mixing', 1, 8)
    gamma = tuple(draw[0])
    omega = pow(440564289, (1 << 27) // config['degree'], e.P)
    points = [e.base(pow(omega, i, e.P)) for i in indices]
    values = [e.evaluate(cs, x) for x in points]
    ws, claim = accumulate(ws, claim, [z]+points, [y]+values, gamma)
    source_queries = [[p.opening(src, i), p.opening(src, i+config['degree'])] for i in indices]
    trees, rounds = [nxt], []
    while len(cs) > 1:
        wire = [list(v) for v in e.quadratic(cs, ws)]
        r, claim = p.round_start(t, wire, claim)
        cs, ws = e.affine_fold(cs, r), e.affine_fold(ws, r)
        nxt = tree(cs, context(t.seed, len(cs)))
        trees.append(nxt)
        t.commit(b'rate-shift/continuation-root', nxt['root'])
        rounds.append(dict(quadratic=wire, root=nxt['root'].hex()))
    h.require(e.mul(cs[0], ws[0]) == claim, 'terminal claim')
    t.commit(b'rate-shift/terminal', p.extbytes(cs[0]))
    queries = []
    for s in p.sample(t, 2*config['degree'], continuation_queries):
        d, chain = config['degree']//4, []
        for i in range(len(rounds)):
            chain.append([p.opening(trees[i], s % (4*d)), p.opening(trees[i+1], s % (2*d))])
            d //= 2
        queries.append(chain)
    return dict(profile=PROFILE, quadratics=prefix, next_root=next_root.hex(), ood_value=list(y),
        source_queries=source_queries, rounds=rounds, terminal=list(cs[0]), queries=queries)


def prefix_metadata(proof, config, root, continuation_queries):
    """Replay the fixed prefix before reading source authentication data."""
    t = start(config, root, continuation_queries)
    h.require(type(proof['quadratics']) is list and len(proof['quadratics']) == 2, 'prefix shape')
    ws, claim, rs = p.eqweights(config['point']), e.canonical(config['claim']), []
    for wire in proof['quadratics']:
        r, claim = p.round_start(t, wire, claim)
        rs.append(r)
        ws = e.affine_fold(ws, r)
    d = config['degree']//4
    contexts, roots = [context(t.seed, d)], [p.hashread(proof['next_root'])]
    t.commit(b'rate-shift/next-root', roots[0])
    z, y = diagnostic.ood(t), e.canonical(proof['ood_value'])
    t.commit(b'rate-shift/ood-value', p.extbytes(y))
    indices = p.sample(t, config['degree'], config['queries'])
    draw, _ = t.draw(b'rate-shift/mixing', 1, 8)
    gamma = tuple(draw[0])
    return t, ws, claim, rs, contexts, roots, z, y, indices, gamma


def continuation_metadata(proof, config, root, continuation_queries, prefix):
    """Authenticate source constraints and derive all continuation query indices."""
    t, ws, claim, rs, contexts, roots, z, y, indices, gamma = prefix
    d = config['degree']//4
    h.require(type(proof['source_queries']) is list and len(proof['source_queries']) == config['queries'], 'source count')
    values = [source_value(q, root, p.source_context(config), config['degree'], i, rs)
              for q, i in zip(proof['source_queries'], indices)]
    omega = pow(440564289, (1 << 27)//config['degree'], e.P)
    points = [e.base(pow(omega, i, e.P)) for i in indices]
    ws, claim = accumulate(ws, claim, [z]+points, [y]+values, gamma)
    h.require(type(proof['rounds']) is list and len(proof['rounds']) == d.bit_length()-1, 'continuation shape')
    rs = []
    for rd in proof['rounds']:
        h.require(type(rd) is dict and set(rd) == {'quadratic','root'}, 'round fields')
        r, claim = p.round_start(t, rd['quadratic'], claim)
        rs.append(r)
        ws = e.affine_fold(ws, r)
        d //= 2
        contexts.append(context(t.seed, d))
        roots.append(p.hashread(rd['root']))
        t.commit(b'rate-shift/continuation-root', roots[-1])
    terminal = e.canonical(proof['terminal'])
    h.require(e.mul(ws[0], terminal) == claim, 'terminal residual')
    terminal_tree = tree([terminal], contexts[-1])
    h.require(terminal_tree['root'] == roots[-1], 'terminal oracle')
    t.commit(b'rate-shift/terminal', p.extbytes(terminal))
    samples = p.sample(t, 2*config['degree'], continuation_queries)
    return roots, contexts, rs, samples, terminal_tree


def verify(proof, config, root, continuation_queries):
    h.require(type(proof) is dict and set(proof) == {'profile','quadratics','next_root','ood_value',
        'source_queries','rounds','terminal','queries'} and proof['profile'] == PROFILE, 'proof fields')
    prefix = prefix_metadata(proof, config, root, continuation_queries)
    roots, contexts, rs, samples, _ = continuation_metadata(proof, config, root, continuation_queries, prefix)
    h.require(type(proof['queries']) is list and len(proof['queries']) == continuation_queries, 'continuation query count')
    for s, chain in zip(samples, proof['queries']):
        h.require(type(chain) is list and len(chain) == len(rs), 'chain shape')
        d = config['degree']//4
        for j, (r, query) in enumerate(zip(rs, chain)):
            h.require(type(query) is list and len(query) == 2, 'pair shape')
            index = s % (4*d)
            a, b = p.read_opening(query[0], roots[j], contexts[j], 2*d, index, False)
            nxt = p.read_opening(query[1], roots[j+1], contexts[j+1], d, s % (2*d), False)
            omega = pow(440564289, (1 << 27)//(8*d), e.P)
            x = pow(omega, index, e.P)
            even = e.scale(e.add(a, b), pow(2, -1, e.P))
            odd = e.scale(e.sub(a, b), pow(2*x, -1, e.P))
            h.require(e.add(even, e.mul(r, e.sub(odd, even))) == nxt[index//(2*d)], 'fold consistency')
            d //= 2
    return True
