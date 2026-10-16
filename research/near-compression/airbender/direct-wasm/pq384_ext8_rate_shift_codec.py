"""Canonical multiproof transport for the rate-shift continuation reference.

Every index/count is derived from the verifier's configuration and transcript.
Repeated sampled checks are preserved after deterministic path expansion.
"""
import pq384_ext8_rate_shift_continuation as r
import pq384_multiproof as mp
p, h = r.p, r.h
MAGIC = b'NRS8MP01'
MAX_BYTES = 4*1024*1024


def compress(root, ctx, count, indices, openings):
    shared = mp.compress(root, ctx, count, indices,
        [bytes.fromhex(o['leaf']) for o in openings],
        [[p.hashread(x) for x in o['path']] for o in openings])
    return b''.join(shared['leaves']) + b''.join(shared['siblings'])


def encode(proof, config, root, continuation_queries):
    r.verify(proof, config, root, continuation_queries)
    prefix = r.prefix_metadata(proof, config, root, continuation_queries)
    indices = prefix[8]
    roots, contexts, _, samples, _ = r.continuation_metadata(proof, config, root, continuation_queries, prefix)
    out = bytearray(MAGIC+root)
    for wire in proof['quadratics']:
        out.extend(b''.join(p.extbytes(v) for v in wire))
    out.extend(p.hashread(proof['next_root']))
    out.extend(p.extbytes(proof['ood_value']))
    source_indices = [j for i in indices for j in (i, i+config['degree'])]
    out.extend(compress(root, p.source_context(config), 2*config['degree'], source_indices,
        [o for pair in proof['source_queries'] for o in pair]))
    for rd in proof['rounds']:
        out.extend(b''.join(p.extbytes(v) for v in rd['quadratic']))
        out.extend(p.hashread(rd['root']))
    out.extend(p.extbytes(proof['terminal']))
    d = config['degree']//4
    for stage in range(len(proof['rounds'])):
        out.extend(compress(roots[stage], contexts[stage], 4*d, [s % (4*d) for s in samples],
            [chain[stage][0] for chain in proof['queries']]))
        d //= 2
    h.require(len(out) <= MAX_BYTES, 'codec size cap')
    return bytes(out)


def decode(data, config, root, continuation_queries):
    h.require(type(data) is bytes and len(data) <= MAX_BYTES, 'codec size cap')
    r.start(config, root, continuation_queries)
    offset = 0
    def read(n):
        nonlocal offset
        h.require(type(n) is int and 0 <= n <= len(data)-offset, 'truncated codec')
        result = data[offset:offset+n]
        offset += n
        return result
    def expand(expected, ctx, count, indices, width):
        unique, boundary = mp.shape(count, indices), mp.boundary(count, indices)
        h.require(width*len(unique)+48*len(boundary) <= len(data)-offset, 'stage size')
        shared = dict(leaves=[read(width) for _ in unique], siblings=[read(48) for _ in boundary])
        leaves, paths = mp.expand(expected, ctx, count, indices, shared)
        return [dict(leaf=leaf.hex(), path=[x.hex() for x in path]) for leaf, path in zip(leaves, paths)]
    h.require(read(len(MAGIC)) == MAGIC, 'codec version')
    h.require(read(48) == root, 'external root binding')
    proof = dict(profile=r.PROFILE,
        quadratics=[[list(p.extread(read(32))) for _ in range(3)] for _ in range(2)],
        next_root=read(48).hex(), ood_value=list(p.extread(read(32))),
        source_queries=[], rounds=[], terminal=[], queries=[])
    prefix = r.prefix_metadata(proof, config, root, continuation_queries)
    indices = prefix[8]
    source_indices = [j for i in indices for j in (i, i+config['degree'])]
    source_openings = expand(root, p.source_context(config), 2*config['degree'], source_indices, 8)
    proof['source_queries'] = [source_openings[i:i+2] for i in range(0, len(source_openings), 2)]
    for _ in range((config['degree']//4).bit_length()-1):
        proof['rounds'].append(dict(quadratic=[list(p.extread(read(32))) for _ in range(3)], root=read(48).hex()))
    proof['terminal'] = list(p.extread(read(32)))
    roots, contexts, _, samples, terminal = r.continuation_metadata(proof, config, root, continuation_queries, prefix)
    d, openings = config['degree']//4, []
    for stage in range(len(proof['rounds'])):
        openings.append(expand(roots[stage], contexts[stage], 4*d, [s % (4*d) for s in samples], 64))
        d //= 2
    h.require(offset == len(data), 'trailing codec bytes')
    openings.append([p.opening(terminal, s % 4) for s in samples])
    proof['queries'] = [[[openings[j][i], openings[j+1][i]] for j in range(len(proof['rounds']))]
                        for i in range(len(samples))]
    return proof


def verify(data, config, root, continuation_queries):
    return r.verify(decode(data, config, root, continuation_queries), config, root, continuation_queries)


def breakdown(proof, config, root, continuation_queries):
    prefix = r.prefix_metadata(proof, config, root, continuation_queries)
    indices = prefix[8]
    _, _, _, samples, _ = r.continuation_metadata(proof, config, root, continuation_queries, prefix)
    rows = []
    def row(name, count, indices, width):
        rows.append(dict(stage=name, sampled_openings=len(indices), unique_leaves=len(set(indices)),
            leaf_bytes=width*len(set(indices)), sibling_bytes=48*len(mp.boundary(count, indices))))
    row('source', 2*config['degree'], [j for i in indices for j in (i, i+config['degree'])], 8)
    d = config['degree']//4
    for stage in range(len(proof['rounds'])):
        row(f'continuation-{stage}', 4*d, [s % (4*d) for s in samples], 64)
        d //= 2
    header = len(MAGIC)+48+2*96+48+32+len(proof['rounds'])*144+32
    total = header+sum(x['leaf_bytes']+x['sibling_bytes'] for x in rows)
    external = len(p.config_bytes(config))+8
    return dict(header_bytes=header, stages=rows, proof_bytes=total,
        external_canonical_configuration_bytes=external, total_required_input_bytes=total+external,
        root_already_in_proof=True, counts_and_indices_transcript_derived=True)
