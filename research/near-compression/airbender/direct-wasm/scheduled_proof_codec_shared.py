#!/usr/bin/env python3
"""Lossless canonical shared-vector binary container for the COMPLETE scheduled bus proof.

All JSON proof fields are retained, including redundant transcript data and
non-verifier metadata. Trusted AIR/public/profile/source roots remain external
verifier inputs. No cryptographic compression or security claim. Decoder bounds
are container resource limits, not protocol parameter validation: always call
the scheduled_bus_whir verifier with the trusted statement after decoding.

Format V2: magic; tagged value. Tag 10 references a prior packed-u32 vector.
Every distinct vector is emitted once, at its deterministic first occurrence.
No reference can target a future vector or another reference. Integers/vector words are little endian.
Dictionary keys use the fixed sorted vocabulary below and must be increasing.
Lengths/counts are u32. Specialized extension/vector tags have unique canonical
priority over dictionaries/lists; a final re-encoding check enforces uniqueness.
"""
import struct

P = 2013265921
MAGIC = b'NSBPC\x00\x02\x00'
MAX_BYTES = 128 * 1024 * 1024
MAX_NODES = 4_000_000
MAX_DEPTH = 64
MAX_STRING = 1_048_576
KEYS = tuple(sorted('''_marker aux_roots base_lde_factor batched_opening batching_challenge
bincode_bytes c0 c1 cap cap_size commitment constraint_rounds current_evals evals
evaluation_point experiment final_monomials finals format index initial_whir_seed
intermediate_whir_oracles leaf_values_concatenated limitations log_rows
memory_commitment next_evals num_columns ood_samples openings original_evaluation_point
path pow_nonces proof queries rounds rows security_bits_claimed setup_commitment
shift_reduction statement_words sumcheck_polys tables verified whir_pow_schedule
whir_queries_schedule whir_schedule whir_steps_lde_factors whir_steps_schedule
witness_commitment'''.split()))
KEY_IDS = {k: i for i, k in enumerate(KEYS)}
# 0 null; 1 false; 2 true; 3 u32; 4 u64; 5 UTF8; 6 list; 7 object;
# 8 nonempty packed-u32 list; 9 canonical extension element (four field words).


def require(ok, message):
    if not ok:
        raise ValueError(message)


def extension_words(value):
    if type(value) is not dict or set(value) != {'c0', 'c1'}:
        return None
    if not all(type(value[k]) is dict and set(value[k]) == {'c0', 'c1'} for k in ('c0', 'c1')):
        return None
    words = [value[a][b] for a in ('c0', 'c1') for b in ('c0', 'c1')]
    require(all(type(x) is int and 0 <= x < P for x in words), 'noncanonical extension field')
    return words


def encode(proof):
    """Encode all fields, rejecting unsupported types/keys and resource excess."""
    out = bytearray(MAGIC)
    nodes = 0
    vectors = {}
    def u32(x):
        out.extend(struct.pack('<I', x))
    def visit(x, depth):
        nonlocal nodes
        nodes += 1
        require(nodes <= MAX_NODES and depth <= MAX_DEPTH, 'container complexity bound')
        if x is None:
            out.append(0)
        elif type(x) is bool:
            out.append(2 if x else 1)
        elif type(x) is int:
            require(0 <= x < 2**64, 'unsigned integer range')
            out.append(3 if x < 2**32 else 4)
            out.extend(struct.pack('<I' if x < 2**32 else '<Q', x))
        elif type(x) is str:
            b = x.encode('utf-8')
            require(len(b) <= MAX_STRING, 'string bound')
            out.append(5); u32(len(b)); out.extend(b)
        elif type(x) is list:
            require(len(x) <= MAX_NODES - nodes, 'list bound')
            packed = bool(x) and all(type(v) is int and 0 <= v < 2**32 for v in x)
            if packed:
                nodes += len(x)
                key = tuple(x)
                if key in vectors:
                    out.append(10); u32(vectors[key])
                else:
                    vectors[key] = len(vectors)
                    out.append(8); u32(len(x))
                    for v in x: u32(v)
            else:
                out.append(6); u32(len(x))
                for v in x: visit(v, depth + 1)
        elif type(x) is dict:
            words = extension_words(x)
            if words is not None:
                out.append(9)
                for v in words: u32(v)
            else:
                require(all(type(k) is str and k in KEY_IDS for k in x), 'unknown object key')
                out.append(7); u32(len(x))
                for k in sorted(x, key=KEY_IDS.__getitem__):
                    out.append(KEY_IDS[k]); visit(x[k], depth + 1)
        else:
            raise ValueError('unsupported container value type')
        require(len(out) <= MAX_BYTES, 'container byte bound')
    require(type(proof) is dict and set(proof) == {'aux_roots', 'finals', 'tables'}, 'proof envelope')
    visit(proof, 0)
    return bytes(out)


def decode(data):
    """Strict decoding; rejects trailing, truncated, ambiguous or oversized data."""
    require(type(data) is bytes and len(data) <= MAX_BYTES, 'container byte bound/type')
    require(data.startswith(MAGIC), 'container magic/version')
    offset = len(MAGIC)
    nodes = 0
    vectors = []
    def take(n):
        nonlocal offset
        require(n <= len(data) - offset, 'truncated container')
        b = data[offset:offset+n]; offset += n
        return b
    def u32(): return struct.unpack('<I', take(4))[0]
    def visit(depth):
        nonlocal nodes
        nodes += 1
        require(nodes <= MAX_NODES and depth <= MAX_DEPTH, 'container complexity bound')
        tag = take(1)[0]
        if tag <= 2: return (None, False, True)[tag]
        if tag == 3: return u32()
        if tag == 4:
            v = struct.unpack('<Q', take(8))[0]
            require(v >= 2**32, 'nonminimal integer')
            return v
        if tag == 5:
            n = u32(); require(n <= MAX_STRING, 'string bound')
            try: return take(n).decode('utf-8')
            except UnicodeDecodeError as e: raise ValueError('invalid UTF8') from e
        if tag in (6, 7, 8):
            n = u32()
            require(n <= MAX_NODES - nodes, 'collection bound')
            if tag == 8:
                require(n > 0 and n <= (len(data)-offset)//4, 'packed vector length')
                nodes += n
                value = [u32() for _ in range(n)]
                vectors.append(value)
                return value
            if tag == 6:
                require(n <= len(data)-offset, 'list length')
                return [visit(depth+1) for _ in range(n)]
            require(n <= len(KEYS), 'object key count')
            result = {}; previous = -1
            for _ in range(n):
                key = take(1)[0]
                require(previous < key < len(KEYS), 'object key ordering')
                previous = key; result[KEYS[key]] = visit(depth+1)
            return result
        if tag == 9:
            v = [u32() for _ in range(4)]
            require(all(x < P for x in v), 'noncanonical extension field')
            return {'c0': {'c0': v[0], 'c1': v[1]}, 'c1': {'c0': v[2], 'c1': v[3]}}
        if tag == 10:
            index = u32()
            require(index < len(vectors), 'invalid/forward vector reference')
            value = vectors[index]
            require(len(value) <= MAX_NODES - nodes, 'reference expansion bound')
            nodes += len(value)
            return value.copy()
        raise ValueError('unknown value tag')
    proof = visit(0)
    require(offset == len(data), 'trailing container bytes')
    require(encode(proof) == data, 'noncanonical representation')
    return proof
