"""Versioned SHA-384 primitive reference; NOT a complete or secure PCS profile.

No hidden SHA-256 statement digest, truncated hash state, or modulo-only draws.
Extension coefficient counts are explicit: this module chooses no extension
polynomial and establishes neither hash pseudorandomness nor QROM soundness.
"""
import hashlib
import struct

P = 2013265921
PREFIX = b'NEAR-PQ384-PRIMITIVES-V1'
LIMIT = (1 << 32) // P * P


def require(ok, reason):
    if not ok: raise ValueError(reason)


def u64(value):
    require(type(value) is int and 0 <= value < 1 << 64, 'u64')
    return struct.pack('<Q', value)


def hash_parts(tag, *parts):
    require(type(tag) is bytes and len(tag) < 1 << 32, 'hash tag')
    require(len(parts) < 1 << 32 and all(type(p) is bytes for p in parts), 'hash parts')
    h = hashlib.sha384()
    h.update(PREFIX + struct.pack('<I', len(tag)) + tag + struct.pack('<I', len(parts)))
    for part in parts:
        h.update(u64(len(part))); h.update(part)
    return h.digest()


def digest_words(value):
    require(type(value) is bytes and len(value) == 48, 'SHA-384 digest width')
    return list(struct.unpack('<12I', value))


def field_words(values):
    require(isinstance(values, list) and all(type(v) is int and 0 <= v < P for v in values),
            'canonical field words')
    return b''.join(struct.pack('<I', v) for v in values)


def accept_word(word):
    require(type(word) is int and 0 <= word < 1 << 32, 'sample word')
    return word % P if word < LIMIT else None


class Transcript:
    def __init__(self, statement):
        require(type(statement) is bytes, 'statement bytes')
        self.seed = hash_parts(b'transcript/init', statement)

    def commit(self, label, payload):
        self.seed = hash_parts(b'transcript/commit', self.seed, label, payload)

    def draw(self, label, count, coefficients, max_blocks=4096):
        require(type(label) is bytes and type(count) is int and type(coefficients) is int
                and 0 < count <= 4096 and 0 < coefficients <= 64, 'draw shape')
        require(type(max_blocks) is int and 0 < max_blocks <= 1 << 20, 'draw block bound')
        # Separate requests even when they happen to request the same total words.
        seed = hash_parts(b'transcript/request', self.seed, label, u64(count), u64(coefficients))
        values = []; rejected = 0
        for counter in range(max_blocks):
            block = hash_parts(b'transcript/squeeze', seed, label, u64(counter))
            seed = hash_parts(b'transcript/ratchet', seed, label, block)
            for word in digest_words(block):
                value = accept_word(word)
                if value is None:
                    rejected += 1
                else:
                    values.append(value)
                    if len(values) == count * coefficients:
                        self.seed = hash_parts(b'transcript/draw-result', seed, label,
                                               u64(count), u64(coefficients), u64(counter+1))
                        return [values[i:i+coefficients] for i in range(0,len(values),coefficients)], {
                            'blocks': counter+1, 'rejected_words': rejected}
        # Failure does not advance state or fall back to biased reduction.
        raise ValueError('rejection sampler exhausted block budget')


def merkle_tree(leaves, context):
    require(type(context) is bytes and isinstance(leaves, list) and len(leaves) >= 2
            and len(leaves) & (len(leaves)-1) == 0
            and all(type(v) is bytes for v in leaves), 'Merkle shape')
    layers = [[hash_parts(b'merkle/leaf', context, u64(i), leaf)
               for i, leaf in enumerate(leaves)]]
    while len(layers[-1]) > 1:
        values = layers[-1]; level = len(layers)
        layers.append([hash_parts(b'merkle/node', context, u64(level), values[i], values[i+1])
                       for i in range(0,len(values),2)])
    root = hash_parts(b'merkle/root', context, u64(len(leaves)), layers[-1][0])
    return root, layers


def merkle_path(layers, index):
    require(type(index) is int and 0 <= index < len(layers[0]), 'leaf index')
    path = []
    for layer in layers[:-1]:
        path.append(layer[index ^ 1]); index //= 2
    return path


def verify_path(expected_root, context, leaf_count, index, leaf, path):
    require(type(leaf_count) is int and leaf_count >= 2
            and leaf_count & (leaf_count-1) == 0, 'leaf count')
    require(type(index) is int and 0 <= index < leaf_count and type(leaf) is bytes, 'leaf')
    require(type(expected_root) is bytes and len(expected_root) == 48
            and isinstance(path, list) and len(path) == leaf_count.bit_length()-1
            and all(type(h) is bytes and len(h) == 48 for h in path), 'path shape')
    value = hash_parts(b'merkle/leaf', context, u64(index), leaf)
    for level, sibling in enumerate(path, 1):
        left, right = (sibling, value) if index & 1 else (value, sibling)
        value = hash_parts(b'merkle/node', context, u64(level), left, right)
        index //= 2
    require(hash_parts(b'merkle/root', context, u64(leaf_count), value) == expected_root,
            'Merkle root mismatch')
    return True
