"""Pre-state trie surgery for gen_extra_d0a.py (`--state OP`): canonical insert / delete with
exact nearcore `memory_usage`, a rebuild from the revealed key set, and one non-canonical
operation (an extension node with an empty key).

A trie is a tree of tuples over the witness store (partial: unrevealed nodes stay `('H', h)`):

    ('H', h)                         unrevealed subtree (hash only)
    ('L', key, vref, mem)            leaf, `key` relative nibbles, vref = (len, sha256(value))
    ('E', key, child, mem)           extension
    ('B', vref | None, {i: child}, mem)

Insert follows `NearSpec.PTrie.upsert` (spec/lean/NearSpec/TrieUpsert.lean; = nearcore
`insert_delete.rs`): leaf split, extension split, new branch child / value, and every
`memory_usage` on the path updated by differences (an unrevealed child's usage is recovered
from its parent's stored usage).  Delete is nearcore's `delete` + `squash_node`: a branch left
with one entry collapses into its child (leaf / extension merge; the child must be revealed),
an extension whose child became a leaf or extension merges with it.  `check_mem` re-verifies
every fully revealed node's usage against the canonical formula.
"""
from v3lib.prim import (Node, decode_node, hp_encode, nibbles, sha, value_mem, NODE_COST,
                        BYTE_OF_KEY, Reject)


class EditError(Exception):
    pass


def leaf_mem(key, vlen):
    return NODE_COST + BYTE_OF_KEY * len(hp_encode(key, True)) + value_mem(vlen)


def ext_own(key):
    # hp_encode([]) is one byte; the Python encoder needs a non-empty slice only for odd length
    return NODE_COST + BYTE_OF_KEY * len(hp_encode(key, False))


def mem(n):
    if n is None:
        return 0
    if n[0] == 'H':
        raise EditError("memory_usage of an unrevealed subtree is needed")
    return n[-1]


def load(store, root):
    """The revealed tree below `root` (None for the empty trie, ZERO32 root)."""
    if root == bytes(32):
        return None

    def go(h):
        if h not in store:
            return ('H', h)
        try:
            x = decode_node(store[h])
        except Reject:
            raise EditError("not a node: %s" % h.hex())
        if x.kind == 'leaf':
            return ('L', x.key, x.vref, x.mem)
        if x.kind == 'ext':
            return ('E', x.key, go(x.child), x.mem)
        return ('B', x.vref, {i: go(c) for i, c in x.children.items()}, x.mem)
    return go(root)


def leaf(key, vref):
    return ('L', list(key), vref, leaf_mem(key, vref[0]))


def wrap(prefix, b):
    return b if not prefix else ('E', list(prefix), b, ext_own(prefix) + mem(b))


def cp_len(a, b):
    i = 0
    while i < min(len(a), len(b)) and a[i] == b[i]:
        i += 1
    return i


def insert(n, key, vref):
    if n is None:
        return leaf(key, vref)
    t = n[0]
    if t == 'H':
        raise EditError("insert runs into an unrevealed subtree")
    if t == 'L':
        k = n[1]
        if k == key:
            return leaf(k, vref)
        p = cp_len(k, key)
        kr, nr = k[p:], key[p:]
        kids, bv, m = {}, None, NODE_COST
        if not kr:
            bv = n[2]
            m += value_mem(bv[0])
        else:
            kids[kr[0]] = leaf(kr[1:], n[2])
            m += mem(kids[kr[0]])
        if not nr:
            bv = vref
            m += value_mem(vref[0])
        else:
            kids[nr[0]] = leaf(nr[1:], vref)
            m += mem(kids[nr[0]])
        return wrap(key[:p], ('B', bv, kids, m))
    if t == 'E':
        k, c, m = n[1], n[2], n[3]
        if key[:len(k)] == k:
            c2 = insert(c, key[len(k):], vref)
            return ('E', k, c2, m - mem(c) + mem(c2))
        p = cp_len(k, key)
        cm = m - ext_own(k)
        x, xs = k[p], k[p + 1:]
        if xs:
            sub, sm = ('E', xs, c, ext_own(xs) + cm), ext_own(xs) + cm
        else:
            sub, sm = c, cm
        nr = key[p:]
        if not nr:
            return wrap(key[:p], ('B', vref, {x: sub}, NODE_COST + value_mem(vref[0]) + sm))
        fresh = leaf(nr[1:], vref)
        return wrap(key[:p], ('B', None, {x: sub, nr[0]: fresh}, NODE_COST + sm + mem(fresh)))
    bv, kids, m = n[1], dict(n[2]), n[3]
    if not key:
        return ('B', vref, kids, m + value_mem(vref[0]) - (value_mem(bv[0]) if bv else 0))
    c = key[0]
    old = kids.get(c)
    new = insert(old, key[1:], vref)
    kids[c] = new
    return ('B', bv, kids, m - mem(old) + mem(new))


def squash(n):
    """nearcore `squash_node` of a branch / extension after a deletion below it."""
    if n is None:
        return None
    if n[0] == 'E':
        k, c = n[1], n[2]
        if c[0] == 'L':
            return leaf(k + c[1], c[2])
        if c[0] == 'E':
            cm = c[3] - ext_own(c[1])
            return ('E', k + c[1], c[2], ext_own(k + c[1]) + cm)
        return n
    if n[0] != 'B':
        return n
    bv, kids = n[1], n[2]
    if len(kids) + (1 if bv else 0) >= 2:
        return n
    if not kids:
        return leaf([], bv) if bv else None
    (i, c), = kids.items()
    if c[0] == 'H':
        raise EditError("delete collapses a branch onto an unrevealed child")
    if c[0] == 'L':
        return leaf([i] + c[1], c[2])
    if c[0] == 'E':
        cm = c[3] - ext_own(c[1])
        return ('E', [i] + c[1], c[2], ext_own([i] + c[1]) + cm)
    return ('E', [i], c, ext_own([i]) + mem(c))


def delete(n, key):
    if n is None or n[0] == 'H':
        raise EditError("delete: key absent or unrevealed")
    t = n[0]
    if t == 'L':
        if n[1] != key:
            raise EditError("delete: key absent")
        return None
    if t == 'E':
        k, c, m = n[1], n[2], n[3]
        if key[:len(k)] != k:
            raise EditError("delete: key absent")
        c2 = delete(c, key[len(k):])
        if c2 is None:
            return None
        return squash(('E', k, c2, m - mem(c) + mem(c2)))
    bv, kids, m = n[1], dict(n[2]), n[3]
    if not key:
        if not bv:
            raise EditError("delete: key absent")
        return squash(('B', None, kids, m - value_mem(bv[0])))
    c = key[0]
    if c not in kids:
        raise EditError("delete: key absent")
    old = kids[c]
    new = delete(old, key[1:])
    if new is None:
        del kids[c]
    else:
        kids[c] = new
    return squash(('B', bv, kids, m - mem(old) + mem(new)))


def get_vref(n, key):
    while n is not None:
        t = n[0]
        if t == 'H':
            raise EditError("get: unrevealed")
        if t == 'L':
            return n[2] if n[1] == key else None
        if t == 'E':
            if key[:len(n[1])] != n[1]:
                return None
            key, n = key[len(n[1]):], n[2]
            continue
        if not key:
            return n[1]
        n, key = n[2].get(key[0]), key[1:]
    return None


def ext0(n, path):
    """Non-canonical: put an extension with an EMPTY key above the node that starts at nibble
    path `path` (a node boundary); every ancestor's usage grows by ext_own([])."""
    if not path:
        return ('E', [], n, ext_own([]) + mem(n))
    t = n[0]
    if t == 'E':
        k = n[1]
        if path[:len(k)] != k:
            raise EditError("ext0: path is not a node boundary")
        c2 = ext0(n[2], path[len(k):])
        return ('E', k, c2, n[3] - mem(n[2]) + mem(c2))
    if t == 'B':
        kids = dict(n[2])
        old = kids[path[0]]
        kids[path[0]] = ext0(old, path[1:])
        return ('B', n[1], kids, n[3] - mem(old) + mem(kids[path[0]]))
    raise EditError("ext0: path is not a node boundary")


def leaves(n, path=()):
    """(full nibble key, vref) of every revealed value."""
    if n is None or n[0] == 'H':
        return
    if n[0] == 'L':
        yield list(path) + n[1], n[2]
    elif n[0] == 'E':
        yield from leaves(n[2], tuple(path) + tuple(n[1]))
    else:
        if n[1]:
            yield list(path), n[1]
        for i, c in sorted(n[2].items()):
            yield from leaves(c, tuple(path) + (i,))


def check_mem(n):
    """Canonical usage of every node whose subtree is fully revealed; returns usage or None."""
    if n is None or n[0] == 'H':
        return None
    if n[0] == 'L':
        want = leaf_mem(n[1], n[2][0])
    elif n[0] == 'E':
        c = check_mem(n[2])
        if c is None:
            return None
        want = ext_own(n[1]) + c
    else:
        cs = [check_mem(c) for c in n[2].values()]
        if any(c is None for c in cs):
            return None
        want = NODE_COST + (value_mem(n[1][0]) if n[1] else 0) + sum(cs)
    if want != n[-1]:
        raise EditError("memory_usage %d != canonical %d" % (n[-1], want))
    return want


def encode(n, out):
    """Serialise every revealed node into `out` (hash -> bytes); returns the root hash."""
    if n is None:
        return bytes(32)
    t = n[0]
    if t == 'H':
        return n[1]
    if t == 'L':
        x = Node('leaf', key=n[1], vref=n[2], mem=n[3])
    elif t == 'E':
        x = Node('ext', key=n[1], child=encode(n[2], out), mem=n[3])
    else:
        x = Node('branch', vref=n[1], children={i: encode(c, out) for i, c in n[2].items()}, mem=n[3])
    b = x.encode()
    h = sha(b)
    out[h] = b
    return h


def apply_ops(store, root, ops):
    """Run `--state` operations; returns (new_root, new_store_entries, log)."""
    t = load(store, root)
    new_vals = {}
    log = []
    for op in ops:
        kind, _, arg = op.partition(":")
        if kind == "del":
            t = delete(t, nibbles(bytes.fromhex(arg)))
        elif kind == "put":
            k, _, v = arg.partition("=")
            if v.startswith("@"):
                vr = get_vref(t, nibbles(bytes.fromhex(v[1:])))
                if vr is None:
                    raise EditError("put: source key %s absent" % v[1:])
            else:
                val = bytes.fromhex(v)
                vr = (len(val), sha(val))
                new_vals[vr[1]] = val
            t = insert(t, nibbles(bytes.fromhex(k)), vr)
        elif kind == "keep":
            pfx = [bytes.fromhex(p) for p in arg.split(",") if p]
            kv = [(k, vr) for k, vr in leaves(t)
                  if len(k) % 2 == 0 and any(nibbles(p) == k[:2 * len(p)] for p in pfx)]
            t = None
            for k, vr in kv:
                t = insert(t, k, vr)
            log.append("keep %s: %d keys" % (arg, len(kv)))
        elif kind == "ext0":
            t = ext0(t, [int(c, 16) for c in arg])
        else:
            raise EditError("unknown state op %r" % op)
    if not any(op.startswith("ext0:") for op in ops):
        check_mem(t)
    out = dict(new_vals)
    r = encode(t, out)
    return r, out, log
