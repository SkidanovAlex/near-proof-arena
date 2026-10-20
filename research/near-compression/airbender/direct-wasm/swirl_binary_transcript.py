"""Version 2 diagnostic bindings: canonical binary prefix and GKR messages.

Caller must first verify prefix under the fixed native key and derive controls.
These hashes replace v1 Debug/JSON bindings and therefore change challenges.
"""
from pq384_primitives import hash_parts
from swirl_bundle_codec import encode_gkr,pack,unpack
MAGIC=b'NPBND002'


def statement(prefix):
    if not isinstance(prefix,bytes) or not prefix.startswith(b'NPREF001'):
        raise ValueError('canonical native prefix required')
    return hash_parts(b'nearproof-binary-prefix-gkr-v2',prefix)


def binding(statement_digest,layout,proof):
    if len(statement_digest)!=48:raise ValueError('statement digest')
    return hash_parts(b'nearproof-binary-gkr-to-whir-v2',statement_digest,encode_gkr(layout,proof))


def pack_v2(sections):return MAGIC+pack(sections)[8:]
def unpack_v2(data):
    if data[:8]!=MAGIC:raise ValueError('binary transcript bundle version')
    return unpack(b'NPBND001'+data[8:])
