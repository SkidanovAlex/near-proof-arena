"""Verifier-key preparation: freeze layout and precompute its existing hash.

No protocol change: only a constant hash is moved out of per-proof evaluation.
The returned verifier has no caller-selected layout or layout-digest argument.
"""
import json,types
from types import MappingProxyType
import pq384_terminal_gkr as g


def freeze(value):
    if isinstance(value,dict):return MappingProxyType({k:freeze(v) for k,v in value.items()})
    if isinstance(value,(list,tuple)):return tuple(map(freeze,value))
    return value


def prepare(layout,*,hash_function=g.hash_parts,transcript_type=g.Transcript):
    digest=g.hash_parts(g.PROFILE,json.dumps(layout,sort_keys=True,separators=(',',':')).encode())
    fixed=freeze(layout)
    def begin(selected,statement,claim):
        assert selected is fixed
        return transcript_type(hash_function(g.PROFILE,statement,digest,g.vector_bytes([g.ext(claim)])))
    verifier=types.FunctionType(g.verify.__code__,dict(g.verify.__globals__,begin=begin),argdefs=g.verify.__defaults__)
    def verify(statement,proof,claim=g.ZERO):return verifier(fixed,statement,proof,claim)
    return verify
