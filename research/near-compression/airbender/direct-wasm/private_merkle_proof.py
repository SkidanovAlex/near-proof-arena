"""Diagnostic complete private Merkle verifier: compression AIR + same-use-root routing.

Trusted static SHA384 AIR/spec is external configuration. Public Merkle statement
is external input. Proof carries commitments and both proof components; original
siblings, hash-call messages, use rows and a native inner verifier are not inputs.
Ext8/q-configured diagnostic only: no PQ128 or compiled-correctness certificate.
"""
import hashlib
import struct
import merkle_recursive_call_routes as route
import sha384_call_ext8_pcs as call
import ext8_execution_codec as compression
from pq384_primitives import Transcript,hash_parts,require,u64
from verify_sha384_node_chunk import canonical,contract,PROFILE as CHUNK_PROFILE
from packed_claim_handoff import packing_context

PROFILE=b'near-private-merkle-verifier-ext8-v1'
ROUTE_MAGIC=b'NPMR8001'
BUNDLE_MAGIC=b'NPMV8001'
MAX_BYTES=32*1024*1024


def receipt(spec,roots,public):
    program=route.compile_routes(public);count=program['use_count']
    require(type(roots)is list and len(roots)==4,'four proof-carried roots')
    expected=dict(profile=CHUNK_PROFILE,base=0,count=count,fanout_bits=1,use_count=count,
        air_sha384=hashlib.sha384(canonical(spec['air'])).hexdigest(),use_root=roots[3],
        use_context_hex=packing_context(spec['log_rows'][3],179,spec['source_packings'][3]).hex())
    contract(dict(spec=spec,roots=roots),expected)
    require((1<<spec['log_rows'][3])==program['row_count'],'routing/use table alignment')
    return program


def compile_layout(spec,roots,public,queries):
    require(type(queries)is int and 1<=queries<=4096,'fixed query budget')
    program=receipt(spec,roots,public);n=program['row_count'];capacity=n*256
    eq=route.flatten_equations(program)
    st=hash_parts(PROFILE,u64(queries),canonical(public),canonical(spec),*[bytes.fromhex(r) for r in roots])
    t=Transcript(st);point=[tuple(x) for x in t.draw(b'private-merkle-routing-after-all-roots',(len(eq)-1).bit_length(),8)[0]]
    coeff=[call.g.ZERO]*capacity;claim=call.g.ZERO
    for e,w in zip(eq,call.g.eqs(point)):
        for slot,multiplier in e['terms']:
            require(0<=slot<n*179,'actual use-table slot')
            coeff[slot]=call.g.add(coeff[slot],call.g.mul(w,call.g.base(multiplier % route.P)))
        claim=call.g.add(claim,call.g.mul(w,call.g.base(e['constant'])))
    layout=call.g.layer_circuit(call.compile_dag(coeff,claim,capacity))
    return layout,st,t.seed,program


def parent(binding,gp):return hash_parts(PROFILE,binding,canonical(gp))


def prove_routing(rows,spec,roots,public,cache,native,queries):
    layout,st,binding,program=compile_layout(spec,roots,public,queries)
    require(not any(route.residuals(program,rows)),'honest routing equations')
    require(cache.root.hex()==roots[3],'same-use-root prover cache')
    n=len(rows);private=[call.g.base(rows[r][c]) if c<179 else call.g.ZERO for c in range(256) for r in range(n)]
    gp,ob=call.g.prove(layout,binding,private,kernel=native)
    branches=call.branches(dict(spec=spec,roots=roots),ob)
    opening=call.pcs.prove([cache,cache],native,st,parent(binding,gp),branches,ob['private_claim'],queries=queries)
    return dict(gkr=gp,opening=opening)


def encode_routing(proof,spec,roots,public,queries):
    layout,st,binding,_=compile_layout(spec,roots,public,queries)
    gp=proof['gkr'];ob=call.g.verify(layout,binding,gp)
    out=bytearray(ROUTE_MAGIC)
    for layer in gp['layers']:
        for value in [v for row in layer['rounds'] for v in row]+layer['inputs']:
            out+=struct.pack('<8I',*call.g.ext(value))
    out+=call.codec.encode(proof['opening'],st,parent(binding,gp),call.branches(dict(spec=spec,roots=roots),ob),ob['private_claim'],queries=queries,shared_sources=True)
    return bytes(out)


def verify_routing(wire,spec,roots,public,queries):
    require(type(wire)is bytes and len(wire)<=MAX_BYTES and wire[:8]==ROUTE_MAGIC,'routing framing')
    layout,st,binding,_=compile_layout(spec,roots,public,queries);offset=8;layers=[]
    def scalar():
        nonlocal offset
        require(offset+32<=len(wire),'truncated routing scalar')
        value=list(call.g.ext(struct.unpack_from('<8I',wire,offset)));offset+=32;return value
    for i in range(len(layout['layers'])-1,-1,-1):
        prev=layout['input_size'] if i==0 else len(layout['layers'][i-1])
        layers.append(dict(rounds=[[scalar() for _ in range(3)] for _ in range(2*(prev.bit_length()-1))],inputs=[scalar(),scalar()]))
    gp=dict(profile=call.g.PROFILE.decode(),layers=layers);ob=call.g.verify(layout,binding,gp)
    require(call.codec.verify(wire[offset:],st,parent(binding,gp),call.branches(dict(spec=spec,roots=roots),ob),ob['private_claim'],queries=queries),'routing PCS opening')
    return True


def combine(compression_wire,routing_wire):
    require(type(compression_wire)is bytes and type(routing_wire)is bytes,'component bytes')
    result=BUNDLE_MAGIC+u64(len(compression_wire))+compression_wire+routing_wire
    require(len(result)<=MAX_BYTES,'bundle cap')
    return result


def verify(wire,trusted_spec,public,queries):
    require(type(wire)is bytes and 16<=len(wire)<=MAX_BYTES and wire[:8]==BUNDLE_MAGIC,'bundle framing')
    size=struct.unpack_from('<Q',wire,8)[0]
    require(200<=size<=len(wire)-24,'compression length')
    cwire,rwire=wire[16:16+size],wire[16+size:]
    require(cwire[:8]==compression.magic('affine-v1'),'compression profile')
    roots=[cwire[8+48*i:8+48*(i+1)].hex() for i in range(4)]
    receipt(trusted_spec,roots,public)
    # Both components use exactly these proof-carried roots and trusted static spec.
    compression.decode(cwire,trusted_spec,roots,queries=queries,terminal_profile='affine-v1')
    verify_routing(rwire,trusted_spec,roots,public,queries)
    return True


if __name__=='__main__':
    import argparse,json,gzip
    from pathlib import Path
    p=argparse.ArgumentParser();p.add_argument('--proof',type=Path,required=True)
    p.add_argument('--trusted-spec',type=Path,required=True);p.add_argument('--public',type=Path,required=True)
    p.add_argument('--queries',type=int,required=True);a=p.parse_args()
    def read_json(path):
        raw=path.read_bytes()
        return json.loads(gzip.decompress(raw) if path.suffix=='.gz' else raw)
    assert verify(a.proof.read_bytes(),read_json(a.trusted_spec),read_json(a.public),a.queries)
    print('PASS complete bounded private Merkle verification; diagnostic security only, not full PCS recursion or PQ128.')
