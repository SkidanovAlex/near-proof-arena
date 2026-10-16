"""GKR-compressed mandatory external-input-root verifier for a committed-input hash component.

The caller supplies a trusted receipt created before proof generation. It is
not read from the proof and cannot be omitted. This is not recursive producer
routing, nor a cryptographic security theorem for the diagnostic Q8 protocol.
"""
import argparse,hashlib,json,sys
from pathlib import Path
PROFILE='near-direct-input-sha384-v1/captured376'
# Standard SHA384 IV, expanded into low-to-high 16-bit limbs per word.
SHA384_IV=(0xcbbb9d5dc1059ed8,0x629a292a367cd507,0x9159015a3070dd17,0x152fecd8f70e5939,
           0x67332667ffc00b31,0x8eb44a8768581511,0xdb0c2e0d64f98fa7,0x47b5481dbefa4fa4)
def check_public(public):
    from pq384_primitives import require
    require(type(public) is list and len(public)==88,'canonical SHA384 public length')
    require(all(type(x) is int for x in public),'canonical SHA384 integer encoding')
    require(all(0<=x<256 for x in public[:48]),'canonical SHA384 digest bytes')
    suffix=[1,0,0,0]+[(word>>(16*j))&65535 for word in SHA384_IV for j in range(4)]+[1,0,0,0]
    require(public[48:]==suffix,'canonical SHA384 IV and counts')
    return True

def canonical(value):return json.dumps(value,sort_keys=True,separators=(',',':')).encode()
def verify(wire,statement,expected):
    from pq384_primitives import require
    from packed_claim_handoff import packing_context
    import pq384_compact_gkr_bus_codec as codec
    require(type(expected)is dict and set(expected)=={'profile','declared_length','air_sha384','input_root','input_context_hex'},'required external input receipt')
    require(expected['profile']==PROFILE and type(expected['declared_length'])is int and expected['declared_length']==376,'restricted committed-input context')
    spec=statement['spec'];roots=[bytes.fromhex(r) for r in statement['roots']]
    require(len(roots)==3 and len(spec['air']['tables'])==3,'committed-input table layout')
    require(len(spec['public'])==88 and spec['air']['numPub']==88,'committed-input public layout')
    check_public(spec['public'])
    require(spec['air']['tables'][2]['width']==8*expected['declared_length'] and spec['log_rows'][2]==1,'declared input shape')
    require(hashlib.sha384(canonical(spec['air'])).hexdigest()==expected['air_sha384'],'trusted canonical AIR/framing/padding binding')
    root=bytes.fromhex(expected['input_root']);require(len(root)==48 and roots[2]==root,'externally fixed input root')
    context=packing_context(spec['log_rows'][2],spec['air']['tables'][2]['width'],spec['source_packings'][2])
    require(context.hex()==expected['input_context_hex'],'externally fixed input context')
    # All roots, complete AIR and public values are bound before bus challenges
    # by the mandatory underlying full verifier. No optional local-only path.
    codec.decode(wire,spec,roots)
    return True

def main():
    p=argparse.ArgumentParser();p.add_argument('binary');p.add_argument('statement');p.add_argument('expected_input');p.add_argument('--reference-dir',required=True);a=p.parse_args();sys.path.append(a.reference_dir)
    verify(Path(a.binary).read_bytes(),json.loads(Path(a.statement).read_text()),json.loads(Path(a.expected_input).read_text()))
    print('PASS: SHA384 committed-input component; mandatory external input root, full AIR and bus fingerprint diagnostic')
if __name__=='__main__':main()
