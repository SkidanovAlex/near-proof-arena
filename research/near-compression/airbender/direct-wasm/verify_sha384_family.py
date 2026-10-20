"""Bounded-length direct SHA384 component with mandatory trusted input receipt.

Public values must be the canonical standard-SHA384 digest/IV/count layout.
The trusted receipt fixes length, framing bytes, canonical AIR and input root.
This is committed witness data, not a zero-knowledge or recursion guarantee.
"""
import argparse,hashlib,json,sys
from pathlib import Path
PROFILE='near-direct-input-sha384-v2/bounded1024'
IV=(0xcbbb9d5dc1059ed8,0x629a292a367cd507,0x9159015a3070dd17,0x152fecd8f70e5939,0x67332667ffc00b31,0x8eb44a8768581511,0xdb0c2e0d64f98fa7,0x47b5481dbefa4fa4)
def canonical(x):return json.dumps(x,sort_keys=True,separators=(',',':')).encode()
def fixed_contract(n,fixed):
    if type(n)is not int or not 1<=n<=1024:raise ValueError('trusted declared length1..1024')
    if type(fixed)is not list:raise ValueError('trusted fixed framing list')
    prev=-1
    for pair in fixed:
        if type(pair)is not list or len(pair)!=2 or any(type(v)is not int for v in pair):raise ValueError('canonical framing pair')
        i,v=pair
        if not prev<i<n or not 0<=v<256:raise ValueError('canonical framing index/byte')
        prev=i

def canonical_public(pub):
    tail=[1,0,0,0]+[(word>>(16*j))&65535 for word in IV for j in range(4)]+[1,0,0,0]
    if type(pub)is not list or len(pub)!=88 or any(type(v)is not int for v in pub):raise ValueError('canonical public types/length')
    if any(not 0<=v<256 for v in pub[:48]) or pub[48:]!=tail:raise ValueError('standard SHA384 digest/IV/count public layout')

def bitexpr(base,k):
    return ['c',0] if k==0 else ['+',['v',base,0],['*',['c',2],bitexpr(base+1,k-1)]]
def verify(wire,statement,expected):
    from pq384_primitives import require
    from packed_claim_handoff import packing_context
    import pq384_compact_gkr_bus_codec as codec
    require(type(expected)is dict and set(expected)=={'profile','declared_length','fixed_framing','air_sha384','input_root','input_context_hex'},'mandatory trusted input receipt')
    require(expected['profile']==PROFILE,'bounded direct profile');n=expected['declared_length'];fixed=expected['fixed_framing'];fixed_contract(n,fixed)
    spec=statement['spec'];canonical_public(spec['public']);roots=[bytes.fromhex(v) for v in statement['roots']]
    require(len(roots)==len(spec['air']['tables'])==3,'direct table layout')
    require(spec['air']['numPub']==spec['air']['maxPub']==88,'direct public layout')
    table=spec['air']['tables'][2]
    require(table['width']==8*n and table['maxLog']==1 and spec['log_rows'][2]==1,'declared input shape')
    require(hashlib.sha384(canonical(spec['air'])).hexdigest()==expected['air_sha384'],'trusted canonical AIR')
    fixedexpr=[['*',['first'],['+',bitexpr(8*i,8),['-',['c',v]]]] for i,v in fixed]
    require(table['constraints'][8*n:8*n+len(fixed)]==fixedexpr,'trusted fixed framing expression contract')
    require(len(table['constraints'])==8*n+len(fixed)+(n+16)//128+1,'canonical input constraint count')
    root=bytes.fromhex(expected['input_root']);require(len(root)==48 and roots[2]==root,'mandatory external input root')
    require(packing_context(1,8*n,spec['source_packings'][2]).hex()==expected['input_context_hex'],'mandatory external input context')
    codec.decode(wire,spec,roots)
    return True

def main():
    p=argparse.ArgumentParser();p.add_argument('binary');p.add_argument('statement');p.add_argument('expected_input');p.add_argument('--reference-dir',required=True);a=p.parse_args();sys.path.append(a.reference_dir)
    assert verify(Path(a.binary).read_bytes(),json.loads(Path(a.statement).read_text()),json.loads(Path(a.expected_input).read_text()))
    print('PASS: bounded committed-witness SHA384; canonical IV/counts, mandatory input root and full diagnostic proof')
if __name__=='__main__':main()
