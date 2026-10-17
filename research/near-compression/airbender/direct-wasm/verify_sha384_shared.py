"""Two-call shared compression component; both external input roots mandatory.

The verifier-supplied receipt authenticates the canonical exported AIR/config.
This wrapper does not prove producer-to-root routing, ZK or QROM soundness.
"""
import argparse,hashlib,json,sys
from pathlib import Path
from verify_sha384_family import canonical,fixed_contract,bitexpr
PROFILE='near-shared-sha384-v1/two267-five-nodes'
def verify(wire,statement,expected):
    from pq384_primitives import require
    from packed_claim_handoff import packing_context
    import pq384_compact_gkr_bus_codec as codec
    require(type(expected)is dict and set(expected)=={'profile','air_sha384','inputs'},'mandatory trusted shared receipt')
    require(expected['profile']==PROFILE,'shared profile')
    spec=statement['spec'];pub=spec['public'];air=spec['air'];roots=[bytes.fromhex(v) for v in statement['roots']]
    require(type(pub)is list and len(pub)==96 and all(type(v)is int and 0<=v<256 for v in pub),'two canonical digest byte arrays')
    require(len(roots)==len(air['tables'])==6 and all(len(r)==48 for r in roots),'six source roots')
    require(air['numPub']==air['maxPub']==96 and air['numBuses']==6 and air['pubSegs']==[],'shared canonical public/bus shape')
    require(spec['log_rows']==[9,3,3,3,1,1] and [t['width'] for t in air['tables']]==[5234,1666,180,182,2136,2136],'fixed shared shape')
    require(hashlib.sha384(canonical(air)).hexdigest()==expected['air_sha384'],'trusted canonical shared AIR')
    require(type(expected['inputs'])is list and len(expected['inputs'])==2,'both caller input receipts required')
    for c,receipt in enumerate(expected['inputs']):
        require(type(receipt)is dict and set(receipt)=={'declared_length','fixed_framing','input_root','input_context_hex'},'input receipt shape')
        n=receipt['declared_length'];fixed=receipt['fixed_framing'];fixed_contract(n,fixed);require(n==267,'fixed family length')
        table=air['tables'][4+c];require(table['maxLog']==1,'input maxLog')
        fixedexpr=[['*',['first'],['+',bitexpr(8*i,8),['-',['c',v]]]] for i,v in fixed]
        require(table['constraints'][8*n:8*n+len(fixed)]==fixedexpr and len(table['constraints'])==8*n+len(fixed)+3,'framing/source constraint contract')
        root=bytes.fromhex(receipt['input_root']);require(len(root)==48 and roots[4+c]==root,'mandatory external root for ordered call')
        require(packing_context(1,2136,spec['source_packings'][4+c]).hex()==receipt['input_context_hex'],'mandatory external context')
    codec.decode(wire,spec,roots)
    return True

def main():
    p=argparse.ArgumentParser();p.add_argument('binary');p.add_argument('statement');p.add_argument('expected_inputs');p.add_argument('--reference-dir',required=True);a=p.parse_args();sys.path.append(a.reference_dir)
    assert verify(Path(a.binary).read_bytes(),json.loads(Path(a.statement).read_text()),json.loads(Path(a.expected_inputs).read_text()))
    print('PASS: shared five-node/two-call component; both external roots and complete diagnostic proof verified')
if __name__=='__main__':main()
