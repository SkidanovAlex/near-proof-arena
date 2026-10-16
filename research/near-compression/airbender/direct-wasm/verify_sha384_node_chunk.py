"""Compression-only wrapper. Expected ordered-use commitment is mandatory.
The receipt is caller-supplied trusted configuration, never derived from a proof.
"""
import argparse,hashlib,json,sys
from pathlib import Path
PROFILE='near-sha384-node-chunk-v1'
def canonical(x):return json.dumps(x,sort_keys=True,separators=(',',':'),ensure_ascii=True).encode()
def contract(statement,expected):
    from pq384_primitives import require
    from packed_claim_handoff import packing_context
    require(type(expected)is dict and set(expected)=={'profile','base','count','fanout_bits','use_count','air_sha384','use_root','use_context_hex'},'mandatory trusted compression receipt')
    require(expected['profile']==PROFILE,'profile')
    base,n,bits,uses=[expected[k] for k in ('base','count','fanout_bits','use_count')]
    require(all(type(v)is int for v in(base,n,bits,uses)) and 0<=base and 0<n<=25 and base+n<2013265921 and 1<=bits<=13 and 0<uses<8192,'bounded trusted config')
    spec=statement['spec'];air=spec['air'];roots=[bytes.fromhex(v) for v in statement['roots']]
    logs=[(80*n).bit_length(),n.bit_length(),n.bit_length(),uses.bit_length()]
    require(spec['public']==[] and spec['log_rows']==logs,'canonical empty public/shapes')
    require(len(roots)==4 and all(len(r)==48 for r in roots),'four commitments')
    require([t['width'] for t in air['tables']]==[5234,1666,178+bits,179] and [t['maxLog'] for t in air['tables']]==logs,'canonical table dimensions')
    require(air['numBuses']==5 and air['numPub']==air['maxPub']==0 and air['pubSegs']==[],'compression bus/public contract')
    require(hashlib.sha384(canonical(air)).hexdigest()==expected['air_sha384'],'trusted canonical AIR')
    for table in air['tables'][:3]:
        for interaction in table['interactions']:
            require(interaction['msg'][0][0]=='+' and interaction['msg'][0][1]==['c',base],'global interval base')
    def stop_constraint(active,tag,count):
        return ['*',['*',['v',active,0],['+',['last'],['*',['trans'],['+',['c',1],['-',['v',active,1]]]]]],['+',['v',tag,0],['-',['c',count-1]]]]
    require(air['tables'][2]['constraints'][5]==stop_constraint(1,0,n) and air['tables'][3]['constraints'][5]==stop_constraint(1,0,uses),'exact record/use active counts')
    root=bytes.fromhex(expected['use_root']);require(len(root)==48 and roots[3]==root,'mandatory external ordered-use root')
    require(packing_context(logs[3],179,spec['source_packings'][3]).hex()==expected['use_context_hex'],'mandatory use commitment context')
    return True

def verify(wire,statement,expected):
    import pq384_compact_gkr_bus_codec as codec
    contract(statement,expected)
    codec.decode(wire,statement['spec'],[bytes.fromhex(v) for v in statement['roots']])
    return True

def main():
    p=argparse.ArgumentParser();p.add_argument('binary');p.add_argument('statement');p.add_argument('expected_receipt');p.add_argument('--reference-dir',required=True);a=p.parse_args();sys.path.append(a.reference_dir)
    assert verify(Path(a.binary).read_bytes(),json.loads(Path(a.statement).read_text()),json.loads(Path(a.expected_receipt).read_text()))
    print('PASS compression-only diagnostic; externally fixed ordered uses. No call-chain or recursive proof claim.')
if __name__=='__main__':main()
