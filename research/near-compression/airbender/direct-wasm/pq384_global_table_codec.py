"""Full table-local AIR plus shared global-chain binary, external trusted spec/root.

AIR equations derive the packed-opening arguments before PCS decoding. Decode
runs both verification layers; no witness, point, branch or size is proof-chosen.
"""
import struct
import pq384_global_table_air as air
import pq384_global_codec as pcs
from pq384_primitives import P,require
MAGIC=b'NPGT\x00\x01'

def shape(spec):
    table,d=air.validate(spec);n=spec['log_rows'];w=table['width'];D=(1<<n)*spec['packing']
    terminal=spec['terminal_degree'];rounds=D.bit_length()-terminal.bit_length()
    fixed=len(MAGIC)+16*(n*(d+2)+3*w+3*n)
    pcs_min=len(pcs.MAGIC)+96*rounds+16*terminal;pcs_max=pcs_min
    for j in range(rounds+1):
        words=2*((w+spec['packing']-1)//spec['packing']) if j==0 else 8
        pcs_max+=pcs.gc.QUERIES*(4*words+48*((2*D).bit_length()-1));D//=2
    return n,w,d,fixed,pcs_min,pcs_max

def encode(proof,spec,root):
    args=air.verify_reduction(proof,spec,root);n,w,d,fixed,_,_=shape(spec);out=bytearray(MAGIC)
    def vector(values,count):
        require(isinstance(values,list) and len(values)==count,'table codec vector')
        for value in values:
            require(isinstance(value,list) and len(value)==4 and all(type(v)is int and 0<=v<P for v in value),'table codec Ext4')
            out.extend(struct.pack('<4I',*value))
    for rd in proof['constraint_rounds']:vector(rd,d+2)
    red=proof['shift_reduction'];vector(red['current_evals'],w);vector(red['next_evals'],w)
    for rd in red['rounds']:vector(rd,3)
    vector(proof['column_claims'],w);require(len(out)==fixed,'table prefix size')
    out.extend(pcs.encode(proof['opening'],terminal_degree=spec['terminal_degree'],**args));return bytes(out)

def decode(data,spec,root):
    n,w,d,fixed,minimum,maximum=shape(spec)
    require(type(data)is bytes and fixed+minimum<=len(data)<=fixed+maximum,'table codec size')
    require(data[:len(MAGIC)]==MAGIC,'table codec magic');offset=len(MAGIC)
    def vector(count):
        nonlocal offset
        result=[]
        for _ in range(count):
            value=list(struct.unpack_from('<4I',data,offset));offset+=16
            require(all(v<P for v in value),'table noncanonical field');result.append(value)
        return result
    rounds=[vector(d+2) for _ in range(n)]
    red=dict(current_evals=vector(w),next_evals=vector(w),rounds=[vector(3) for _ in range(n)])
    claims=vector(w);require(offset==fixed,'table prefix length')
    proof=dict(profile=air.PROFILE,constraint_rounds=rounds,shift_reduction=red,column_claims=claims,opening=None)
    args=air.verify_reduction(proof,spec,root)
    proof['opening']=pcs.decode(data[offset:],terminal_degree=spec['terminal_degree'],**args)
    return proof

if __name__=='__main__':
    import json,sys
    from pathlib import Path
    statement=json.loads(Path(sys.argv[2]).read_text())
    decode(Path(sys.argv[1]).read_bytes(),statement['spec'],bytes.fromhex(statement['root']))
    print('PASS: full table-local AIR/global-chain binary diagnostic')
