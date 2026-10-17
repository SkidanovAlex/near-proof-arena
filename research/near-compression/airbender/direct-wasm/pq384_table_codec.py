"""Lossless fixed-shape table-local proof codec. Decoding is not verification."""
import struct
from pq384_primitives import P,require
from pq384_table_air import validate,PROFILE
import pq384_batched_codec as pcs
MAGIC=b'NPTA\x00\x01'

def shape(spec):
    table,degree=validate(spec);n=spec['log_rows'];w=table['width']
    return n,w,degree,pcs.expected_size(n,w,spec['packing'])

def expected_size(spec):
    n,w,d,opening=shape(spec)
    return len(MAGIC)+16*(n*(d+2)+3*w+3*n)+opening

def encode(proof,spec):
    n,w,d,_=shape(spec);out=bytearray(MAGIC)
    require(type(proof)is dict and set(proof)=={'profile','constraint_rounds','shift_reduction','column_claims','opening'} and proof['profile']==PROFILE,'table codec fields')
    def vector(xs,count):
        require(isinstance(xs,list) and len(xs)==count,'table codec vector')
        for x in xs:
            require(isinstance(x,list) and len(x)==4 and all(type(v)is int and 0<=v<P for v in x),'table codec Ext4')
            out.extend(struct.pack('<4I',*x))
    require(isinstance(proof['constraint_rounds'],list) and len(proof['constraint_rounds'])==n,'table codec rounds')
    for rd in proof['constraint_rounds']:vector(rd,d+2)
    red=proof['shift_reduction']
    require(type(red)is dict and set(red)=={'current_evals','next_evals','rounds'},'table codec shift')
    vector(red['current_evals'],w);vector(red['next_evals'],w)
    require(isinstance(red['rounds'],list) and len(red['rounds'])==n,'table codec shift rounds')
    for rd in red['rounds']:vector(rd,3)
    vector(proof['column_claims'],w)
    out.extend(pcs.encode(proof['opening'],n,w,spec['packing']))
    require(len(out)==expected_size(spec),'table codec size')
    return bytes(out)

def decode(data,spec):
    require(type(data)is bytes and len(data)==expected_size(spec),'table codec byte length')
    require(data[:len(MAGIC)]==MAGIC,'table codec magic')
    n,w,d,opening=shape(spec);offset=len(MAGIC)
    def vector(count):
        nonlocal offset
        result=[]
        for _ in range(count):
            x=list(struct.unpack_from('<4I',data,offset));offset+=16
            require(all(v<P for v in x),'table codec canonical field');result.append(x)
        return result
    rounds=[vector(d+2) for _ in range(n)]
    red=dict(current_evals=vector(w),next_evals=vector(w),rounds=[vector(3) for _ in range(n)])
    claims=vector(w);require(len(data)-offset==opening,'table codec opening size')
    proof=dict(profile=PROFILE,constraint_rounds=rounds,shift_reduction=red,column_claims=claims,
               opening=pcs.decode(data[offset:],n,w,spec['packing']))
    require(encode(proof,spec)==data,'table codec canonical roundtrip')
    return proof
