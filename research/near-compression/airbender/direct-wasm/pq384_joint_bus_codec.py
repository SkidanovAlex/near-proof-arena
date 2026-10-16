"""Whole joint-bus diagnostic transport, including source and auxiliary roots."""
import struct
import pq384_joint_bus as combined
import pq384_joint_codec as joint
from pq384_primitives import require,P
bus=combined.bus
MAGIC=b'NPJB\x00\x01'

def shape(spec):
    degrees=bus.validate(spec);fixed=len(MAGIC)+48*len(degrees);dimensions=[]
    for ti,(table,d) in enumerate(zip(spec['air']['tables'],degrees)):
        n=spec['log_rows'][ti];layout=bus.aux.layout(table);cw=4*layout['aux_columns'];width=table['width']+cw
        fixed+=48+16*layout['finals']+16*(n*(d+2)+3*width+3*n)
        dimensions.append(dict(log_rows=n,width=table['width'],packing=spec['source_packings'][ti]))
        if cw:dimensions.append(dict(log_rows=n,width=cw,packing=spec['aux_packings'][ti]))
    _,minimum,maximum=joint.limits(dimensions);return fixed,minimum,maximum

def encode(proof,spec,roots):
    require(type(proof)is dict and set(proof)=={'profile','air','joint'} and proof['profile']==combined.PROFILE,'joint bus fields')
    prefix=proof['air'];args=combined.arguments(prefix,spec,roots);out=bytearray(MAGIC+b''.join(roots))
    def vector(values):
        for v in values:out.extend(struct.pack('<4I',*bus.ext(v)))
    for root,fs in zip(prefix['aux_roots'],prefix['finals']):out.extend(bus.pcs.decode_hash(root));vector(fs)
    for part in prefix['tables']:
        for rd in part['constraint_rounds']:vector(rd)
        red=part['shift_reduction'];vector(red['current_evals']);vector(red['next_evals'])
        for rd in red['rounds']:vector(rd)
        vector(part['column_claims'])
    fixed,_,_=shape(spec);require(len(out)==fixed,'joint AIR size')
    encoded=joint.encode(proof['joint'],args);out.extend(struct.pack('<Q',len(encoded)));out.extend(encoded);return bytes(out)

def _decode(data,spec,roots,shared):
    fixed,minimum,maximum=shape(spec);require(type(data)is bytes and fixed+8+minimum<=len(data)<=fixed+8+maximum,'joint bus size')
    require(data[:len(MAGIC)]==MAGIC,'joint bus magic');offset=len(MAGIC)
    def read(n):
        nonlocal offset
        require(offset+n<=len(data),'joint bus truncation');v=data[offset:offset+n];offset+=n;return v
    def vector(n):
        result=[]
        for _ in range(n):
            v=list(struct.unpack('<4I',read(16)));require(all(x<P for x in v),'joint bus noncanonical');result.append(v)
        return result
    require([read(48) for _ in spec['air']['tables']]==roots,'joint transported source roots');ars=[];finals=[]
    for table in spec['air']['tables']:ars.append(read(48).hex());finals.append(vector(bus.aux.layout(table)['finals']))
    parts=[]
    for ti,table in enumerate(spec['air']['tables']):
        n=spec['log_rows'][ti];d=bus.algebra.table_degree(table,spec['air']['numPub']);cw=4*bus.aux.layout(table)['aux_columns'];w=table['width']+cw
        rounds=[vector(d+2) for _ in range(n)]
        red=dict(current_evals=vector(w),next_evals=vector(w),rounds=[vector(3) for _ in range(n)])
        parts.append(dict(constraint_rounds=rounds,shift_reduction=red,column_claims=vector(w),openings=[None]*(2 if cw else 1)))
    require(offset==fixed,'joint fixed prefix');length=struct.unpack('<Q',read(8))[0]
    require(minimum<=length<=maximum and len(data)-offset==length,'joint opening framing')
    prefix=dict(profile=bus.PROFILE,aux_roots=ars,finals=finals,tables=parts);args=combined.arguments(prefix,spec,roots)
    if shared:
        from pq384_shared_joint_verify import verify
        return verify(read(length),args)
    opening=joint.decode(read(length),args)
    return dict(profile=combined.PROFILE,air=prefix,joint=opening)

def decode(data,spec,roots):
    return _decode(data,spec,roots,False)

def verify_shared(data,spec,roots):
    return _decode(data,spec,roots,True)

if __name__=='__main__':
    import json,sys
    from pathlib import Path
    trusted=json.loads(Path(sys.argv[2]).read_text())
    decode(Path(sys.argv[1]).read_bytes(),trusted['spec'],[bytes.fromhex(v) for v in trusted['roots']])
    print('PASS: joint full-AIR binary diagnostic; no joint soundness certification')
