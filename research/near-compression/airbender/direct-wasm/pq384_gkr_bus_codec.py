"""Complete GKR-bus diagnostic binary, all commitments and framing counted.

Circuit-derived GKR dimensions; no proof-selected points, widths, indices or
weights. Shared Merkle paths are authenticated then expanded before PCS verify.
"""
import struct
import pq384_gkr_bus as bus
import pq384_weighted_joint_codec as joint
from pq384_primitives import require,P
MAGIC=b'NPGK\x00\x01'
MAX_GKR_BYTES=64<<20


def shape(spec):
    degrees=bus.validate(spec);fixed=len(MAGIC)+48*len(degrees);dimensions=[]
    for ti,(table,d) in enumerate(zip(spec['air']['tables'],degrees)):
        n=spec['log_rows'][ti];layout=bus.aux.layout(table);cw=4*layout['aux_columns']
        fixed+=48+16*layout['finals']+16*n*(d+2)
        dimensions.append(dict(log_rows=n,width=table['width'],packing=spec['source_packings'][ti]))
        if cw:dimensions.append(dict(log_rows=n,width=cw,packing=spec['aux_packings'][ti]))
    _,minimum,maximum=joint.limits(dimensions);return fixed,minimum,maximum


def prefix(spec,roots,proof):
    st,t,alpha,gamma=bus.begin(spec,roots);ars=[bus.pcs.decode_hash(x) for x in proof['aux_roots']]
    bus.initialize_aux(t,spec,ars,proof['finals']);require(len(proof['tables'])==len(roots),'table count')
    terminals=[bus.constraint_verify(spec,t,ti,rd) for ti,rd in enumerate(proof['tables'])]
    circuit,layout,binding=bus.terminal_layout(spec,t,alpha,gamma,proof['finals'],terminals)
    sizes=[2*((layout['input_size'] if i==0 else len(layout['layers'][i-1])).bit_length()-1) for i in range(len(layout['layers'])-1,-1,-1)]
    size=16*sum(3*n+2 for n in sizes);require(size<=MAX_GKR_BYTES,'GKR codec cap')
    return st,alpha,gamma,ars,terminals,circuit,layout,binding,sizes,size


def encode(proof,spec,roots):
    require(bus.verify(proof,spec,roots),'full encoding verification');out=bytearray(MAGIC+b''.join(roots))
    def vector(values):
        for v in values:out.extend(struct.pack('<4I',*bus.ext(v)))
    for root,fs in zip(proof['aux_roots'],proof['finals']):out.extend(bus.pcs.decode_hash(root));vector(fs)
    for rounds in proof['tables']:
        for rd in rounds:vector(rd)
    fixed,_,_=shape(spec);require(len(out)==fixed,'prefix size')
    st,alpha,gamma,ars,terminals,circuit,layout,binding,sizes,size=prefix(spec,roots,proof)
    for part in proof['gkr']['layers']:
        for rd in part['rounds']:vector(rd)
        vector(part['inputs'])
    require(len(out)==fixed+size,'GKR transport size')
    ob=bus.gkr.verify(layout,binding,proof['gkr']);args=bus.opening_arguments(spec,roots,ars,terminals,circuit,ob)
    encoded=joint.encode(proof['opening'],st,bus.opening_parent(binding,proof['gkr']),args,ob['private_claim'])
    out.extend(struct.pack('<Q',len(encoded)));out.extend(encoded);return bytes(out)


def decode(data,spec,roots):
    fixed,minimum,maximum=shape(spec)
    require(type(data)is bytes and fixed+8+minimum<=len(data)<=fixed+MAX_GKR_BYTES+8+maximum,'whole size')
    require(data[:len(MAGIC)]==MAGIC,'magic');offset=len(MAGIC)
    def read(n):
        nonlocal offset
        require(offset+n<=len(data),'truncation');v=data[offset:offset+n];offset+=n;return v
    def vector(n):
        result=[]
        for _ in range(n):
            v=list(struct.unpack('<4I',read(16)));require(all(x<P for x in v),'noncanonical field');result.append(v)
        return result
    require([read(48) for _ in spec['air']['tables']]==roots,'source root binding');ars=[];finals=[]
    for table in spec['air']['tables']:ars.append(read(48).hex());finals.append(vector(bus.aux.layout(table)['finals']))
    tables=[]
    for ti,table in enumerate(spec['air']['tables']):
        d=bus.old.algebra.table_degree(table,spec['air']['numPub']);tables.append([vector(d+2) for _ in range(spec['log_rows'][ti])])
    require(offset==fixed,'prefix boundary');proof=dict(profile=bus.PROFILE,aux_roots=ars,finals=finals,tables=tables)
    st,alpha,gamma,ars,terminals,circuit,layout,binding,sizes,size=prefix(spec,roots,proof)
    require(fixed+size+8+minimum<=len(data)<=fixed+size+8+maximum,'derived GKR size')
    gp=dict(profile=bus.gkr.PROFILE.decode(),layers=[dict(rounds=[vector(3) for _ in range(n)],inputs=vector(2)) for n in sizes]);proof['gkr']=gp
    require(offset==fixed+size,'GKR boundary');length=struct.unpack('<Q',read(8))[0]
    require(minimum<=length<=maximum and len(data)-offset==length,'opening framing')
    ob=bus.gkr.verify(layout,binding,gp);args=bus.opening_arguments(spec,roots,ars,terminals,circuit,ob)
    proof['opening']=joint.decode(read(length),st,bus.opening_parent(binding,gp),args,ob['private_claim'])
    require(offset==len(data),'trailing bytes');require(bus.old.global_fingerprint_balance(spec,finals,alpha,gamma),'bus fingerprint product')
    return proof

if __name__=='__main__':
    import json,sys
    from pathlib import Path
    s=json.loads(Path(sys.argv[2]).read_text());decode(Path(sys.argv[1]).read_bytes(),s['spec'],[bytes.fromhex(x) for x in s['roots']])
    print('PASS: complete GKR-bus binary diagnostic; security not certified')
