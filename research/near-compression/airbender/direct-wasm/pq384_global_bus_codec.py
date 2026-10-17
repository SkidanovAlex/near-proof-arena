"""Complete bus diagnostic binary; fixed AIR shapes, authenticated PCS branches.

External spec/source roots are trusted inputs. All source roots are also
transported in the binary and checked against caller roots; their bytes count. Lengths frame PCS bytes only and
are bounded before slicing. Decode verifies local relations and fingerprint
product equality; natural balance/security remain conditional as in protocol.
"""
import struct
import pq384_global_bus as bus
import pq384_global_codec as pcs
from pq384_primitives import require,P
MAGIC=b'NPGB\x00\x03'

def max_size(spec):
    degrees=bus.validate(spec);total=len(MAGIC)+48*len(spec['air']['tables'])
    for ti,(table,d) in enumerate(zip(spec['air']['tables'],degrees)):
        layout=bus.aux.layout(table);n=spec['log_rows'][ti];sw=table['width'];cw=4*layout['aux_columns']
        total+=48+16*layout['finals']+16*(n*(d+2)+3*(sw+cw)+3*n)
        for width,key in [(sw,'source_packings'),(cw,'aux_packings')]:
            if not width:continue
            packing=spec[key][ti];D=(1<<n)*packing;terminal=spec['terminal_degree'];rounds=D.bit_length()-terminal.bit_length()
            total+=8+len(pcs.MAGIC)+96*rounds+16*terminal
            for j in range(rounds+1):
                words=2*((width+packing-1)//packing) if j==0 else 8
                total+=pcs.gc.QUERIES*(4*words+48*((2*D).bit_length()-1));D//=2
    return total

def encode(proof,spec,roots):
    require(type(proof)is dict and set(proof)=={'profile','aux_roots','finals','tables'} and proof['profile']==bus.PROFILE,'bus codec fields')
    st,t,alpha,gamma=bus.begin(spec,roots);ars=[pcs.gc.decode_hash(v) for v in proof['aux_roots']]
    bus.initialize_aux(t,spec,ars,proof['finals']);out=bytearray(MAGIC+b''.join(roots))
    def vector(values,count):
        require(isinstance(values,list) and len(values)==count,'bus codec vector')
        for value in values:
            v=bus.ext(value);out.extend(struct.pack('<4I',*v))
    for root,fs in zip(ars,proof['finals']):out.extend(root);vector(fs,len(fs))
    require(isinstance(proof['tables'],list) and len(proof['tables'])==len(roots),'bus codec tables')
    for ti,part in enumerate(proof['tables']):
        argslist=bus.verify_table_reduction(part,spec,st,t,alpha,gamma,ti,proof['finals'][ti],[roots[ti],ars[ti]])
        table=spec['air']['tables'][ti];n=spec['log_rows'][ti];d=bus.algebra.table_degree(table,spec['air']['numPub']);w=table['width']+4*bus.aux.layout(table)['aux_columns']
        for rd in part['constraint_rounds']:vector(rd,d+2)
        red=part['shift_reduction'];vector(red['current_evals'],w);vector(red['next_evals'],w)
        for rd in red['rounds']:vector(rd,3)
        vector(part['column_claims'],w)
        for opening,args in zip(part['openings'],argslist):
            encoded=pcs.encode(opening,terminal_degree=spec['terminal_degree'],**args)
            out.extend(struct.pack('<Q',len(encoded)));out.extend(encoded)
    require(bus.global_fingerprint_balance(spec,proof['finals'],alpha,gamma),'bus codec global fingerprint equality')
    require(len(out)<=max_size(spec),'bus codec maximum');return bytes(out)

def _decode(data,spec,roots,shared):
    maximum=max_size(spec);require(type(data)is bytes and len(MAGIC)<=len(data)<=maximum,'bus codec size')
    require(data[:len(MAGIC)]==MAGIC,'bus codec magic');offset=len(MAGIC)
    def read(n):
        nonlocal offset
        require(offset+n<=len(data),'bus codec truncation');v=data[offset:offset+n];offset+=n;return v
    def vector(count):
        result=[]
        for _ in range(count):
            v=list(struct.unpack('<4I',read(16)));require(all(x<P for x in v),'bus codec noncanonical field');result.append(v)
        return result
    st,t,alpha,gamma=bus.begin(spec,roots)
    require([read(48) for _ in roots]==roots,'transported source commitments')
    ars=[];finals=[]
    for table in spec['air']['tables']:ars.append(read(48));finals.append(vector(bus.aux.layout(table)['finals']))
    bus.initialize_aux(t,spec,ars,finals);parts=[]
    for ti,table in enumerate(spec['air']['tables']):
        n=spec['log_rows'][ti];d=bus.algebra.table_degree(table,spec['air']['numPub']);cw=4*bus.aux.layout(table)['aux_columns'];w=table['width']+cw
        rounds=[vector(d+2) for _ in range(n)]
        red=dict(current_evals=vector(w),next_evals=vector(w),rounds=[vector(3) for _ in range(n)])
        part=dict(constraint_rounds=rounds,shift_reduction=red,column_claims=vector(w),openings=[None]*(2 if cw else 1))
        argslist=bus.verify_table_reduction(part,spec,st,t,alpha,gamma,ti,finals[ti],[roots[ti],ars[ti]])
        for branch,args in enumerate(argslist):
            length=struct.unpack('<Q',read(8))[0];_,minimum,limit=pcs.limits(args,spec['terminal_degree'])
            require(minimum<=length<=limit,'PCS branch length')
            branch_wire=read(length)
            if shared:
                from pq384_shared_global_verify import verify
                require(verify(branch_wire,terminal_degree=spec['terminal_degree'],**args),'shared PCS rejected')
            else:
                part['openings'][branch]=pcs.decode(branch_wire,terminal_degree=spec['terminal_degree'],**args)
        parts.append(part)
    require(offset==len(data),'bus codec trailing bytes')
    require(bus.global_fingerprint_balance(spec,finals,alpha,gamma),'bus codec global fingerprint equality')
    if shared:return True
    return dict(profile=bus.PROFILE,aux_roots=[v.hex() for v in ars],finals=finals,tables=parts)

def decode(data,spec,roots):
    return _decode(data,spec,roots,False)

def verify_shared(data,spec,roots):
    """Full AIR/bus binary verification with mandatory shared PCS authentication."""
    return _decode(data,spec,roots,True)

if __name__=='__main__':
    import json,sys
    from pathlib import Path
    trusted=json.loads(Path(sys.argv[2]).read_text())
    decode(Path(sys.argv[1]).read_bytes(),trusted['spec'],[bytes.fromhex(v) for v in trusted['roots']])
    print('PASS: complete AIR and randomized bus-fingerprint binary diagnostic')
