"""Lossless compact wire for the SAME GKR-bus profile and transcript.

Only deterministic redundancy removed; no new security parameters or queries.
All commitments, framing and bit-padding canonicality remain checked.
"""
import struct
import pq384_gkr_bus_codec as original
import pq384_compact_weighted_codec as compact
from pq384_primitives import require
bus=original.bus
MAGIC=b'NPGC\x00\x01'
FIXED_MAGIC=b'NPGF\x00\x01'

def wire_magic(input_log):
    bus.profile(input_log)
    return MAGIC if input_log is None else FIXED_MAGIC


def encode(proof,spec,roots, *, input_log=None):
    require(bus.verify(proof,spec,roots,input_log=input_log),'complete proof');out=compact.Writer();out.raw(wire_magic(input_log)+b''.join(roots))
    for root,fs in zip(proof['aux_roots'],proof['finals']):out.raw(bus.pcs.decode_hash(root));out.vector(fs)
    for rounds in proof['tables']:
        for row in rounds:out.vector([row[0]]+row[2:])
    out.align()
    for layer in proof['gkr']['layers']:
        for row in layer['rounds']:out.vector([row[0],row[2]])
        out.vector(layer['inputs'])
    out.align()
    st,alpha,gamma,ars,terminals,circuit,layout,binding,sizes,size=original.prefix(spec,roots,proof,input_log=input_log)
    ob=bus.gkr.verify(layout,binding,proof['gkr']);args=bus.opening_arguments(spec,roots,ars,terminals,circuit,ob)
    opening=compact.encode(proof['opening'],st,bus.opening_parent(binding,proof['gkr']),args,ob['private_claim'])
    out.raw(struct.pack('<Q',len(opening)));out.raw(opening);return out.finish()


def decode(data,spec,roots, *, input_log=None):
    magic=wire_magic(input_log)
    fixed,_,maximum=original.shape(spec)
    require(type(data)is bytes and len(MAGIC)+48*len(roots)<=len(data)<=fixed+original.MAX_GKR_BYTES+8+maximum,'compact size')
    rd=compact.Reader(data);require(rd.raw(len(magic))==magic,'compact magic');require([rd.raw(48) for _ in spec['air']['tables']]==roots,'source roots')
    st,t,alpha,gamma=bus.begin(spec,roots,input_log=input_log);ars=[];finals=[]
    for table in spec['air']['tables']:ars.append(rd.raw(48));finals.append(rd.vector(bus.aux.layout(table)['finals']))
    bus.initialize_aux(t,spec,ars,finals);tables=[];terminals=[]
    for ti,table in enumerate(spec['air']['tables']):
        n=spec['log_rows'][ti];d=bus.old.algebra.table_degree(table,spec['air']['numPub']);mixing,tau=bus.old.table_start(t,ti,n);point=[];claim=bus.ZERO;rounds=[]
        for _ in range(n):
            row=compact.recover(rd.vector(d+1),claim);t.commit_ext(row);r=t.draw(1,True)[0];point.append(r);claim=bus.poly([bus.ext(x) for x in row],r);rounds.append(row)
        tables.append(rounds);terminals.append(dict(point=point,mixing=mixing,tau=tau,claim=claim))
    rd.align();circuit,layout,binding=bus.terminal_layout(spec,t,alpha,gamma,finals,terminals,input_log=input_log)
    sizes=[2*((layout['input_size'] if i==0 else len(layout['layers'][i-1])).bit_length()-1) for i in range(len(layout['layers'])-1,-1,-1)]
    require(16*sum(3*n+2 for n in sizes)<=original.MAX_GKR_BYTES,'GKR cap');gt=bus.gkr.begin(layout,binding,bus.ZERO);claim=bus.ZERO;layers=[]
    for n in sizes:
        rounds=[]
        for _ in range(n):
            row=compact.recover(rd.vector(2),claim);bus.gkr.commit(gt,row);r=bus.gkr.draw(gt);claim=bus.poly([bus.ext(x) for x in row],r);rounds.append(row)
        inputs=rd.vector(2);bus.gkr.commit(gt,inputs);gamma_gkr=bus.gkr.draw(gt);claim=bus.add(bus.ext(inputs[0]),bus.gkr.mul(gamma_gkr,bus.ext(inputs[1])));layers.append(dict(rounds=rounds,inputs=inputs))
    rd.align();gp=dict(profile=bus.gkr.PROFILE.decode(),layers=layers);ob=bus.gkr.verify(layout,binding,gp)
    args=bus.opening_arguments(spec,roots,ars,terminals,circuit,ob);length=struct.unpack('<Q',rd.raw(8))[0]
    require(len(compact.MAGIC)<=length<=maximum and len(data)-rd.offset==length,'compact opening framing')
    opening=compact.decode(rd.raw(length),st,bus.opening_parent(binding,gp),args,ob['private_claim']);rd.finish()
    require(bus.old.global_fingerprint_balance(spec,finals,alpha,gamma),'bus product')
    return dict(profile=bus.profile(input_log),aux_roots=[r.hex() for r in ars],finals=finals,tables=tables,gkr=gp,opening=opening)

if __name__=='__main__':
    import json,sys
    from pathlib import Path
    s=json.loads(Path(sys.argv[2]).read_text());decode(Path(sys.argv[1]).read_bytes(),s['spec'],[bytes.fromhex(x) for x in s['roots']])
    print('PASS: exact original GKR-bus proof reconstructed and verified; diagnostic security only')
