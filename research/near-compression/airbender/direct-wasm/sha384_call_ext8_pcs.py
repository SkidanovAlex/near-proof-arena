"""Ext8 call-link GKR/PCS on the same use root, with an explicit query budget.
This is an experimental profile, not a PQ128 certificate.
No disclosed rows enter verification. External call operands remain trusted.
"""
import json,struct
import pq384_ext8_terminal_gkr as g
import pq384_ext8_weighted as pcs
import pq384_ext8_weighted_codec as codec
from pq384_primitives import Transcript,hash_parts,require,P,u64
from verify_sha384_node_chunk import contract,canonical
from certify_sha384_occurrence_chains import IV
PROFILE=b'near-sha384-call-link-ext8-pcs-v1'
MAGIC=b'NPCL8001'


from sha384_call_pcs import equations


def compile_coefficients(eq,weights,capacity):
    coeff=[g.ZERO]*capacity;claim=g.ZERO
    for (left,right,value),w in zip(eq,weights):
        coeff[left]=g.add(coeff[left],w)
        if right is not None:coeff[right]=g.sub(coeff[right],w)
        claim=g.add(claim,g.mul(w,g.base(value)))
    return coeff,claim


def compile_dag(coeff,claim,capacity):
    nodes=[['input',i] for i in range(capacity)];terms=[]
    def emit(node):nodes.append(node);return len(nodes)-1
    for i,w in enumerate(coeff):
        if w!=g.ZERO:terms.append(emit(['mul',i,emit(['const',*w])]))
    while len(terms)>1:terms=[emit(['add',terms[i],terms[i+1]]) if i+1<len(terms) else terms[i] for i in range(0,len(terms),2)]
    total=terms[0] if terms else emit(['const',*g.ZERO])
    root=emit(['sub',total,emit(['const',*claim])]);live=set();todo=[root]
    while todo:
        i=todo.pop()
        if i in live:continue
        live.add(i)
        if nodes[i][0] in ('add','sub','mul'):todo.extend(nodes[i][1:])
    return dict(nodes=nodes,live_nodes=sorted(live),private_input_capacity=capacity,root=root)


def compile_layout(statement,expected,calls, *, queries=309):
    require(type(queries)is int and 1<=queries<=4096,'query budget')
    eq=equations(statement,expected,calls);spec=statement['spec'];n=1<<spec['log_rows'][3];capacity=n*256
    st=hash_parts(PROFILE,u64(queries),canonical(expected),canonical(calls),canonical(spec),bytes.fromhex(statement['roots'][3]))
    t=Transcript(st);point=[tuple(x) for x in t.draw(b'call-equations-after-use-root',(len(eq)-1).bit_length(),8)[0]]
    coeff,claim=compile_coefficients(eq,g.eqs(point),capacity)
    layout=g.layer_circuit(compile_dag(coeff,claim,capacity))
    return layout,st,t.seed,eq


def branches(statement,ob):
    spec=statement['spec'];log=spec['log_rows'][3];packing=spec['source_packings'][3];result=[]
    for point,scale in ob['queries']:
        require(len(point)>=log+8,'complete input dimensions')
        columns=[]
        for col in range(179):
            weight=scale
            for bit,r in enumerate(point[log:]):weight=g.mul(weight,r if (col>>bit)&1 else g.sub(g.ONE,r))
            columns.append(weight)
        lanes=[([columns[c] if c<179 else g.ZERO for c in range(j,j+packing)],[g.ZERO]*packing) for j in range(0,179,packing)]
        result.append(dict(root=statement['roots'][3],log_rows=log,width=179,packing=packing,row_point=point[:log],lanes=lanes))
    require(len(result)==2,'two input queries')
    return result


def parent(binding,proof):return hash_parts(PROFILE,binding,canonical(proof))


def prove(rows,statement,expected,calls,cache,native,kernel, *, queries=309):
    layout,st,binding,eq=compile_layout(statement,expected,calls,queries=queries);n=1<<statement['spec']['log_rows'][3]
    require(len(rows)==n and all(len(r)==179 and all(type(x)is int and 0<=x<P for x in r) for r in rows),'source rows')
    private=[g.base(rows[r][c]) if c<179 else g.ZERO for c in range(256) for r in range(n)]
    require(all(g.sub(private[a],private[b] if b is not None else g.base(value))==g.ZERO for a,b,value in eq),'honest equation parity')
    gp,ob=g.prove(layout,binding,private,kernel=kernel);bs=branches(statement,ob)
    got=g.ZERO
    for b in bs:
        columns=[w for lane in b['lanes'] for w in lane[0]][:179]
        for c,w in enumerate(columns):got=g.add(got,g.mul(w,g.mle([g.base(row[c]) for row in rows],b['row_point'])))
    require(got==ob['private_claim'],'source-slot/PCS functional parity')
    opening=pcs.prove([cache,cache],native,st,parent(binding,gp),bs,ob['private_claim'],queries=queries)
    return dict(gkr=gp,opening=opening)


def verify(proof,statement,expected,calls, *, queries=309):
    require(type(proof)is dict and set(proof)=={'gkr','opening'},'proof fields')
    layout,st,binding,_=compile_layout(statement,expected,calls,queries=queries)
    ob=g.verify(layout,binding,proof['gkr'])
    pcs.verify(proof['opening'],st,parent(binding,proof['gkr']),branches(statement,ob),ob['private_claim'],queries=queries)
    return True


def encode(proof,statement,expected,calls, *, queries=309):
    verify(proof,statement,expected,calls,queries=queries)
    layout,st,binding,_=compile_layout(statement,expected,calls,queries=queries);gp=proof['gkr'];ob=g.verify(layout,binding,gp)
    data=bytearray(MAGIC)
    for layer in gp['layers']:
        for value in [v for row in layer['rounds'] for v in row]+layer['inputs']:data+=struct.pack('<8I',*g.ext(value))
    data+=codec.encode(proof['opening'],st,parent(binding,gp),branches(statement,ob),ob['private_claim'],queries=queries)
    return bytes(data)


def decode(wire,statement,expected,calls, *, queries=309):
    require(type(wire)is bytes and len(wire)<=2**24 and wire[:8]==MAGIC,'call proof framing')
    layout,st,binding,_=compile_layout(statement,expected,calls,queries=queries);offset=8;layers=[]
    def scalar():
        nonlocal offset
        require(offset+32<=len(wire),'truncated GKR');v=list(g.ext(struct.unpack_from('<8I',wire,offset)));offset+=32;return v
    for i in range(len(layout['layers'])-1,-1,-1):
        prev=layout['input_size'] if i==0 else len(layout['layers'][i-1]);rounds=2*(prev.bit_length()-1)
        layers.append(dict(rounds=[[scalar() for _ in range(3)] for _ in range(rounds)],inputs=[scalar(),scalar()]))
    gp=dict(profile=g.PROFILE.decode(),layers=layers);ob=g.verify(layout,binding,gp)
    opening=codec.decode(wire[offset:],st,parent(binding,gp),branches(statement,ob),ob['private_claim'],queries=queries)
    return dict(gkr=gp,opening=opening)
