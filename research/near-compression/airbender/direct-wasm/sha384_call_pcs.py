"""Call-link GKR/PCS on the SAME use root; Q8/Ext4 diagnostic only.
No disclosed rows enter verification. External call operands remain trusted.
"""
import json,struct
import pq384_terminal_gkr as g
import pq384_weighted_joint as pcs
import pq384_weighted_joint_codec as codec
from pq384_primitives import Transcript,hash_parts,require,P
from verify_sha384_node_chunk import contract,canonical
from certify_sha384_occurrence_chains import IV
PROFILE=b'near-sha384-call-link-pcs-v1'
MAGIC=b'NPCALL01'


def equations(statement,expected,calls):
    contract(statement,expected);spec=statement['spec'];n=1<<spec['log_rows'][3]
    require(n<=128 and type(calls)is list and calls,'bounded call profile')
    eq=[];coverage=[]
    def constant(row,col,value):eq.append((row+n*col,None,value))
    def same(row,col,other,othercol):eq.append((row+n*col,other+n*othercol,0))
    def limbs(raw):
        return [(int.from_bytes(raw[i:i+8],'big')>>(16*j))&65535 for i in range(0,len(raw),8) for j in range(4)]
    for call in calls:
        require(type(call)is dict and set(call)=={'message_hex','ordinals','digest_hex'},'external call fields')
        message=bytes.fromhex(call['message_hex']);digest=bytes.fromhex(call['digest_hex']);ids=call['ordinals']
        require(len(digest)==48 and type(ids)is list and ids and all(type(i)is int and 0<=i<expected['use_count'] for i in ids),'call bounds')
        padded=message+b'\x80'+b'\0'*((111-len(message))%128)+(8*len(message)).to_bytes(16,'big')
        require(len(padded)==128*len(ids),'canonical padded block count')
        for step,row in enumerate(ids):
            for j in range(32):
                if step==0:constant(row,3+j,limbs(IV)[j])
                else:same(row,3+j,ids[step-1],99+j)
            for j,value in enumerate(limbs(padded[128*step:128*(step+1)])):constant(row,35+j,value)
        for j,value in enumerate(digest):constant(ids[-1],131+j,value)
        coverage+=ids
    require(coverage==list(range(expected['use_count'])),'exact ordered coverage')
    return eq


def compile_layout(statement,expected,calls):
    eq=equations(statement,expected,calls);spec=statement['spec'];n=1<<spec['log_rows'][3];capacity=n*256
    st=hash_parts(PROFILE,canonical(expected),canonical(calls),canonical(spec),bytes.fromhex(statement['roots'][3]))
    t=Transcript(st);point=[tuple(x) for x in t.draw(b'call-equations-after-use-root',(len(eq)-1).bit_length(),4)[0]]
    coeff=[g.ZERO]*capacity;claim=g.ZERO
    for (left,right,value),w in zip(eq,g.eqs(point)):
        coeff[left]=g.add(coeff[left],w)
        if right is not None:coeff[right]=g.sub(coeff[right],w)
        claim=g.add(claim,g.mul(w,g.base(value)))
    nodes=[['input',i] for i in range(capacity)];terms=[]
    def emit(node):nodes.append(node);return len(nodes)-1
    for i,w in enumerate(coeff):
        if w!=g.ZERO:terms.append(emit(['mul',i,emit(['const',*w])]))
    while len(terms)>1:terms=[emit(['add',terms[i],terms[i+1]]) if i+1<len(terms) else terms[i] for i in range(0,len(terms),2)]
    root=emit(['sub',terms[0],emit(['const',*claim])]);live=set();todo=[root]
    while todo:
        i=todo.pop()
        if i in live:continue
        live.add(i)
        if nodes[i][0] in ('add','sub','mul'):todo.extend(nodes[i][1:])
    layout=g.layer_circuit(dict(nodes=nodes,live_nodes=sorted(live),private_input_capacity=capacity,root=root))
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


def prove(rows,statement,expected,calls,cache,native,kernel):
    layout,st,binding,eq=compile_layout(statement,expected,calls);n=1<<statement['spec']['log_rows'][3]
    require(len(rows)==n and all(len(r)==179 and all(type(x)is int and 0<=x<P for x in r) for r in rows),'source rows')
    private=[g.base(rows[r][c]) if c<179 else g.ZERO for c in range(256) for r in range(n)]
    require(all(g.sub(private[a],private[b] if b is not None else g.base(value))==g.ZERO for a,b,value in eq),'honest equation parity')
    gp,ob=g.prove(layout,binding,private,kernel=kernel);bs=branches(statement,ob)
    got=g.ZERO
    for b in bs:
        columns=[w for lane in b['lanes'] for w in lane[0]][:179]
        for c,w in enumerate(columns):got=g.add(got,g.mul(w,g.mle([g.base(row[c]) for row in rows],b['row_point'])))
    require(got==ob['private_claim'],'source-slot/PCS functional parity')
    opening=pcs.prove([cache,cache],native,st,parent(binding,gp),bs,ob['private_claim'])
    return dict(gkr=gp,opening=opening)


def verify(proof,statement,expected,calls):
    require(type(proof)is dict and set(proof)=={'gkr','opening'},'proof fields')
    layout,st,binding,_=compile_layout(statement,expected,calls)
    ob=g.verify(layout,binding,proof['gkr'])
    pcs.verify(proof['opening'],st,parent(binding,proof['gkr']),branches(statement,ob),ob['private_claim'])
    return True


def encode(proof,statement,expected,calls):
    verify(proof,statement,expected,calls)
    layout,st,binding,_=compile_layout(statement,expected,calls);gp=proof['gkr'];ob=g.verify(layout,binding,gp)
    data=bytearray(MAGIC)
    for layer in gp['layers']:
        for value in [v for row in layer['rounds'] for v in row]+layer['inputs']:data+=struct.pack('<4I',*g.ext(value))
    data+=codec.encode(proof['opening'],st,parent(binding,gp),branches(statement,ob),ob['private_claim'])
    return bytes(data)


def decode(wire,statement,expected,calls):
    require(type(wire)is bytes and len(wire)<=2**20 and wire[:8]==MAGIC,'call proof framing')
    layout,st,binding,_=compile_layout(statement,expected,calls);offset=8;layers=[]
    def scalar():
        nonlocal offset
        require(offset+16<=len(wire),'truncated GKR');v=list(g.ext(struct.unpack_from('<4I',wire,offset)));offset+=16;return v
    for i in range(len(layout['layers'])-1,-1,-1):
        prev=layout['input_size'] if i==0 else len(layout['layers'][i-1]);rounds=2*(prev.bit_length()-1)
        layers.append(dict(rounds=[[scalar() for _ in range(3)] for _ in range(rounds)],inputs=[scalar(),scalar()]))
    gp=dict(profile=g.PROFILE.decode(),layers=layers);ob=g.verify(layout,binding,gp)
    opening=codec.decode(wire[offset:],st,parent(binding,gp),branches(statement,ob),ob['private_claim'])
    return dict(gkr=gp,opening=opening)
