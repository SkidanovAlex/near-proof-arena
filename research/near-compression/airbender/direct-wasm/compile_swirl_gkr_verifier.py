"""Fixed-layout Ext4 arithmetic verifier; transcript/PCS obligations stay external.

Inputs are never frozen to the honest proof. All endpoint/wiring equalities are
outputs, not assertions executed during compilation. Not a recursive proof.
"""
import collections
import gzip
import hashlib
import json
import types
from pathlib import Path
import pq384_terminal_gkr as g
from prove_swirl_root_public_dag import context, OUT as GKR
from prove_swirl_weighted_dag import split_obligation

OUT=GKR.parent/'compiled-gkr-verifier'


class Circuit:
    def __init__(self):
        self.nodes=[]
        self.index={}
        self.inputs=[]
        self.zero=self.const(g.ZERO)
        self.one=self.const(g.ONE)

    def intern(self,key):
        if key not in self.index:
            self.index[key]=len(self.nodes)
            self.nodes.append(key)
        return self.index[key]

    def const(self,x):return self.intern(('const',*x))
    def inp(self,name):
        assert name not in self.inputs
        self.inputs.append(name)
        return self.intern(('input',name))
    def op(self,op,a,b):
        if op=='add':
            if a==self.zero:return b
            if b==self.zero:return a
        if op=='sub' and b==self.zero:return a
        if op=='sub' and a==b:return self.zero
        if op=='mul':
            if self.zero in (a,b):return self.zero
            if a==self.one:return b
            if b==self.one:return a
        if op in ('add','mul') and a>b:a,b=b,a
        if self.nodes[a][0]==self.nodes[b][0]=='const':
            return self.const(g.gate(op,self.nodes[a][1:],self.nodes[b][1:]))
        return self.intern((op,a,b))
    def add(self,a,b):return self.op('add',a,b)
    def sub(self,a,b):return self.op('sub',a,b)
    def mul(self,a,b):return self.op('mul',a,b)
    def eqs(self,point):
        out=[self.one]
        for r in point:
            comp=self.sub(self.one,r)
            out=[self.mul(x,comp) for x in out]+[self.mul(x,r) for x in out]
        return out
    def weights(self,n,queries):
        out=[self.zero]*n
        for point,scale in queries:
            eq=self.eqs(point)
            assert len(eq)==n
            out=[self.add(x,self.mul(scale,y)) for x,y in zip(out,eq)]
        return out
    def sum(self,terms):
        terms=list(terms)
        if not terms:return self.zero
        while len(terms)>1:
            terms=[self.add(terms[i],terms[i+1]) if i+1<len(terms) else terms[i]
                   for i in range(0,len(terms),2)]
        return terms[0]
    def evaluate(self,inputs):
        assert set(inputs)==set(self.inputs)
        values=[]
        for node in self.nodes:
            op=node[0]
            if op=='const':v=tuple(node[1:])
            elif op=='input':v=tuple(inputs[node[1]])
            else:v=g.gate(op,values[node[1]],values[node[2]])
            values.append(v)
        return values


def compile_verifier(layout,slots,known_slots,wiring_kind=None):
    c=Circuit();checks=[];claim=c.inp('claim')
    n=(len(layout['layers'][-1])-1).bit_length()
    queries=[([c.const(g.base((layout['root']>>i)&1)) for i in range(n)],c.one)]
    for k,layer in enumerate(range(len(layout['layers'])-1,-1,-1)):
        gates=layout['layers'][layer]
        if wiring_kind is None:w=c.weights(len(gates),queries)
        prev=layout['input_size'] if layer==0 else len(layout['layers'][layer-1])
        m=(prev-1).bit_length();point=[]
        for j in range(2*m):
            a,b,d=[c.inp(f'proof/{k}/round/{j}/{i}') for i in range(3)]
            checks.append(c.sub(c.add(c.add(a,a),c.add(b,d)),claim))
            r=c.inp(f'challenge/{k}/{j}');point.append(r)
            claim=c.add(a,c.mul(r,c.add(b,c.mul(r,d))))
        a,b=[c.inp(f'proof/{k}/input/{i}') for i in range(2)]
        if wiring_kind is None:
            eu,ev=c.eqs(point[:m]),c.eqs(point[m:])
            # Group by operation before multiplying by layer input values.
            # This preserves sum w*eq_u*eq_v*op(a,b) by distributivity.
            coeff={op:[] for op in ('add','sub','mul')}
            for (op,i,j),weight in zip(gates,w):
                coeff[op].append(c.mul(weight,c.mul(eu[i],ev[j])))
            ans=c.zero
            for op in coeff:ans=c.add(ans,c.mul(c.sum(coeff[op]),c.op(op,a,b)))
        else:
            from swirl_wiring_bdd import wiring
            ans=wiring(c,gates,queries,point[:m],point[m:],a,b,wiring_kind)
        checks.append(c.sub(ans,claim))
        gamma=c.inp(f'challenge/{k}/gamma')
        claim=c.add(a,c.mul(gamma,b));queries=[(point[:m],c.one),(point[m:],gamma)]
    weights=c.weights(layout['input_size'],queries)
    terms=[c.mul(weights[i],c.const(v)) for i,v in layout['constants'].items()]
    terms.extend(c.mul(weights[i],c.inp(f'known/{i}')) for i in sorted(known_slots))
    claim=c.sub(claim,c.sum(terms))
    pcs=[(i,weights[i]) for key,i in sorted(slots.items(),key=lambda x:x[1]) if key[0]=='variable']
    assert set(known_slots).isdisjoint(i for i,_ in pcs)
    return c,checks,claim,pcs


def main(wiring_kind=None,output_dir=OUT):
    OUT=output_dir
    layout,slots,known,claim,statement,_=context()
    proof=json.loads(gzip.decompress((GKR/'proof.json.gz').read_bytes()))
    draws=[]
    def draw(t):
        x=g.draw(t);draws.append(x);return x
    # Clone verifier globals to capture the actual authenticated challenge order.
    verify=types.FunctionType(g.verify.__code__,dict(g.verify.__globals__,draw=draw),argdefs=g.verify.__defaults__)
    ob=verify(layout,statement,proof,claim)
    expected=split_obligation(ob,slots,known)
    c,checks,residual,pcs=compile_verifier(layout,slots,set(known),wiring_kind)
    inputs={'claim':claim,**{f'known/{i}':v for i,v in known.items()}}
    cursor=0
    for k,part in enumerate(proof['layers']):
        for j,row in enumerate(part['rounds']):
            for i,v in enumerate(row):inputs[f'proof/{k}/round/{j}/{i}']=v
            inputs[f'challenge/{k}/{j}']=draws[cursor];cursor+=1
        for i,v in enumerate(part['inputs']):inputs[f'proof/{k}/input/{i}']=v
        inputs[f'challenge/{k}/gamma']=draws[cursor];cursor+=1
    assert cursor==len(draws)
    values=c.evaluate(inputs)
    assert all(values[i]==g.ZERO for i in checks)
    assert values[residual]==expected['claim']
    assert [(i,values[w]) for i,w in pcs]==[(x['slot'],x['weight']) for x in expected['coordinates']]
    negatives=[]
    for key in ['claim','proof/0/round/0/0','proof/0/input/0','challenge/0/0']:
        altered=inputs.copy();altered[key]=g.add(tuple(altered[key]),g.ONE)
        vs=c.evaluate(altered)
        assert any(vs[i]!=g.ZERO for i in checks)
        negatives.append(key)
    # Known values belong to the PCS residual, not GKR endpoint equalities.
    key=next(f'known/{i}' for i in known if ob['private_weights'][i]!=g.ZERO)
    altered=inputs.copy();altered[key]=g.add(tuple(altered[key]),g.ONE)
    vs=c.evaluate(altered)
    assert all(vs[i]==g.ZERO for i in checks) and vs[residual]!=values[residual]
    depths=[]
    for node in c.nodes:depths.append(0 if node[0] in ('input','const') else 1+max(depths[node[1]],depths[node[2]]))
    artifact=dict(nodes=c.nodes,checks=checks,residual=residual,pcs=pcs,inputs=c.inputs)
    raw=json.dumps(artifact,separators=(',',':')).encode()
    OUT.mkdir(exist_ok=True)
    (OUT/'circuit.json.gz').write_bytes(gzip.compress(raw,mtime=0))
    report=dict(status='FIXED_GKR_ARITHMETIC_PARITY',wiring_kind=wiring_kind,nodes=len(c.nodes),operations=dict(collections.Counter(x[0] for x in c.nodes)),
        max_depth=max(depths),inputs=len(c.inputs),equality_checks=len(checks),pcs_coordinates=len(pcs),
        challenge_inputs=len(draws),negative_checks=negatives,known_mutation_changes_residual=True,
        circuit_sha256=hashlib.sha256(raw).hexdigest(),
        limitations=['Ext4 arithmetic DAG, not generated recursive proof or base-field AIR.',
                     'Transcript challenge derivation/hash binding remains external.',
                     'Known input derivation, prefix verification and weighted PCS remain external.',
                     'No Lean compiler refinement, soundness composition, PQ128 or full NEAR claim.'])
    paths=[Path(__file__),Path(g.__file__),GKR/'proof.json.gz',GKR.parent/'root-split-witness/public-controls.json']
    if wiring_kind is not None:paths.append(Path(__file__).with_name('swirl_wiring_bdd.py'))
    report['sha256']={str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
    (OUT/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(report)


if __name__=='__main__':main()
