#!/usr/bin/env python3
"""Independent verifier for the fixed eight-row WHIR opening experiment only.

No witness/codeword input. No GKR, recursion, ZK or security-level claim.
This experimental implementation has not been formally verified or audited.
"""
import json,hashlib,struct,sys
from pathlib import Path
from copy import deepcopy
from check_whir_handoff import P,INV_R,ZERO,ONE,add,sub,mul
from check_commitment import words

def require(b,label):
    if not b:raise ValueError(label)
def raw(e):
    require(isinstance(e,dict) and set(e)=={'c0','c1'},'extension shape')
    for c in ('c0','c1'):require(isinstance(e[c],dict) and set(e[c])=={'c0','c1'},'quadratic shape')
    v=[e['c0']['c0'],e['c0']['c1'],e['c1']['c0'],e['c1']['c1']]
    require(all(type(x)is int and 0<=x<P for x in v),'canonical field')
    return v
def ext(e):
    v=raw(e);return tuple(v[i]*INV_R%P for i in (0,2,1,3))
def base(n):return(n%P,0,0,0)
def scale(a,n):return tuple(x*n%P for x in a)
def eq(a,b):return add(mul(a,b),mul(sub(ONE,a),sub(ONE,b)))
def poly(cs,x):
    a=ZERO
    for c in cs[::-1]:a=add(mul(a,x),c)
    return a
def digest(data):return hashlib.blake2s(data).digest()
def root(n):return pow(440564289,2**(27-n),P)
class Transcript:
    def __init__(self,statement):self.seed=digest(words(statement))
    def commit(self,data):self.seed=digest(self.seed+words(data))
    def commit_ext(self,es):self.commit([v for e in es for v in raw(e)])
    def draw(self,n,fresh=False):
        if fresh:self.seed=digest(self.seed)
        out=[]
        for i in range((4*n+7)//8):
            if i:self.seed=digest(self.seed)
            out.extend(struct.unpack('<8I',self.seed))
        return [tuple(out[4*i+j]%P*INV_R%P for j in (0,2,1,3)) for i in range(n)]
    def queries(self,nonce,bits):
        require(type(nonce)is int and 0<=nonce<2**64,'nonce')
        self.seed=digest(self.seed+struct.pack('<Q',nonce))
        # Both fixed rounds need <=32 query bits. Skip first PoW word.
        stream=struct.unpack('<8I',self.seed)[1]
        return [(stream>>(bits*i))&((1<<bits)-1) for i in range(8)]
def merkle(payload,index,path,cap,depth):
    require(type(index)is int and 0<=index<2**depth and len(path)==depth,'Merkle geometry')
    require(len(cap)==8,'cap length');h=digest(words(payload))
    for sibling in path:
        require(len(sibling)==8,'sibling length');s=words(sibling)
        h=digest(s+h if index&1 else h+s);index>>=1
    require(h==words(cap),'Merkle inclusion')
def tree_index(query,poly_log):
    coset=query%4;return (((coset&1)<<1)|(coset>>1))*2**(poly_log-1)+query//4
SCHEDULE={'base_lde_factor':4,'cap_size':1,'whir_steps_schedule':[1,1],
          'whir_queries_schedule':[8,8],'whir_steps_lde_factors':[4],'whir_pow_schedule':[0,0]}
def verify(x,expected_root):
    return _verify_with_handoff(x,expected_root,None)

def _verify_with_handoff(x,expected_root,handoff,width=104):
    require(type(width)is int and width>0,'expected column width')
    p=x['proof'];require(p['whir_schedule']==SCHEDULE,'unsupported schedule')
    wit=p['witness_commitment'];require(wit['num_columns']==width and len(wit['evals'])==width,'column shape')
    require(wit['commitment']['cap']['cap']==[expected_root],'root binding')
    for name in ('memory_commitment','setup_commitment'):
        a=p[name];require(a['num_columns']==0 and a['evals']==[] and a['queries']==[] and a['commitment']['cap']['cap']==[],'unexpected auxiliary oracle')
    if handoff is None:
        require(width==104,'standalone profile width')
        statement=list(b'NEAR-WHIR-OPENING-EXPERIMENT-V1')+[8,104,4,1,1,2,1,1,8,8,4,0,0]+expected_root
        require(x['statement_words']==statement,'statement encoding')
        t=Transcript(statement);z=t.draw(3,True)
    else:
        # Internal entry: caller must derive both from a verified prior protocol.
        # This is not exposed as a CLI option or accepted as proof metadata.
        t,z=handoff

    require([ext(v) for v in x['evaluation_point']]==z,'point draw')
    require([ext(v) for v in p['original_evaluation_point']]==z,'point binding')
    t.commit_ext(wit['evals']);batch=t.draw(1,True)[0]
    require(ext(p['batching_challenge'])==batch,'batch draw')
    require(words(x['initial_whir_seed'])==t.seed,'initial seed')
    claim=ZERO;power=ONE
    for v in wit['evals']:claim=add(claim,mul(power,ext(v)));power=mul(power,batch)
    require(ext(p['batched_opening'])==claim,'batch claim')
    require(len(p['sumcheck_polys'])==2 and all(len(c)==3 for c in p['sumcheck_polys']),'sumcheck shape')
    require(len(p['ood_samples'])==1 and len(p['pow_nonces'])==2,'round shape')
    require(len(p['intermediate_whir_oracles'])==1,'oracle shape')
    def sumcheck(i,claim):
        enc=p['sumcheck_polys'][i];cs=[ext(c) for c in enc]
        require(add(poly(cs,ZERO),poly(cs,ONE))==claim,'sumcheck identity')
        t.commit_ext(enc);r=t.draw(1)[0]
        return r,poly(cs,r)
    r0,claim=sumcheck(0,claim)
    mid=p['intermediate_whir_oracles'][0];caps=mid['commitment']['cap']['cap']
    require(len(caps)==1 and len(caps[0])==8,'intermediate cap');t.commit(caps[0])
    ood=t.draw(1)[0];oodvalue=ext(p['ood_samples'][0]);t.commit_ext(p['ood_samples'])
    indices=t.queries(p['pow_nonces'][0],4);gamma=t.draw(1,True)[0]
    claim=add(claim,mul(gamma,oodvalue));power=mul(gamma,gamma)
    terms=[(ood,gamma)]
    require(len(wit['queries'])==8,'base query count')
    for index,q in zip(indices,wit['queries']):
        require(q['index']==tree_index(index,3),'base query index')
        values=q['leaf_values_concatenated'];require(len(values)==2*width,'base leaf width')
        require(all(type(v)is int and 0<=v<P for v in values),'base leaf field')
        merkle([values[o*width+c] for c in range(width) for o in range(2)],q['index'],q['path'],expected_root,4)
        ys=[]
        for o in range(2):
            acc=ZERO;b=ONE
            for v in values[o*width:(o+1)*width]:acc=add(acc,scale(b,v*INV_R%P));b=mul(b,batch)
            ys.append(acc)
        # Recover even/odd univariate parts from evaluations at t,-t.
        inv=pow(pow(root(5),index,P),-1,P)
        folded=add(scale(add(*ys),pow(2,-1,P)),mul(r0,scale(sub(*ys),inv*pow(2,-1,P)%P)))
        point=base(pow(root(4),index,P));terms.append((point,power))
        claim=add(claim,mul(power,folded));power=mul(power,gamma)
    r1,claim=sumcheck(1,claim)
    final=p['final_monomials'];require(len(final)==2,'final polynomial degree')
    cs=[ext(c) for c in final];t.commit_ext(final)
    indices=t.queries(p['pow_nonces'][1],3)
    require(len(mid['queries'])==8,'final query count')
    for index,q in zip(indices,mid['queries']):
        require(q['index']==tree_index(index,2),'final query index')
        es=q['leaf_values_concatenated'];require(len(es)==2,'intermediate leaf width')
        merkle([w for e in es for w in raw(e)],q['index'],q['path'],caps[0],3)
        folded=add(ext(es[0]),mul(r1,ext(es[1])))
        require(folded==poly(cs,base(pow(root(3),index,P))),'final query fold')
    # Explicit final sumcheck after two LSB folds. Only one variable remains.
    total=ZERO
    for b in (ZERO,ONE):
        weight=mul(mul(eq(z[0],r0),eq(z[1],r1)),eq(z[2],b))
        for point,power in terms:weight=add(weight,mul(power,mul(eq(point,r1),eq(mul(point,point),b))))
        total=add(total,mul(poly(cs,b),weight))
    require(total==claim,'final sumcheck')
    return True

def main():
    artifact,commitment,report=map(Path,sys.argv[1:]);x=json.loads(artifact.read_text());cap=json.loads(commitment.read_text())['root']
    verify(x,cap)
    result={'status':'PASS','fixed_profile_whir_verified':True,'witness_used':False,
            'profile':'8 rows, 104 columns, folds [1,1], queries [8,8], no grinding',
            'limitations':['Experimental fixed-profile verifier, not formally verified or security-audited.','No security-level claim for toy parameters.','No GKR constraint proof or NEAR state-transition proof.']}
    report.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
if __name__=='__main__':main()
