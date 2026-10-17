"""Canonical table-local AIR → cyclic shift → SHA384 packed opening diagnostic.

Complete executable table-local relation, not cross-table bus balance/HoldsP.
Q8/Ext4 remains diagnostic: no 128-bit, QROM, proximity or ZK certification.
Verifier accepts no witness and derives opening point/parent binding itself.
"""
import itertools,json
import pq384_global_chain as pcs
import pq384_batched_fold as source_pcs
from pq384_primitives import Transcript,require,hash_parts
from packed_claim_handoff import packing_context,vector_bytes,canonical_ext as ext
from table_constraint_whir import evaluate,selectors
from reference import schema,expr_degree
from verify_whir_toy import P,ZERO,ONE,base,add,mul,poly
from check_whir_handoff import mle
import pq384_shift as shift

PROFILE='near-pq384-global-table-local-v1'

def constraints(table):
    return table['constraints']+[['*',b,['+',b,['-',['c',1]]]]
            for i in table['interactions'] for b in i['mult']]

def validate(spec):
    require(type(spec)is dict and set(spec)=={'air','table_index','public','log_rows','packing','terminal_degree'},'spec fields')
    require(type(spec['terminal_degree'])is int and spec['terminal_degree'] in (1,64),'terminal profile')
    air=spec['air'];schema(air);i=spec['table_index'];n=spec['log_rows']
    require(type(i)is int and 0<=i<len(air['tables']),'table index');table=air['tables'][i]
    require(type(n)is int and 1<=n<=13 and n<=table['maxLog'] and table['width']>0,'table shape')
    require(isinstance(spec['public'],list) and all(type(v)is int and 0<=v<P for v in spec['public']),'public field')
    packing_context(n,table['width'],spec['packing'])
    d=(1<<n)*spec['packing']
    require(128<=d<=262144 and (table['width']+spec['packing']-1)//spec['packing']<=64,'PCS shape')
    degree=max([expr_degree(e,table['width'],air['numPub']) for e in constraints(table)],default=0)
    require(degree<=16,'constraint degree cap');return table,degree

class AirTranscript:
    """Only pure algebra helpers consume this adapter; every hash is SHA384."""
    def __init__(self,statement):self.t=Transcript(statement)
    @property
    def seed(self):return self.t.seed
    def commit_ext(self,values):
        self.t.commit(b'air-extension-vector',vector_bytes([ext(v) for v in values]))
    def draw(self,count,extension):
        require(extension is True,'extension challenge')
        values,_=self.t.draw(b'air-algebra-challenge',count,4)
        return [tuple(v) for v in values]

def begin(spec,root):
    table,degree=validate(spec)
    require(type(root)is bytes and len(root)==48,'root encoding')
    statement=json.dumps({'profile':PROFILE,'spec':spec},sort_keys=True,separators=(',',':')).encode()
    t=AirTranscript(statement);t.t.commit(b'source-packed-root',root)
    t.t.commit(b'source-packing-context',packing_context(spec['log_rows'],table['width'],spec['packing']))
    mixing=t.draw(1,True)[0];tau=t.draw(spec['log_rows'],True)
    return statement,t,mixing,tau

def weighted(spec,mixing,tau,point,current,nxt):
    table=spec['air']['tables'][spec['table_index']];sels=selectors(point);total=ZERO;power=ONE
    for e in constraints(table):
        total=add(total,mul(power,evaluate(e,current,nxt,spec['public'],sels)));power=mul(power,mixing)
    return mul(shift.eq_point(tau,point),total)

def handoff(spec,root,statement,t,point,claims):
    table,_=validate(spec)
    parent=hash_parts(b'global-table-local-packed-opening-branch',t.seed,
                      spec['table_index'].to_bytes(8,'little'),b'original-source')
    return dict(statement=statement,parent_binding=parent,expected_root=root,
                log_rows=spec['log_rows'],width=table['width'],packing=spec['packing'],
                row_point=point,column_claims=claims)

def source_commitment(rows,spec):
    table,_=validate(spec);n=1<<spec['log_rows'];width=table['width'];packing=spec['packing'];degree=n*packing
    require(isinstance(rows,list) and len(rows)==n and all(isinstance(row,list) and len(row)==width
            and all(type(v)is int and 0<=v<P for v in row) for row in rows),'witness shape')
    matrices=[]
    for lane in range((width+packing-1)//packing):
        cs=[rows[r][lane*packing+c] if lane*packing+c<width else 0 for c in range(packing) for r in range(n)]
        bit=1
        while bit<degree:
            for i in range(degree):
                if i&bit:cs[i]=(cs[i]-cs[i^bit])%P
            bit*=2
        matrices.append([base(v) for v in cs])
    return source_pcs.source_tree(matrices,packing_context(spec['log_rows'],width,packing))[0]

def prove(spec,root,rows):
    table,degree=validate(spec);n=spec['log_rows'];width=table['width']
    require(source_commitment(rows,spec)==root,'source commitment')
    statement,t,mixing,tau=begin(spec,root);point=[];rounds=[];nextrows=rows[1:]+rows[:1]
    for i in range(n):
        values=[]
        for node in range(degree+2):
            total=ZERO
            for suffix in itertools.product((ZERO,ONE),repeat=n-i-1):
                at=point+[base(node)]+list(suffix)
                current=[mle([row[c] for row in rows],at) for c in range(width)]
                nxt=[mle([row[c] for row in nextrows],at) for c in range(width)]
                total=add(total,weighted(spec,mixing,tau,at,current,nxt))
            values.append(total)
        cs=[list(v) for v in shift.interpolate(values)];rounds.append(cs)
        t.commit_ext(cs);point.append(t.draw(1,True)[0])
    reduction,at,claims=shift.prove(rows,point,t)
    args=handoff(spec,root,statement,t,at,claims)
    return dict(profile=PROFILE,constraint_rounds=rounds,shift_reduction=reduction,
                column_claims=[list(v) for v in claims],opening=prove_opening(rows,spec,**args))

def verify_reduction(proof,spec,root):
    table,degree=validate(spec);n=spec['log_rows'];width=table['width']
    require(type(proof)is dict and set(proof)=={'profile','constraint_rounds','shift_reduction','column_claims','opening'}
            and proof['profile']==PROFILE,'proof fields')
    statement,t,mixing,tau=begin(spec,root);point=[];claim=ZERO
    require(isinstance(proof['constraint_rounds'],list) and len(proof['constraint_rounds'])==n,'round count')
    for encoded in proof['constraint_rounds']:
        require(isinstance(encoded,list) and len(encoded)==degree+2,'round degree');cs=[ext(v) for v in encoded]
        require(add(poly(cs,ZERO),poly(cs,ONE))==claim,'AIR zerocheck')
        t.commit_ext(encoded);r=t.draw(1,True)[0];point.append(r);claim=poly(cs,r)
    red=proof['shift_reduction']
    require(type(red)is dict and set(red)=={'current_evals','next_evals','rounds'},'shift fields')
    require(len(red['current_evals'])==len(red['next_evals'])==width,'terminal width')
    current=[ext(v) for v in red['current_evals']];nxt=[ext(v) for v in red['next_evals']]
    require(claim==weighted(spec,mixing,tau,point,current,nxt),'AIR terminal')
    claims=proof['column_claims'];require(isinstance(claims,list) and len(claims)==width,'opening claims')
    for value in claims:ext(value)
    at=shift.verify(red,point,width,t,claims)
    return handoff(spec,root,statement,t,at,claims)

def verify_table_local(proof,spec,root):
    args=verify_reduction(proof,spec,root)
    return pcs.verify(proof['opening'],terminal_degree=spec['terminal_degree'],**args)

def prove_opening(rows,spec,**args):
    """Small reference source construction; no persistent cache required."""
    from array import array
    from pq384_native_fft import NativeFFT
    import os
    n=len(rows);width=len(rows[0]);packing=spec['packing'];degree=n*packing;matrices=[]
    for lane in range((width+packing-1)//packing):
        cs=[rows[r][lane*packing+c] if lane*packing+c<width else 0 for c in range(packing) for r in range(n)]
        bit=1
        while bit<degree:
            for i in range(degree):
                if i&bit:cs[i]=(cs[i]-cs[i^bit])%P
            bit*=2
        matrices.append([base(v) for v in cs])
    ctx=packing_context(spec['log_rows'],width,packing)
    root,layers,leaves=source_pcs.source_tree(matrices,ctx)
    class Cache:
        def coefficients(self,lane):return array('I',(v[0] for v in matrices[lane]))
        def opening(self,i):return source_pcs.opening(layers,leaves,i)
    cache=Cache();cache.root=root;cache.context=ctx;cache.degree=degree;cache.lanes=len(matrices)
    return pcs.prove_cached(cache,NativeFFT(os.environ['NEAR_PQ384_FFT_LIB']),terminal_degree=spec['terminal_degree'],**args)

if __name__=='__main__':
    import sys
    from pathlib import Path
    artifact=json.loads(Path(sys.argv[1]).read_text())
    assert verify_table_local(artifact['proof'],artifact['spec'],bytes.fromhex(artifact['root']))
    print('PASS: SHA384 canonical AIR table-local opening diagnostic')
