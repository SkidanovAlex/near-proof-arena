"""Complete disclosed arithmetic trace for actual weighted PCS fold verification.

Checks all rows and all residual outputs, never a random subset/residual sum.
The transcript/terminal and Merkle verifiers remain native. This is NOT succinct
recursion. Caller-fixed PCS headers still require authenticated GKR derivation.
"""
import argparse,copy,hashlib,importlib,json,struct,sys,time
from pathlib import Path


def canonical(x):return json.dumps(x,sort_keys=True,separators=(',',':')).encode()
def require(ok,msg):
    if not ok:raise ValueError(msg)

PROFILE=b'NEAR-RECURSIVE-WEIGHTED-FOLD-TRACE-V1'


def header(session):
    return {k:session[k] for k in ('statement','parent','branches','claim')}


def canonical_value(x):
    require(type(x)is list and len(x)==4 and all(type(v)is int and 0<=v<2013265921 for v in x),'canonical Ext4 input')
    return tuple(x)


def derive_bindings(sessions):
    """Replay actual transcript+terminal and authenticate every source/next pair.

    Does not assume successful fold equations. The supplied even/odd witnesses
    are checked separately by the complete arithmetic DAG.
    """
    import pq384_weighted_joint as w
    from pq384_batched_fold import check_opening
    from check_whir_handoff import add
    from pq384_one_fold import decode_hash,ZERO,ONE
    rows=[];contexts=[]
    for ci,session in enumerate(sessions):
        require(set(session)=={'statement','parent','branches','claim','proof'},'session shape')
        proof=session['proof'];statement=bytes.fromhex(session['statement']);parent=bytes.fromhex(session['parent'])
        degrees,D,ctxs,betas,roots,fold_ctxs,challenges,samples=w.replay(proof,statement,parent,session['branches'],canonical_value(session['claim']))
        require(len(proof['queries'])==len(samples)==8,'complete query coverage')
        contexts.append({'degree':D,'rounds':len(challenges),'queries':len(samples)})
        for qi,(sample,query) in enumerate(zip(samples,proof['queries'])):
            require(set(query)=={'sources','folds'} and len(query['sources'])==len(session['branches']) and len(query['folds'])==len(challenges),'query coverage')
            a,b=ZERO,ZERO;source_refs=[]
            for bi,(op,branch,d,ctx,beta) in enumerate(zip(query['sources'],session['branches'],degrees,ctxs,betas)):
                pair=check_opening(op,decode_hash(branch['root']),ctx,2*d,sample%(2*d),True,beta)
                if d<D:pair=(pair[(sample%(4*d))//(2*d)],)*2
                a,b=add(a,pair[0]),add(b,pair[1])
                source_refs.append({'branch':bi,'root':branch['root'],'context_hex':ctx.hex(),'half':2*d,'index':sample%(2*d),'projection_side':None if d==D else (sample%(4*d))//(2*d)})
            degree=D
            for ri,(op,r) in enumerate(zip(query['folds'],challenges)):
                pair=check_opening(op,roots[ri],fold_ctxs[ri],degree,sample%degree,False,[ONE])
                require(degree>0 and degree&(degree-1)==0 and (1<<27)%(4*degree)==0,'exact power-of-two domain')
                omega=pow(440564289,(1<<27)//(4*degree),2013265921);x=pow(omega,sample%(2*degree),2013265921);side=(sample%(2*degree))//degree
                require(x!=0 and pow(omega,4*degree,2013265921)==1 and pow(omega,2*degree,2013265921)!=1,'nonzero exact-order domain point')
                provenance={'component':ci,'query_ordinal':qi,'sample':sample,'round':ri,'degree':degree,'x':x,'next_root':roots[ri].hex(),'next_context_hex':fold_ctxs[ri].hex(),'next_half':degree,'next_index':sample%degree,'next_side':side,'source':source_refs if ri==0 else {'previous_fold_row':len(rows)-1,'previous_pair_root':roots[ri-1].hex()},'challenge_slot':[ci,ri]}
                rows.append({'provenance':provenance,'a':list(a),'b':list(b),'x':[x,0,0,0],'r':list(r),'expected':list(pair[side])})
                a,b=pair;degree//=2
    return rows,contexts


def build_dag(count):
    """Seven Ext4 inputs per row: a,b,x,r,even,odd,authenticated next value."""
    require(type(count)is int and 0<count<=100000,'trace row bound')
    nodes=[['input',i] for i in range(7*count)];outputs=[]
    def emit(op,a,b):nodes.append([op,a,b]);return len(nodes)-1
    for row in range(count):
        a,b,x,r,e,o,target=range(7*row,7*row+7)
        two_e=emit('add',e,e);sum_ab=emit('add',a,b)
        even_res=emit('sub',two_e,sum_ab)
        two_x=emit('add',x,x);two_x_o=emit('mul',two_x,o);diff_ab=emit('sub',a,b)
        odd_res=emit('sub',two_x_o,diff_ab)
        diff=emit('sub',o,e);scaled=emit('mul',r,diff);folded=emit('add',e,scaled)
        fold_res=emit('sub',folded,target)
        outputs.append([even_res,odd_res,fold_res])
    return {'input_count':7*count,'nodes':nodes,'outputs':outputs,'residual_order':['2e-a-b','2xo-a+b','e+r(o-e)-next']}


def evaluate_dag(dag,values):
    from check_whir_handoff import add,sub,mul
    require(len(values)==dag['input_count'],'all operand slots present')
    vv=[canonical_value(v) for v in values];computed=[]
    for i,node in enumerate(dag['nodes']):
        require(type(node)is list and node,'node shape')
        if node[0]=='input':
            require(len(node)==2 and type(node[1])is int and 0<=node[1]<len(vv),'input slot');value=vv[node[1]]
        else:
            require(len(node)==3 and node[0] in ('add','sub','mul') and all(type(j)is int and 0<=j<i for j in node[1:]),'DAG opcode/edges')
            value={'add':add,'sub':sub,'mul':mul}[node[0]](computed[node[1]],computed[node[2]])
        computed.append(value)
    require(all(len(row)==3 for row in dag['outputs']),'residual coverage')
    for row in dag['outputs']:
        for i in row:
            require(type(i)is int and 0<=i<len(computed),'output index')
            require(computed[i]==(0,0,0,0),'nonzero arithmetic residual')
    return True


def trace_commitment(context,rows,values):
    from pq384_primitives import merkle_tree,field_words
    require(len(values)==7*len(rows),'commitment slot count')
    leaves=[]
    for i,row in enumerate(rows):
        provenance=canonical(row['provenance'])
        words=[v for item in values[7*i:7*(i+1)] for v in canonical_value(item)]
        leaves.append(struct.pack('<QQ',i,len(provenance))+provenance+field_words(words))
    require(leaves and len(leaves)&(len(leaves)-1)==0,'power-of-two row trace')
    return merkle_tree(leaves,context)[0].hex()


def context_for(headers,contexts,dag):
    from pq384_primitives import hash_parts
    return hash_parts(PROFILE,canonical(headers),canonical(contexts),canonical(dag))


def build(sessions):
    from check_whir_handoff import add,sub
    bindings,contexts=derive_bindings(sessions);values=[]
    for row in bindings:
        a,b,x=[canonical_value(row[k]) for k in ('a','b','x')]
        even=[v*pow(2,-1,2013265921)%2013265921 for v in add(a,b)]
        odd=[v*pow(2*x[0],-1,2013265921)%2013265921 for v in sub(a,b)]
        values += [row['a'],row['b'],row['x'],row['r'],even,odd,row['expected']]
    dag=build_dag(len(bindings));evaluate_dag(dag,values)
    ctx=context_for([header(s) for s in sessions],contexts,dag)
    return {'profile':PROFILE.decode(),'sessions':sessions,'contexts':contexts,'dag':dag,'rows':[r['provenance'] for r in bindings],'values':values,'trace_root':trace_commitment(ctx,bindings,values)}


def verify(artifact,expected_headers):
    require(type(artifact)is dict and set(artifact)=={'profile','sessions','contexts','dag','rows','values','trace_root'},'complete trace fields')
    require(artifact['profile']==PROFILE.decode(),'trace profile')
    require(canonical([header(s) for s in artifact['sessions']])==canonical(expected_headers),'caller-fixed PCS headers')
    bindings,contexts=derive_bindings(artifact['sessions'])
    dag=build_dag(len(bindings));require(artifact['dag']==dag,'exact complete fold DAG')
    require(artifact['contexts']==contexts and artifact['rows']==[r['provenance'] for r in bindings],'exact row/provenance coverage')
    values=artifact['values'];require(len(values)==7*len(bindings),'complete operand vector')
    for i,row in enumerate(bindings):
        for slot,key in ((0,'a'),(1,'b'),(2,'x'),(3,'r'),(6,'expected')):
            require(canonical_value(values[7*i+slot])==canonical_value(row[key]),'authenticated/replayed operand binding')
    ctx=context_for(expected_headers,contexts,dag)
    require(artifact['trace_root']==trace_commitment(ctx,bindings,values),'single complete trace commitment')
    evaluate_dag(dag,values)
    return True


def capture(results):
    import pq384_weighted_joint as w
    sessions=[]
    def observe(frame,event,arg):
        if event=='call' and frame.f_code is w.verify.__code__:
            v=frame.f_locals;sessions.append(json.loads(canonical({'statement':v['statement'].hex(),'parent':v['parent'].hex(),'branches':v['branches'],'claim':v['claim'],'proof':v['proof']})))
    for name,module in [('sha384-direct','verify_sha384_direct'),('sha384-committed-gkr','verify_sha384_committed_gkr')]:
        d=results/name;wire=(d/'proof.bin').read_bytes();statement=json.loads((d/'statement.json').read_text());receipt=json.loads((d/'expected-input.json').read_text())
        verifier=importlib.import_module(module).verify
        require(sys.getprofile() is None,'profiler occupied');sys.setprofile(observe)
        try:require(verifier(wire,statement,receipt),'actual component verifier')
        finally:sys.setprofile(None)
    require(len(sessions)==2,'exactly two complete weighted openings')
    return sessions


def main():
    p=argparse.ArgumentParser();p.add_argument('--reference-dir',required=True);p.add_argument('--results-dir',type=Path,required=True);p.add_argument('--output-dir',type=Path,required=True);a=p.parse_args();sys.path.insert(0,a.reference_dir)
    start=time.monotonic();sessions=capture(a.results_dir);capture_seconds=time.monotonic()-start
    expected=[header(s) for s in sessions];start=time.monotonic();artifact=build(sessions);build_seconds=time.monotonic()-start
    start=time.monotonic();require(verify(artifact,expected),'independent complete verifier');verify_seconds=time.monotonic()-start
    a.output_dir.mkdir(parents=True,exist_ok=True)
    (a.output_dir/'trace.json').write_bytes(canonical(artifact));(a.output_dir/'expected-headers.json').write_bytes(canonical(expected))
    report={'status':'PASS','recursive_proof':False,'components':len(sessions),'fold_rows':len(artifact['rows']),'separately_checked_ext4_residuals':3*len(artifact['rows']),'base_field_equalities':12*len(artifact['rows']),'committed_ext4_slots':len(artifact['values']),'dag_nodes':len(artifact['dag']['nodes']),'trace_bytes':(a.output_dir/'trace.json').stat().st_size,'expected_header_bytes':(a.output_dir/'expected-headers.json').stat().st_size,'trace_root':artifact['trace_root'],'capture_seconds':capture_seconds,'build_seconds':build_seconds,'verify_seconds':verify_seconds,'limits':['All fold checks covered; no residual aggregation or subset sampling.','Trace fully disclosed and original PCS transcript/Merkle routines run natively; no succinct outer proof.','Caller-fixed PCS headers must still be derived from authenticated GKR and source statements; capture performs that derivation through original wrappers.','Source virtual batching, transcript rejection/terminal, geometry and Merkle authentication are native boundaries, not proved by this DAG.','No zero knowledge, commitment-binding proof, certified QROM or quantum128 security.']}
    (a.output_dir/'report.json').write_text(json.dumps(report,indent=2));print(json.dumps(report,indent=2))
if __name__=='__main__':main()
