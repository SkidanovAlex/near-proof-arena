"""New configured conjunction GKR + actual packed terminal-functional PCS.

Core verifier has no operand vector/disclosed dot-product. End-to-end binding
still uses native provenance and independently reconstructs the RS root from the
full trace: merely hashing old trace root + RS root is NOT a linking proof.
"""
import argparse,contextlib,json,subprocess,sys,time
from pathlib import Path
import recursive_fold_trace as fold
import recursive_source_batch_trace as source
import recursive_conjunction_gkr as legacy

PROFILE=b'NEAR-RECURSIVE-PACKED-PCS-CONJUNCTION-V1'
LOG_ROWS=12
WIDTH=16
PACKING=16
CAPACITY=16384


def pack_inputs(artifact):
    from check_whir_handoff import ZERO
    values=[fold.canonical_value(v) for v in artifact['fold']['values']+artifact['source_values']]
    fold.require(0<len(values)<=CAPACITY,'fixed private capacity')
    private=values+[ZERO]*(CAPACITY-len(values))
    rows=[[private[r+(1<<LOG_ROWS)*group][coordinate] for group in range(4) for coordinate in range(4)] for r in range(1<<LOG_ROWS)]
    return private,rows


def independent_rs_root(rows):
    """Independent Python lower Mobius + base FFT + exact SHA384 leaf order."""
    from pq384_primitives import P,merkle_tree,field_words
    from packed_claim_handoff import packing_context
    fold.require(len(rows)==1<<LOG_ROWS and all(len(r)==WIDTH for r in rows),'packing shape')
    c=[rows[r][column] for column in range(WIDTH) for r in range(1<<LOG_ROWS)]
    fold.require(all(type(v)is int and 0<=v<P for v in c),'base coordinate canonicality')
    bit=1
    while bit<len(c):
        for i in range(len(c)):
            if i&bit:c[i]=(c[i]-c[i^bit])%P
        bit*=2
    n=4*len(c);v=c+[0]*(n-len(c));j=0
    for i in range(1,n):
        bit=n>>1
        while j&bit:j^=bit;bit>>=1
        j^=bit
        if i<j:v[i],v[j]=v[j],v[i]
    omega=pow(440564289,(1<<27)//n,P);size=2
    while size<=n:
        step=pow(omega,n//size,P)
        for start in range(0,n,size):
            power=1
            for k in range(start,start+size//2):
                u=v[k];b=v[k+size//2]*power%P;v[k]=(u+b)%P;v[k+size//2]=(u-b)%P;power=power*step%P
        size*=2
    leaves=[field_words([v[i],v[i+n//2]]) for i in range(n//2)]
    return merkle_tree(leaves,packing_context(LOG_ROWS,WIDTH,PACKING))[0].hex()


def dependency(artifact,root):
    return {'trace_root':artifact['combined_root'],'rs_root':root,'fold_dag':artifact['fold']['dag'],'source_dag':artifact['source_dag'],'input_count':len(artifact['fold']['values'])+len(artifact['source_values']),'log_rows':LOG_ROWS,'width':WIDTH,'packing':PACKING,'capacity':CAPACITY}


def linked_dependency(artifact,headers,root):
    legacy.bind_without_residual_checks(artifact,headers)
    _,rows=pack_inputs(artifact)
    fold.require(independent_rs_root(rows)==root,'RS commitment must match same bound trace operands')
    return dependency(artifact,root)


def statement(dep):
    from pq384_primitives import hash_parts
    import recursive_configured_gkr_engine as engine
    fold.require(set(dep)=={'trace_root','rs_root','fold_dag','source_dag','input_count','log_rows','width','packing','capacity'},'dependency fields')
    fold.require((dep['log_rows'],dep['width'],dep['packing'],dep['capacity'])==(LOG_ROWS,WIDTH,PACKING,CAPACITY),'fixed packing/slot profile')
    fold.require(dep['input_count']==dep['fold_dag']['input_count']+dep['source_dag']['input_count']<=CAPACITY,'complete input dimensions')
    fold.require(all(type(dep[k])is str and len(bytes.fromhex(dep[k]))==48 for k in ('trace_root','rs_root')),'both commitment roots')
    return hash_parts(PROFILE,engine.CONFIG,fold.canonical(dep))


def compile_layout(dep):
    from pq384_primitives import Transcript
    import recursive_configured_gkr_engine as g
    st=statement(dep);count=sum(map(len,dep['fold_dag']['outputs']))+sum(map(len,dep['source_dag']['outputs']));dimension=(count-1).bit_length()
    t=Transcript(st);draws,_=t.draw(b'complete-output-point-after-both-roots',dimension,4);point=[tuple(x) for x in draws]
    nodes=[['input',i] for i in range(dep['input_count'])];outputs=[];offset=0
    def emit(node):nodes.append(node);return len(nodes)-1
    for dag in (dep['fold_dag'],dep['source_dag']):
        mapping=[]
        for node in dag['nodes']:
            if node[0]=='input':mapping.append(offset+node[1])
            elif node[0]=='const':mapping.append(emit(node))
            else:mapping.append(emit([node[0],mapping[node[1]],mapping[node[2]]]))
        outputs += [mapping[i] for row in dag['outputs'] for i in row];offset+=dag['input_count']
    weights=g.eqs(point);terms=[emit(['mul',output,emit(['const',*weight])]) for output,weight in zip(outputs,weights)]
    fold.require(len(outputs)==count and count>0,'all residual outputs')
    while len(terms)>1:terms=[emit(['add',terms[i],terms[i+1]]) if i+1<len(terms) else terms[i] for i in range(0,len(terms),2)]
    root=terms[0];live=set();todo=[root]
    while todo:
        i=todo.pop()
        if i in live:continue
        live.add(i)
        if nodes[i][0] in ('add','sub','mul'):todo.extend(nodes[i][1:])
    circuit={'nodes':nodes,'live_nodes':sorted(live),'private_input_capacity':CAPACITY,'root':root}
    return g.layer_circuit(circuit),t.seed,st,point


def branches(dep,obligation):
    """Exact low-row/high-group decomposition of GKR input MLE queries.

    Each Ext4 slot becomes four base columns with [1,v,v²,v³] multipliers;
    input bits above private capacity are fixed zero, not dropped.
    """
    import recursive_configured_gkr_engine as g
    result=[]
    for point,scale in obligation['queries']:
        fold.require(len(point)>=14,'GKR input dimension')
        columns=[]
        for group in range(4):
            weight=scale
            for bit,r in enumerate(point[LOG_ROWS:]):weight=g.mul(weight,r if (group>>bit)&1 else g.sub(g.ONE,r))
            for coordinate in range(4):columns.append(g.mul(weight,tuple(int(i==coordinate) for i in range(4))))
        result.append({'root':dep['rs_root'],'log_rows':LOG_ROWS,'width':WIDTH,'packing':PACKING,'row_point':point[:LOG_ROWS],'lanes':[[columns,[g.ZERO]*WIDTH]]})
    fold.require(len(result)==2,'two GKR terminal queries')
    return result


def verify_core(proof,dep):
    """Caller supplies a VERIFIED linked dependency, never a proof-selected one."""
    import recursive_configured_gkr_engine as g
    import pq384_derived_weight_joint as pcs
    fold.require(set(proof)=={'profile','rs_root','trace_root','gkr','opening'} and proof['profile']==PROFILE.decode(),'outer proof fields')
    fold.require(proof['rs_root']==dep['rs_root'] and proof['trace_root']==dep['trace_root'],'root dependency binding')
    layout,binding,st,_=compile_layout(dep);ob=g.verify(layout,binding,proof['gkr'])
    pcs.verify(proof['opening'],st,ob['transcript_seed'],branches(dep,ob),ob['private_claim'])
    return True


def verify_bound(proof,artifact,headers):
    dep=linked_dependency(artifact,headers,proof['rs_root'])
    return verify_core(proof,dep)


def main():
    p=argparse.ArgumentParser();p.add_argument('--reference-dir',required=True);p.add_argument('--trace-directory',type=Path,required=True);p.add_argument('--headers',type=Path,required=True);p.add_argument('--rs-binary',required=True);p.add_argument('--fft-library',required=True);p.add_argument('--output-directory',type=Path,required=True);a=p.parse_args();sys.path.insert(0,a.reference_dir)
    import recursive_configured_gkr_engine as g
    import pq384_derived_weight_joint as pcs
    from pq384_source_cache import SourceCache
    from pq384_native_fft import NativeFFT
    artifact=json.loads((a.trace_directory/'trace.json').read_text());headers=json.loads(a.headers.read_text());private,rows=pack_inputs(artifact);out=a.output_directory;out.mkdir(parents=True,exist_ok=True);cache=out/'source-cache'
    request=out/'commit-input.json';request.write_bytes(fold.canonical({'rows':rows,'packing':PACKING,'indices':[],'cache_directory':str(cache)}));start=time.monotonic();subprocess.run([a.rs_binary,str(request),str(out/'commit-output.json')],check=True,capture_output=True);commit_seconds=time.monotonic()-start
    root=json.loads((cache/'manifest.json').read_text())['root_hex'];start=time.monotonic();dep=linked_dependency(artifact,headers,root);link_seconds=time.monotonic()-start
    layout,binding,st,point=compile_layout(dep);start=time.monotonic();gp,ob=g.prove(layout,binding,private);gkr_seconds=time.monotonic()-start
    bs=branches(dep,ob)
    # Independent direct row-MLE check for the coordinate packing map before PCS.
    got=g.ZERO
    for b in bs:
        columns=b['lanes'][0][0]
        for col,weight in enumerate(columns):got=g.add(got,g.mul(weight,g.mle([g.base(row[col]) for row in rows],b['row_point'])))
    fold.require(got==ob['private_claim'],'exact packed coordinate functional')
    start=time.monotonic()
    with SourceCache(cache,expected_root=bytes.fromhex(root),log_rows=LOG_ROWS,width=WIDTH,packing=PACKING) as data:
        opening=pcs.prove([data,data],NativeFFT(a.fft_library),st,ob['transcript_seed'],bs,ob['private_claim'])
    pcs_seconds=time.monotonic()-start;proof={'profile':PROFILE.decode(),'rs_root':root,'trace_root':dep['trace_root'],'gkr':gp,'opening':opening}
    start=time.monotonic();fold.require(verify_core(proof,dep),'actual packed PCS verifier');verify_seconds=time.monotonic()-start
    (out/'proof.json').write_bytes(fold.canonical(proof));(out/'verified-dependency.json').write_bytes(fold.canonical(dep))
    report={'status':'PASS','complete_recursive_proof':False,'profile':PROFILE.decode(),'compiler_config':g.CONFIG.decode(),'rs_root':root,'trace_root':dep['trace_root'],'rows':len(rows),'width':WIDTH,'packing':PACKING,'degree':len(rows)*PACKING,'input_slots':len(private),'gkr_proof_json_bytes':len(fold.canonical(gp)),'pcs_proof_json_bytes':len(fold.canonical(opening)),'proof_json_bytes':(out/'proof.json').stat().st_size,'verified_dependency_json_bytes':(out/'verified-dependency.json').stat().st_size,'commit_seconds':commit_seconds,'independent_full_root_link_seconds':link_seconds,'gkr_prover_seconds':gkr_seconds,'pcs_prover_seconds':pcs_seconds,'core_verify_seconds':verify_seconds,'full_trace_disclosure_needed_for_native_root_link':True,'limits':['Actual packed PCS replaces disclosed terminal dot-product in core verifier.','Verified dependency MUST come from native root-link/provenance check; hashing roots together does not establish equal committed data.','End-to-end wrapper still needs full3.70MB trace for root link/native header/hash binding; proof payload alone is not complete recursive compression.','New configured GKR transcript and compiler CONFIG; no legacy proof relabeling.','Q8/Ext4 diagnostic; no PQ128,QROM,proximity or zero-knowledge certification.']}
    (out/'report.json').write_text(json.dumps(report,indent=2));print(json.dumps(report,indent=2))
if __name__=='__main__':main()
