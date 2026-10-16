"""One RS source binds every arithmetic slot, including native-derived operands.

No trace or trace-to-RS linking disclosure is a verifier input. Original inner
proofs/statements remain required for native transcript/GKR/hash authentication.
Q8/Ext4 diagnostic, not complete recursion or certified PQ128.
"""
import argparse,json,subprocess,sys,time
from pathlib import Path
import recursive_fold_trace as f
import recursive_source_batch_trace as source
import recursive_gkr_header_binding as header
import recursive_pcs_conjunction as packing
PROFILE=b'NEAR-RECURSIVE-SINGLE-RS-CONJUNCTION-V1'


def derive_components(proofs,statements):
    f.require(type(proofs)is list and type(statements)is list and len(proofs)==len(statements)==2,'exact two original components')
    f.require([len(s['roots']) for s in statements]==[3,4] and statements[0]['roots']==statements[1]['roots'][:3],'three shared component source roots')
    sessions=[]
    for proof,statement in zip(proofs,statements):
        h=header.derive(proof,statement);sessions.append(dict(h,proof=proof['opening']))
    return derive_sessions(sessions)


def derive_sessions(sessions):
    """Internal: sessions MUST come from derive_components, not a public header."""
    rows,contexts=f.derive_bindings(sessions);fd=f.build_dag(len(rows));values=[];fixed=[]
    for row in rows:
        base=len(values);values += [row['a'],row['b'],row['x'],row['r'],[0]*4,[0]*4,row['expected']]
        fixed += [[base+slot,values[base+slot]] for slot in (0,1,2,3,6)]
    sd,sv,provenance=source.derive(sessions,{'rows':[r['provenance'] for r in rows],'values':values})
    fixed += [[len(values)+i,v] for i,v in enumerate(sv)]
    dep={'fold_dag':fd,'source_dag':sd,'fixed':fixed,'input_count':len(values)+len(sv),'contexts':contexts,'fold_provenance':[r['provenance'] for r in rows],'source_provenance':provenance}
    f.require(dep['input_count']<=packing.CAPACITY,'fixed capacity')
    return dep,values+sv


def honest_private(dep,values):
    from check_whir_handoff import add,sub,ZERO
    result=[f.canonical_value(v) for v in values]
    for i in range(dep['fold_dag']['input_count']//7):
        k=7*i;a,b,x=result[k:k+3]
        result[k+4]=tuple(v*pow(2,-1,2013265921)%2013265921 for v in add(a,b))
        result[k+5]=tuple(v*pow(2*x[0],-1,2013265921)%2013265921 for v in sub(a,b))
    return result+[ZERO]*(packing.CAPACITY-len(result))


def source_rows(private):
    f.require(len(private)==packing.CAPACITY,'private capacity')
    return [[private[r+4096*group][coord] for group in range(4) for coord in range(4)] for r in range(4096)]


def statement(dep,root):
    from pq384_primitives import hash_parts
    import recursive_single_root_gkr_engine as g
    f.require(type(root)is str and len(bytes.fromhex(root))==48,'RS root')
    return hash_parts(PROFILE,g.CONFIG,bytes.fromhex(root),f.canonical(dep))


def compile_layout(dep,root):
    from pq384_primitives import Transcript
    import recursive_single_root_gkr_engine as g
    # All data here is native-derived. No certificate-selected count, position,
    # DAG or expected value is accepted at the public verifier entry point.
    count=sum(map(len,dep['fold_dag']['outputs']))+sum(map(len,dep['source_dag']['outputs']))+len(dep['fixed'])
    st=statement(dep,root);t=Transcript(st);draws,_=t.draw(b'all-arithmetic-and-fixed-slot-outputs', (count-1).bit_length(),4);point=[tuple(x) for x in draws]
    nodes=[['input',i] for i in range(dep['input_count'])];outputs=[];offset=0
    def emit(node):nodes.append(node);return len(nodes)-1
    for dag in (dep['fold_dag'],dep['source_dag']):
        mapping=[]
        for n in dag['nodes']:
            if n[0]=='input':mapping.append(offset+n[1])
            elif n[0]=='const':mapping.append(emit(n))
            else:mapping.append(emit([n[0],mapping[n[1]],mapping[n[2]]]))
        outputs += [mapping[i] for row in dag['outputs'] for i in row];offset+=dag['input_count']
    fixed_ids=[v[0] for v in dep['fixed']]
    free={7*i+j for i in range(dep['fold_dag']['input_count']//7) for j in (4,5)}
    f.require(fixed_ids==[i for i in range(dep['input_count']) if i not in free],'exact fixed slots/order, only e/o free')
    for slot,value in dep['fixed']:
        f.canonical_value(value);outputs.append(emit(['sub',slot,emit(['const',*value])]))
    f.require(len(outputs)==count,'all output coverage')
    terms=[emit(['mul',idx,emit(['const',*weight])]) for idx,weight in zip(outputs,g.eqs(point))]
    while len(terms)>1:terms=[emit(['add',terms[i],terms[i+1]]) if i+1<len(terms) else terms[i] for i in range(0,len(terms),2)]
    rootnode=terms[0];live=set();todo=[rootnode]
    while todo:
        i=todo.pop()
        if i in live:continue
        live.add(i)
        if nodes[i][0] in ('add','sub','mul'):todo.extend(nodes[i][1:])
    layout=g.layer_circuit({'nodes':nodes,'live_nodes':sorted(live),'private_input_capacity':packing.CAPACITY,'root':rootnode})
    return layout,t.seed,st,{'residuals':count,'fixed_slots':len(dep['fixed']),'free_slots':len(free),'output_coordinates':len(point),'nodes':len(nodes)}


def verify_derived(proof,dep):
    """Internal trusted derivation boundary. Public API is verify below."""
    import recursive_single_root_gkr_engine as g
    import pq384_derived_weight_joint as pcs
    f.require(type(proof)is dict and set(proof)=={'profile','rs_root','gkr','opening'} and proof['profile']==PROFILE.decode(),'single-root proof fields')
    layout,binding,st,_=compile_layout(dep,proof['rs_root']);ob=g.verify(layout,binding,proof['gkr'])
    pcs.verify(proof['opening'],st,ob['transcript_seed'],packing.branches({'rs_root':proof['rs_root']},ob),ob['private_claim'])
    return True


def verify(proof,inner_proofs,trusted_statements):
    dep,_=derive_components(inner_proofs,trusted_statements)
    return verify_derived(proof,dep)


def main():
    p=argparse.ArgumentParser();p.add_argument('--reference-dir',required=True);p.add_argument('--results-dir',type=Path,required=True);p.add_argument('--output-directory',type=Path,required=True);p.add_argument('--rs-binary',required=True);p.add_argument('--fft-library',required=True);a=p.parse_args();sys.path.insert(1,a.reference_dir)
    import recursive_single_root_gkr_engine as g
    import pq384_derived_weight_joint as pcs
    from pq384_source_cache import SourceCache
    from pq384_native_fft import NativeFFT
    inner_paths=[Path('/tmp/near-sha384-direct-proof/proof.json'),Path('/tmp/near-sha384-committed-gkr-proof/proof.json')]
    statement_paths=[a.results_dir/name/'statement.json' for name in ('sha384-direct','sha384-committed-gkr')]
    proofs=[json.loads(x.read_text()) for x in inner_paths];statements=[json.loads(x.read_text()) for x in statement_paths];start=time.monotonic();dep,values=derive_components(proofs,statements);derive_seconds=time.monotonic()-start
    private=honest_private(dep,values);rows=source_rows(private);out=a.output_directory;out.mkdir(parents=True,exist_ok=True);cache=out/'source-cache';request=out/'commit-input.json';request.write_bytes(f.canonical({'rows':rows,'packing':16,'indices':[],'cache_directory':str(cache)}));subprocess.run([a.rs_binary,str(request),str(out/'commit-output.json')],check=True,capture_output=True);root=json.loads((cache/'manifest.json').read_text())['root_hex']
    # Honest-prover parity only; NOT invoked or assumed by verifier.
    f.require(packing.independent_rs_root(rows)==root,'honest source packing/native parity')
    layout,binding,st,meta=compile_layout(dep,root);start=time.monotonic();gp,ob=g.prove(layout,binding,private);gkr_seconds=time.monotonic()-start;bs=packing.branches({'rs_root':root},ob)
    start=time.monotonic()
    with SourceCache(cache,expected_root=bytes.fromhex(root),log_rows=12,width=16,packing=16) as data:opening=pcs.prove([data,data],NativeFFT(a.fft_library),st,ob['transcript_seed'],bs,ob['private_claim'])
    pcs_seconds=time.monotonic()-start;proof={'profile':PROFILE.decode(),'rs_root':root,'gkr':gp,'opening':opening};start=time.monotonic();assert verify_derived(proof,dep);core_seconds=time.monotonic()-start
    (out/'proof.json').write_bytes(f.canonical(proof));(out/'derived-dependency.json').write_bytes(f.canonical(dep))
    meta.update({'status':'PASS','complete_recursive_proof':False,'profile':PROFILE.decode(),'proof_json_bytes':len(f.canonical(proof)),'required_additional_metadata_bytes':0,'derived_dependency_cache_bytes':len(f.canonical(dep)),'original_expanded_inner_proof_file_bytes':sum(x.stat().st_size for x in inner_paths),'original_compact_inner_proof_bytes':sum((a.results_dir/n/'proof.bin').stat().st_size for n in ('sha384-direct','sha384-committed-gkr')),'trusted_statement_file_bytes':sum(x.stat().st_size for x in statement_paths),'derive_native_seconds':derive_seconds,'gkr_prover_seconds':gkr_seconds,'pcs_prover_seconds':pcs_seconds,'core_verify_seconds':core_seconds,'full_trace_required':False,'trace_root_required':False,'rs_root':root,'inner_paths':[str(x) for x in inner_paths],'statement_paths':[str(x) for x in statement_paths],'limits':['No disclosed trace or separate trace root/link check; every fixed operand has explicit equality residual under same PCS root.','Derived dependency is internal cache, regenerated from original proofs/statements, never accepted as prover-selected metadata.','Original component proofs and native GKR/transcript/SHA384/Merkle checks remain required; this is not complete recursion.','Trusted statements still require application receipt policy; no new receipt extraction theorem.','Q8/Ext4 diagnostic, no PQ128/QROM/proximity/zero-knowledge certification.']})
    (out/'report.json').write_text(json.dumps(meta,indent=2));print(json.dumps(meta,indent=2))
if __name__=='__main__':main()
