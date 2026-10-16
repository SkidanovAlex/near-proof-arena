"""Commit-before-challenge GKR reduction of ALL source/fold residuals.

This proves one randomized MLE zero claim, not a deterministic conjunction.
Inputs remain disclosed and authenticated by the trace commitment. Replacing
that disclosure with PCS and compiling native transcript/hash checks are pending.
"""
import argparse,copy,json,sys,time
from pathlib import Path
import recursive_fold_trace as fold
import recursive_source_batch_trace as source

PROFILE=b'NEAR-RECURSIVE-COMPLETE-RESIDUAL-GKR-V1'


def bind_without_residual_checks(artifact,headers):
    """Same exact source binding, but deliberately no host residual evaluation."""
    fold.require(type(artifact)is dict and set(artifact)=={'profile','fold','source_dag','source_values','source_provenance','combined_root'} and artifact['profile']==source.PROFILE.decode(),'source artifact fields')
    a=artifact['fold'];fold.require(type(a)is dict and set(a)=={'profile','sessions','contexts','dag','rows','values','trace_root'} and a['profile']==fold.PROFILE.decode(),'fold artifact fields')
    fold.require(fold.canonical([fold.header(s) for s in a['sessions']])==fold.canonical(headers),'trusted PCS headers')
    rows,contexts=fold.derive_bindings(a['sessions']);dag=fold.build_dag(len(rows))
    fold.require(a['dag']==dag and a['contexts']==contexts and a['rows']==[r['provenance'] for r in rows],'complete fold coverage')
    values=a['values'];fold.require(len(values)==7*len(rows),'operand coverage')
    for i,row in enumerate(rows):
        for slot,key in ((0,'a'),(1,'b'),(2,'x'),(3,'r'),(6,'expected')):
            fold.require(fold.canonical_value(values[7*i+slot])==fold.canonical_value(row[key]),'authenticated fold operands')
    context=fold.context_for(headers,contexts,dag)
    fold.require(a['trace_root']==fold.trace_commitment(context,rows,values),'fold commitment')
    sd,sv,sp=source.derive(a['sessions'],a)
    fold.require(artifact['source_dag']==sd and artifact['source_values']==sv and artifact['source_provenance']==sp,'complete authenticated source region')
    fold.require(artifact['combined_root']==source.commitment(a['trace_root'],sd,sv,sp),'combined prechallenge commitment')
    return True


def challenge(artifact):
    from pq384_primitives import Transcript,hash_parts
    count=sum(map(len,artifact['fold']['dag']['outputs']))+sum(map(len,artifact['source_dag']['outputs']))
    dimension=(count-1).bit_length()
    digest=hash_parts(PROFILE,fold.canonical(artifact['fold']['dag']),fold.canonical(artifact['source_dag']))
    transcript=Transcript(hash_parts(PROFILE,digest,bytes.fromhex(artifact['combined_root']),count.to_bytes(8,'little')))
    words,_=transcript.draw(b'all-residual-output-point',dimension,4)
    return [tuple(x) for x in words],transcript.seed,count


def compile_conjunction(artifact):
    import pq384_terminal_gkr as g
    private=artifact['fold']['values']+artifact['source_values'];nodes=[['input',i] for i in range(len(private))];outputs=[]
    def emit(node):nodes.append(node);return len(nodes)-1
    offset=0
    for dag in (artifact['fold']['dag'],artifact['source_dag']):
        mapping=[]
        for node in dag['nodes']:
            if node[0]=='input':mapping.append(offset+node[1])
            elif node[0]=='const':mapping.append(emit(node))
            else:mapping.append(emit([node[0],mapping[node[1]],mapping[node[2]]]))
        outputs += [mapping[i] for row in dag['outputs'] for i in row]
        offset+=dag['input_count']
    point,seed,count=challenge(artifact);fold.require(count==len(outputs),'all outputs included')
    weights=g.eqs(point);terms=[]
    for output,weight in zip(outputs,weights):terms.append(emit(['mul',output,emit(['const',*weight])]))
    while len(terms)>1:terms=[emit(['add',terms[i],terms[i+1]]) if i+1<len(terms) else terms[i] for i in range(0,len(terms),2)]
    root=terms[0];live=set();todo=[root]
    while todo:
        i=todo.pop()
        if i in live:continue
        live.add(i)
        if nodes[i][0] in ('add','sub','mul'):todo.extend(nodes[i][1:])
    capacity=g.size(len(private));private=[tuple(v) for v in private]+[g.ZERO]*(capacity-len(private))
    circuit={'nodes':nodes,'live_nodes':sorted(live),'private_input_capacity':capacity,'root':root}
    layout=g.layer_circuit(circuit)
    return layout,private,seed,{'residual_count':count,'zero_padded_output_count':len(weights),'challenge_coordinates':len(point),'input_capacity':capacity,'nodes':len(nodes),'live_nodes':len(live),'layer_widths':[len(v) for v in layout['layers']]}


def prove(artifact,headers):
    import pq384_terminal_gkr as g
    bind_without_residual_checks(artifact,headers)
    layout,private,binding,meta=compile_conjunction(artifact)
    proof,ob=g.prove(layout,binding,private)
    return {'profile':PROFILE.decode(),'trace_root':artifact['combined_root'],'proof':proof},meta


def verify(proof,artifact,headers):
    import pq384_terminal_gkr as g
    fold.require(set(proof)=={'profile','trace_root','proof'} and proof['profile']==PROFILE.decode(),'conjunction proof fields')
    bind_without_residual_checks(artifact,headers)
    fold.require(proof['trace_root']==artifact['combined_root'],'prechallenge committed input')
    layout,private,binding,_=compile_conjunction(artifact)
    obligation=g.verify(layout,binding,proof['proof'])
    value=g.ZERO
    for weight,v in zip(obligation['private_weights'],private):value=g.add(value,g.mul(weight,v))
    fold.require(value==obligation['private_claim'],'authenticated disclosed terminal input functional')
    return True


def main():
    p=argparse.ArgumentParser();p.add_argument('--reference-dir',required=True);p.add_argument('--trace-directory',type=Path,required=True);p.add_argument('--headers',type=Path,required=True);p.add_argument('--output-directory',type=Path,required=True);a=p.parse_args();sys.path.insert(0,a.reference_dir)
    artifact=json.loads((a.trace_directory/'trace.json').read_text());headers=json.loads(a.headers.read_text())
    start=time.monotonic();proof,meta=prove(artifact,headers);prover_seconds=time.monotonic()-start
    start=time.monotonic();assert verify(proof,artifact,headers);verifier_seconds=time.monotonic()-start
    a.output_directory.mkdir(parents=True,exist_ok=True);wire=fold.canonical(proof);(a.output_directory/'proof.json').write_bytes(wire)
    report={'status':'PASS','recursive_complete_verifier':False,**meta,'gkr_proof_json_bytes':len(wire),'disclosed_trace_bytes':(a.trace_directory/'trace.json').stat().st_size,'prover_seconds':prover_seconds,'verifier_seconds':verifier_seconds,'ideal_output_test':'For a fixed nonzero residual vector committed before independent uniform output coordinates, multilinear agreement bound is dimension/|K|. Commitment, GKR and Fiat-Shamir/QROM losses are additional and not certified here.','limits':['All800 residual coordinates included; no deterministic sum or subset replacement.','Verifier does NOT evaluate residual DAG outputs; verifies GKR plus exact committed disclosed input functional.','Native binding still replays PCS transcript/Merkle and source batching; caller-fixed PCS headers need original GKR derivation.','Full input disclosure remains; no succinct recursive proof or quantum128 claim.']}
    (a.output_directory/'report.json').write_text(json.dumps(report,indent=2));print(json.dumps(report,indent=2))
if __name__=='__main__':main()
