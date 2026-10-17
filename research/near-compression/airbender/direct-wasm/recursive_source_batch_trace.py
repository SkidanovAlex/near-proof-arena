"""All initial source-batching arithmetic linked into the complete fold trace.

One combined commitment binds both regions. All output equalities are checked
individually. Native transcript/beta derivation and SHA384 authentication remain
explicit; this is a disclosed verifier certificate, not recursive compression.
"""
import argparse,copy,json,sys,time
from pathlib import Path
import recursive_fold_trace as fold

PROFILE=b'NEAR-RECURSIVE-SOURCE-AND-FOLD-TRACE-V1'


def derive(sessions,fold_artifact):
    import pq384_weighted_joint as w
    from pq384_primitives import verify_path,field_words
    from pq384_one_fold import decode_hash
    inputs=[];nodes=[];outputs=[];provenance=[]
    def const_zero():nodes.append(['const',0,0,0,0]);return len(nodes)-1
    def inp(value):
        fold.canonical_value(value);nodes.append(['input',len(inputs)]);inputs.append(value);return len(nodes)-1
    def op(kind,a,b):nodes.append([kind,a,b]);return len(nodes)-1
    zero=const_zero();first={(r['component'],r['query_ordinal']):i for i,r in enumerate(fold_artifact['rows']) if r['round']==0}
    for ci,session in enumerate(sessions):
        degrees,D,ctxs,betas,_,_,challenges,samples=w.replay(session['proof'],bytes.fromhex(session['statement']),bytes.fromhex(session['parent']),session['branches'],fold.canonical_value(session['claim']))
        fold.require(len(session['proof']['queries'])==len(samples)==8,'complete source queries')
        for qi,(sample,query) in enumerate(zip(samples,session['proof']['queries'])):
            fold.require(len(query['sources'])==len(session['branches']),'all source branches')
            even,odd=zero,zero;branches=[]
            for bi,(q,b,d,ctx,beta) in enumerate(zip(query['sources'],session['branches'],degrees,ctxs,betas)):
                fold.require(set(q)=={'leaf','path'} and len(q['leaf'])==2*len(beta),'complete source leaf lanes')
                verify_path(decode_hash(b['root']),ctx,2*d,sample%(2*d),field_words(q['leaf']),[decode_hash(x) for x in q['path']])
                start=len(inputs);a,c=zero,zero
                for lane,weight in enumerate(beta):
                    weight_slot=inp(list(weight));left=inp([q['leaf'][2*lane],0,0,0]);right=inp([q['leaf'][2*lane+1],0,0,0])
                    a=op('add',a,op('mul',weight_slot,left));c=op('add',c,op('mul',weight_slot,right))
                side=None if d==D else (sample%(4*d))//(2*d)
                if side is not None:a=c=(a,c)[side]
                even=op('add',even,a);odd=op('add',odd,c)
                branches.append({'branch':bi,'root':b['root'],'context_hex':ctx.hex(),'index':sample%(2*d),'half':2*d,'projection_side':side,'lane_count':len(beta),'slot_start':start,'slot_count':3*len(beta),'slot_order':['beta','base_left','base_right']})
            fold.require((ci,qi) in first,'first fold exists')
            fi=first[(ci,qi)];slot_start=len(inputs)
            actual_a=inp(fold_artifact['values'][7*fi]);actual_b=inp(fold_artifact['values'][7*fi+1])
            outputs.append([op('sub',even,actual_a),op('sub',odd,actual_b)])
            provenance.append({'component':ci,'query_ordinal':qi,'sample':sample,'branches':branches,'first_fold_row':fi,'fold_operand_slots':[7*fi,7*fi+1],'expected_slot_start':slot_start})
    return {'input_count':len(inputs),'nodes':nodes,'outputs':outputs,'output_order':['virtual_even-first_fold_a','virtual_odd-first_fold_b']},inputs,provenance


def evaluate(dag,values):
    from check_whir_handoff import add,sub,mul
    fold.require(len(values)==dag['input_count'],'source operand coverage');vv=[fold.canonical_value(x) for x in values];computed=[]
    for i,node in enumerate(dag['nodes']):
        if node[0]=='const':
            fold.require(node==['const',0,0,0,0],'only canonical zero constant');value=(0,0,0,0)
        elif node[0]=='input':
            fold.require(len(node)==2 and type(node[1])is int and 0<=node[1]<len(vv),'source input slot');value=vv[node[1]]
        else:
            fold.require(len(node)==3 and node[0] in ('add','sub','mul') and all(type(j)is int and 0<=j<i for j in node[1:]),'source DAG edges');value={'add':add,'sub':sub,'mul':mul}[node[0]](computed[node[1]],computed[node[2]])
        computed.append(value)
    for pair in dag['outputs']:
        fold.require(len(pair)==2,'both source outputs')
        for index in pair:
            fold.require(type(index)is int and 0<=index<len(computed),'output index')
            fold.require(computed[index]==(0,0,0,0),'source batching mismatch')
    return True


def commitment(fold_root,dag,values,provenance):
    from pq384_primitives import hash_parts,merkle_tree,field_words
    context=hash_parts(PROFILE,bytes.fromhex(fold_root),fold.canonical(dag),fold.canonical(provenance))
    leaves=[field_words([v for x in values[p['branches'][0]['slot_start']:p['expected_slot_start']+2] for v in fold.canonical_value(x)]) for p in provenance]
    fold.require(leaves and len(leaves)&(len(leaves)-1)==0,'source query trace shape')
    source_root=merkle_tree(leaves,context)[0]
    return hash_parts(PROFILE,bytes.fromhex(fold_root),source_root).hex()


def build(fold_artifact,expected_headers):
    fold.verify(fold_artifact,expected_headers)
    dag,values,provenance=derive(fold_artifact['sessions'],fold_artifact);evaluate(dag,values)
    return {'profile':PROFILE.decode(),'fold':fold_artifact,'source_dag':dag,'source_values':values,'source_provenance':provenance,'combined_root':commitment(fold_artifact['trace_root'],dag,values,provenance)}


def verify(artifact,expected_headers):
    fold.require(type(artifact)is dict and set(artifact)=={'profile','fold','source_dag','source_values','source_provenance','combined_root'} and artifact['profile']==PROFILE.decode(),'source/fold artifact fields')
    fold.verify(artifact['fold'],expected_headers)
    dag,values,provenance=derive(artifact['fold']['sessions'],artifact['fold'])
    fold.require(artifact['source_dag']==dag and artifact['source_provenance']==provenance,'complete source DAG and provenance')
    fold.require(artifact['source_values']==values,'authenticated source leaf and transcript beta slots')
    fold.require(artifact['combined_root']==commitment(artifact['fold']['trace_root'],dag,values,provenance),'combined committed trace')
    evaluate(dag,artifact['source_values']);return True


def main():
    p=argparse.ArgumentParser();p.add_argument('--reference-dir',required=True);p.add_argument('--fold-directory',type=Path,required=True);p.add_argument('--output-directory',type=Path,required=True);a=p.parse_args();sys.path.insert(0,a.reference_dir)
    base=json.loads((a.fold_directory/'trace.json').read_text());headers=json.loads((a.fold_directory/'expected-headers.json').read_text());start=time.monotonic();artifact=build(base,headers);build_seconds=time.monotonic()-start;start=time.monotonic();assert verify(artifact,headers);verify_seconds=time.monotonic()-start
    cases=[]
    def reject(name,change):
        bad=copy.deepcopy(artifact);change(bad)
        try:verify(bad,headers)
        except (ValueError,AssertionError,IndexError,KeyError):cases.append(name)
        else:raise AssertionError('accepted '+name)
    reject('omitted source query',lambda b:b['source_provenance'].pop())
    reject('duplicated source branch',lambda b:b['source_provenance'][0]['branches'].__setitem__(1,b['source_provenance'][0]['branches'][0]))
    reject('wrong projected side',lambda b:b['source_provenance'][0]['branches'][0].__setitem__('projection_side',99))
    reject('wrong first fold link',lambda b:b['source_provenance'][0].__setitem__('first_fold_row',1))
    reject('missing source output',lambda b:b['source_dag']['outputs'][0].pop())
    reject('changed beta slot',lambda b:b['source_values'][0].__setitem__(0,(b['source_values'][0][0]+1)%2013265921))
    reject('changed authenticated leaf slot',lambda b:b['source_values'][1].__setitem__(0,(b['source_values'][1][0]+1)%2013265921))
    reject('wrong combined root',lambda b:b.__setitem__('combined_root','00'*48))
    a.output_directory.mkdir(parents=True,exist_ok=True);(a.output_directory/'trace.json').write_bytes(fold.canonical(artifact))
    report={'status':'PASS','recursive_proof':False,'source_query_pairs':len(artifact['source_provenance']),'source_branches':sum(len(p['branches']) for p in artifact['source_provenance']),'source_lane_pairs':sum(b['lane_count'] for p in artifact['source_provenance'] for b in p['branches']),'source_ext4_input_slots':len(artifact['source_values']),'source_dag_nodes':len(artifact['source_dag']['nodes']),'source_residual_outputs':2*len(artifact['source_provenance']),'fold_residual_outputs':3*len(base['rows']),'combined_trace_bytes':(a.output_directory/'trace.json').stat().st_size,'combined_root':artifact['combined_root'],'build_seconds':build_seconds,'verify_seconds':verify_seconds,'negative_cases':cases,'limits':['One combined commitment; complete source and fold output vectors checked individually by host.','No scalar GKR conjunction proof or succinct recursive verifier; all inputs disclosed.','Transcript, beta/weight evaluation, Merkle, terminal and original GKR-to-PCS header derivation remain native boundaries.','No certified QROM, quantum128, commitment binding or zero knowledge claim.']}
    (a.output_directory/'report.json').write_text(json.dumps(report,indent=2));print(json.dumps(report,indent=2))
if __name__=='__main__':main()
