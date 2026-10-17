"""Conjunction reduction: committed-vector ordering and false-vector regressions."""
import argparse,copy,json,sys,time
from pathlib import Path


def main():
    p=argparse.ArgumentParser();p.add_argument('--reference-dir',required=True);p.add_argument('--trace-directory',type=Path,required=True);p.add_argument('--headers',type=Path,required=True);p.add_argument('--proof-directory',type=Path,required=True);a=p.parse_args();sys.path.insert(1,a.reference_dir)
    import recursive_conjunction_gkr as c
    import recursive_fold_trace as f
    import recursive_source_batch_trace as s
    import pq384_terminal_gkr as g
    artifact=json.loads((a.trace_directory/'trace.json').read_text());headers=json.loads(a.headers.read_text());proof=json.loads((a.proof_directory/'proof.json').read_text());cases=[];start=time.monotonic()
    def forbidden(*args,**kwargs):raise AssertionError('host residual-vector evaluation invoked')
    oldf,olds=f.evaluate_dag,s.evaluate;f.evaluate_dag=s.evaluate=forbidden
    try:assert c.verify(proof,artifact,headers)
    finally:f.evaluate_dag,s.evaluate=oldf,olds
    def reject(name,mutate):
        pp,aa=copy.deepcopy(proof),copy.deepcopy(artifact);mutate(pp,aa)
        try:c.verify(pp,aa,headers)
        except (ValueError,AssertionError,IndexError,KeyError):cases.append(name)
        else:raise AssertionError('accepted '+name)
    reject('missing output before challenge',lambda p,a:a['source_dag']['outputs'].pop())
    reject('wrong prechallenge root',lambda p,a:p.__setitem__('trace_root','00'*48))
    reject('GKR quadratic mutation',lambda p,a:p['proof']['layers'][0]['rounds'][0][0].__setitem__(0,(p['proof']['layers'][0]['rounds'][0][0][0]+1)%2013265921))
    reject('GKR input functional mutation',lambda p,a:p['proof']['layers'][-1]['inputs'][0].__setitem__(0,(p['proof']['layers'][-1]['inputs'][0][0]+1)%2013265921))
    reject('missing GKR layer',lambda p,a:p['proof']['layers'].pop())
    bad=copy.deepcopy(artifact);base=bad['fold'];base['values'][5][0]=(base['values'][5][0]+1)%2013265921
    rows,contexts=f.derive_bindings(base['sessions']);ctx=f.context_for(headers,contexts,base['dag']);base['trace_root']=f.trace_commitment(ctx,rows,base['values'])
    bad['combined_root']=s.commitment(base['trace_root'],bad['source_dag'],bad['source_values'],bad['source_provenance'])
    assert c.bind_without_residual_checks(bad,headers),'binding must not secretly check arithmetic'
    old_point,_,_=c.challenge(artifact);new_point,_,_=c.challenge(bad);assert old_point!=new_point
    layout,private,_,_=c.compile_conjunction(bad);assert g.values(layout,private)[-1][layout['root']]!=g.ZERO
    replay=copy.deepcopy(proof);replay['trace_root']=bad['combined_root']
    try:c.verify(replay,bad,headers)
    except (ValueError,AssertionError):cases.append('false residual with fresh commitment/challenge rejects old proof')
    else:raise AssertionError('accepted false committed vector')
    report={'status':'PASS','all_residuals':800,'host_residual_evaluation_forbidden_during_successful_verification':True,'false_residual_binding_alone_passes':True,'fresh_commitment_changes_aggregation_point':True,'fresh_point_detects_test_false_vector':True,'negative_cases':cases,'seconds':time.monotonic()-start,'scope':'Diagnostic commit-before-challenge GKR reduction with disclosed input functional. No universal FS/QROM or quantum128 security claim.'}
    (a.proof_directory/'negatives.json').write_text(json.dumps(report,indent=2));print(json.dumps(report,indent=2))
if __name__=='__main__':main()
