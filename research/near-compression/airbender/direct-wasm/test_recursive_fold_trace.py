"""Coverage/provenance and noncancellation regressions for the complete trace."""
import argparse,copy,json,sys,time
from pathlib import Path


def main():
    p=argparse.ArgumentParser();p.add_argument('--reference-dir',required=True);p.add_argument('--trace-dir',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args();sys.path.insert(1,a.reference_dir)
    import recursive_fold_trace as t
    import check_whir_handoff as f
    artifact=json.loads((a.trace_dir/'trace.json').read_text());headers=json.loads((a.trace_dir/'expected-headers.json').read_text())
    start=time.monotonic();assert t.verify(artifact,headers);cases=[]
    def reject(name,mutate):
        bad=copy.deepcopy(artifact);mutate(bad)
        try:t.verify(bad,headers)
        except (ValueError,AssertionError,IndexError,KeyError):cases.append(name)
        else:raise AssertionError('accepted '+name)
    reject('omitted row',lambda b:b['rows'].pop())
    reject('duplicate row preserving count',lambda b:b['rows'].__setitem__(1,b['rows'][0]))
    reject('reordered rows',lambda b:b['rows'].reverse())
    reject('omitted residual output',lambda b:b['dag']['outputs'][0].pop())
    reject('duplicate residual output',lambda b:b['dag']['outputs'][0].__setitem__(2,b['dag']['outputs'][0][0]))
    reject('wrong source provenance',lambda b:b['rows'][0]['source'][0].__setitem__('root','00'*48))
    reject('wrong next pair side',lambda b:b['rows'][0].__setitem__('next_side',1-b['rows'][0]['next_side']))
    reject('wrong transcript challenge slot',lambda b:b['rows'][0].__setitem__('challenge_slot',[0,999]))
    reject('substituted challenge value',lambda b:b['values'][3].__setitem__(0,(b['values'][3][0]+1)%f.P))
    reject('zero domain point',lambda b:b['values'][2].__setitem__(0,0))
    reject('wrong source Merkle leaf',lambda b:b['sessions'][0]['proof']['queries'][0]['sources'][0]['leaf'].__setitem__(0,(b['sessions'][0]['proof']['queries'][0]['sources'][0]['leaf'][0]+1)%f.P))
    reject('wrong folded Merkle leaf',lambda b:b['sessions'][0]['proof']['queries'][0]['folds'][0]['leaf'].__setitem__(0,(b['sessions'][0]['proof']['queries'][0]['folds'][0]['leaf'][0]+1)%f.P))
    reject('wrong caller header',lambda b:b['sessions'][0].__setitem__('parent','00'*48))
    reject('missing query',lambda b:b['sessions'][0]['proof']['queries'].pop())
    reject('duplicated query',lambda b:b['sessions'][0]['proof']['queries'].__setitem__(1,b['sessions'][0]['proof']['queries'][0]))
    reject('wrong commitment',lambda b:b.__setitem__('trace_root','00'*48))
    # Recommit a wrong free witness: rejection must come from arithmetic, not
    # merely a stale hash. All authenticated external operand slots unchanged.
    bindings,contexts=t.derive_bindings(artifact['sessions']);ctx=t.context_for(headers,contexts,artifact['dag'])
    def wrong_odd(b):
        b['values'][5][0]=(b['values'][5][0]+1)%f.P
        b['trace_root']=t.trace_commitment(ctx,bindings,b['values'])
    reject('wrong odd witness with recomputed commitment',wrong_odd)
    # The old scalar sum would accept these +delta/-delta target changes.
    # The complete vector checker must reject them regardless of zero sum.
    vv=copy.deepcopy(artifact['values']);vv[6][0]=(vv[6][0]+1)%f.P;vv[13][0]=(vv[13][0]-1)%f.P
    computed=[]
    for node in artifact['dag']['nodes']:
        computed.append(tuple(vv[node[1]]) if node[0]=='input' else {'add':f.add,'sub':f.sub,'mul':f.mul}[node[0]](computed[node[1]],computed[node[2]]))
    residuals=[computed[i] for row in artifact['dag']['outputs'] for i in row];total=(0,0,0,0)
    for residual in residuals:total=f.add(total,residual)
    assert total==(0,0,0,0) and any(x!=(0,0,0,0) for x in residuals)
    try:t.evaluate_dag(artifact['dag'],vv)
    except ValueError:cases.append('opposite nonzero residuals cancel in sum but vector rejected')
    else:raise AssertionError('cancellation accepted')
    report={'status':'PASS','fold_rows':len(artifact['rows']),'residual_outputs':len(residuals),'negative_cases':len(cases),'cases':cases,'seconds':time.monotonic()-start,'scope':'Full disclosed fold trace only; host evaluates each output. No scalar GKR conjunction proof or recursive security claim.'}
    a.output.write_text(json.dumps(report,indent=2));print(json.dumps(report,indent=2))
if __name__=='__main__':main()
