"""Single-RS source: fixed-slot coverage and no disclosed trace dependency."""
import argparse,copy,json,subprocess,sys,time
from pathlib import Path

def main():
 p=argparse.ArgumentParser();p.add_argument('--reference-dir',required=True);p.add_argument('--proof-directory',type=Path,required=True);p.add_argument('--rs-binary',required=True);a=p.parse_args();sys.path.insert(1,a.reference_dir)
 import recursive_single_root_conjunction as c
 import recursive_single_root_gkr_engine as g
 import recursive_conjunction_gkr as old
 report=json.loads((a.proof_directory/'report.json').read_text());proof=json.loads((a.proof_directory/'proof.json').read_text());proofs=[json.loads(Path(x).read_text()) for x in report['inner_paths']];statements=[json.loads(Path(x).read_text()) for x in report['statement_paths']];start=time.monotonic();cases=[]
 altered=copy.deepcopy(statements);altered[1]['roots'][0]='00'*48
 try:c.derive_components(proofs,altered)
 except ValueError as e:assert str(e)=='three shared component source roots';cases.append('mismatched shared source root')
 else:raise AssertionError('shared root mismatch accepted')
 def forbidden(*args,**kwargs):raise AssertionError('disclosed trace/root link or host residual check called')
 # Neither public verification nor native derivation may invoke any old trace,
 # cross-root reconstruction, operand packing or host residual evaluator.
 saved=[(c.packing,'independent_rs_root'),(c.packing,'pack_inputs'),(old,'bind_without_residual_checks'),(c.f,'evaluate_dag'),(c.source,'evaluate')];originals=[getattr(m,n) for m,n in saved]
 for m,n in saved:setattr(m,n,forbidden)
 try:assert c.verify(proof,proofs,statements)
 finally:
  for (m,n),v in zip(saved,originals):setattr(m,n,v)
 dep,values=c.derive_components(proofs,statements)
 def reject(name,mutation):
  q,d=copy.deepcopy(proof),copy.deepcopy(dep);mutation(q,d)
  try:c.verify_derived(q,d)
  except (ValueError,AssertionError,IndexError,KeyError,TypeError):cases.append(name)
  else:raise AssertionError('accepted '+name)
 reject('omitted fixed slot',lambda q,d:d['fixed'].pop())
 reject('duplicate fixed slot',lambda q,d:d['fixed'].__setitem__(1,d['fixed'][0]))
 reject('fixed slot reorder',lambda q,d:d['fixed'].reverse())
 reject('fixed expected value changed',lambda q,d:d['fixed'][0][1].__setitem__(0,(d['fixed'][0][1][0]+1)%2013265921))
 reject('missing arithmetic output',lambda q,d:d['fold_dag']['outputs'][0].pop())
 reject('different RS root',lambda q,d:q.__setitem__('rs_root','00'*48))
 reject('old two-root profile',lambda q,d:q.__setitem__('profile',c.packing.PROFILE.decode()))
 reject('missing GKR layer',lambda q,d:q['gkr']['layers'].pop())
 reject('missing PCS query',lambda q,d:q['opening']['queries'].pop())
 reject('extra trace root',lambda q,d:q.__setitem__('trace_root','00'*48))
 # Attack that satisfies ALL old800 equations: freely shift a noninitial row's
 # even and odd by1, adjust its a,b,next accordingly. Only authenticated fixed
 # operands prevent this attack, not an accidental arithmetic contradiction.
 private=c.honest_private(dep,values);bad=list(private);row=next(i for i,x in enumerate(dep['fold_provenance']) if x['round']==1);k=7*row;x=bad[k+2]
 for slot,delta in [(0,g.add(g.ONE,x)),(1,g.sub(g.ONE,x)),(4,g.ONE),(5,g.ONE),(6,g.ONE)]:bad[k+slot]=g.add(bad[k+slot],delta)
 nf=dep['fold_dag']['input_count'];assert c.f.evaluate_dag(dep['fold_dag'],[list(v) for v in bad[:nf]]);assert c.source.evaluate(dep['source_dag'],[list(v) for v in bad[nf:dep['input_count']]])
 request=a.proof_directory/'attack-commit-input.json';result=a.proof_directory/'attack-commit-output.json';cache=a.proof_directory/'attack-cache';request.write_bytes(c.f.canonical({'rows':c.source_rows(bad),'packing':16,'indices':[],'cache_directory':str(cache)}));subprocess.run([a.rs_binary,str(request),str(result)],check=True,capture_output=True);root=json.loads((cache/'manifest.json').read_text())['root_hex'];assert root!=proof['rs_root'];layout,binding,_,_=c.compile_layout(dep,root)
 assert g.values(layout,bad)[-1][layout['root']]!=g.ZERO
 try:g.prove(layout,binding,bad)
 except ValueError as e:assert str(e)=='false circuit output';cases.append('fresh committed all800-consistent wrong fixed operands rejected by constrained output')
 else:raise AssertionError('false fixed operand circuit accepted')
 replay=copy.deepcopy(proof);replay['rs_root']=root
 try:c.verify_derived(replay,dep)
 except (ValueError,AssertionError):cases.append('recommitted wrong-fixed-slot old proof rejected through GKR')
 else:raise AssertionError('old proof accepted new root')
 out={'status':'PASS','negative_cases':cases,'public_verifier_with_old_trace_host_checks_disabled':True,'fresh_attack_all800_old_arithmetic_residuals_zero':True,'fresh_attack_fixed_operand_constraints_detect_nonzero_output':True,'seconds':time.monotonic()-start,'scope':'Actual PCS/GKR diagnostic. Inner proof/header/transcript/hash checks remain native; no end-to-end recursion or PQ128 claim.'}
 (a.proof_directory/'negatives.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
if __name__=='__main__':main()
