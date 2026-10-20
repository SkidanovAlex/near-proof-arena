"""Actual PCS mutation and coordinate-map checks; no security certification."""
import argparse,copy,json,sys,time
from pathlib import Path

def main():
 p=argparse.ArgumentParser();p.add_argument('--reference-dir',required=True);p.add_argument('--proof-directory',type=Path,required=True);p.add_argument('--trace-directory',type=Path,required=True);p.add_argument('--headers',type=Path,required=True);a=p.parse_args();sys.path.insert(1,a.reference_dir)
 import recursive_pcs_conjunction as c
 import recursive_configured_gkr_engine as g
 proof=json.loads((a.proof_directory/'proof.json').read_text());dep=json.loads((a.proof_directory/'verified-dependency.json').read_text());artifact=json.loads((a.trace_directory/'trace.json').read_text());headers=json.loads(a.headers.read_text());start=time.monotonic();cases=[]
 assert c.verify_bound(proof,artifact,headers)
 def forbidden(*args,**kwargs):raise AssertionError('disclosed arithmetic invoked')
 oldpack,oldf,olds=c.pack_inputs,c.fold.evaluate_dag,c.source.evaluate
 c.pack_inputs=c.fold.evaluate_dag=c.source.evaluate=forbidden
 try:assert c.verify_core(proof,dep)
 finally:c.pack_inputs,c.fold.evaluate_dag,c.source.evaluate=oldpack,oldf,olds
 def reject(name,mutate):
  q,d=copy.deepcopy(proof),copy.deepcopy(dep);mutate(q,d)
  try:c.verify_core(q,d)
  except (ValueError,AssertionError,IndexError,KeyError,TypeError):cases.append(name)
  else:raise AssertionError('accepted '+name)
 def bump(v):v[0]=(v[0]+1)%2013265921
 reject('wrong RS root',lambda q,d:q.__setitem__('rs_root','00'*48))
 reject('wrong trace root',lambda q,d:q.__setitem__('trace_root','00'*48))
 reject('wrong profile',lambda q,d:q.__setitem__('profile','old'))
 reject('wrong dependency capacity',lambda q,d:d.__setitem__('capacity',8192))
 reject('missing GKR layer',lambda q,d:q['gkr']['layers'].pop())
 reject('GKR quadratic',lambda q,d:bump(q['gkr']['layers'][0]['rounds'][0][0]))
 reject('GKR terminal functional',lambda q,d:bump(q['gkr']['layers'][-1]['inputs'][0]))
 reject('missing PCS query',lambda q,d:q['opening']['queries'].pop())
 reject('PCS reduction',lambda q,d:bump(q['opening']['reduction'][0][0]))
 reject('PCS fold quadratic',lambda q,d:bump(q['opening']['rounds'][0]['quadratic'][0]))
 reject('PCS terminal coefficient',lambda q,d:bump(q['opening']['terminal']['coefficients'][0][0]))
 try:c.linked_dependency(artifact,headers,'00'*48)
 except (ValueError,AssertionError):cases.append('unrelated RS commitment rejected by native link')
 else:raise AssertionError('unlinked root accepted')
 # Compare entire tensor coefficient map, including zero, one, mixed challenges.
 checked=0;topbit_regression=False
 for point in ([g.ZERO]*15,[g.ONE]*15,[tuple((17*i+3*j+2)%2013265921 for j in range(4)) for i in range(15)]):
  scale=(2,3,5,7);ob={'queries':[(point,scale),(point,g.ZERO)]};b=c.branches(dep,ob)[0];whole=g.eqs(point);row=g.eqs(point[:12])
  for group in range(4):
   for coordinate in range(4):
    basis=tuple(int(i==coordinate) for i in range(4));weight=b['lanes'][0][0][4*group+coordinate]
    for r in range(4096):
     expected=g.mul(g.mul(scale,whole[r+4096*group]),basis)
     assert g.mul(weight,row[r])==expected;checked+=1
  if point==[g.ONE]*15:
   wrong=g.mul(scale,g.ONE);assert wrong!=b['lanes'][0][0][12];topbit_regression=True
 report={'status':'PASS','negative_cases':cases,'packing_coefficient_comparisons':checked,'omitted_high_private_zero_bit_detected':topbit_regression,'core_verifies_with_operand_packing_and_host_residual_evaluation_disabled':True,'full_bound_wrapper_verified':True,'seconds':time.monotonic()-start,'limits':'Root linkage still native/full disclosure. Q8/Ext4 diagnostic, not complete recursion or PQ128.'}
 (a.proof_directory/'negatives.json').write_text(json.dumps(report,indent=2));print(json.dumps(report,indent=2))
if __name__=='__main__':main()
