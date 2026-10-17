"""Exact emitted source DAG reconstruction and concrete evaluator parity.
Native-derived provenance is the trusted interface, not prover-selected metadata.
Executable certificates are evidence; this does not generate kernel proofs of
captured instances or prove Merkle/transcript authentication.
"""
import argparse,copy,hashlib,json,sys,time
from pathlib import Path

def require(x,msg):
 if not x:raise ValueError(msg)
def nat(v):require(type(v)is int and v>=0,'canonical natural');return v

def rebuild(dep):
 p=dep['source_provenance'];foldrows=dep['fold_provenance'];dag=dep['source_dag'];require(len(p)==16,'all16query pairs')
 require([(q['component'],q['query_ordinal']) for q in p]==[(c,q) for c in range(2) for q in range(8)],'canonical component/query order')
 first={}
 for i,r in enumerate(foldrows):
  if r['round']==0:
   key=(r['component'],r['query_ordinal']);require(key not in first,'unique firstfold');first[key]=i
 require(len(first)==16,'firstfold coverage')
 nodes=[['const',0,0,0,0]];outputs=[];cursor=0;metadata=[]
 def emit(n):nodes.append(n);return len(nodes)-1
 def inp():
  nonlocal cursor
  v=emit(['input',cursor]);cursor+=1;return v
 for q in p:
  even=odd=0;branches=[]
  for bi,b in enumerate(q['branches']):
   require(nat(b['branch'])==bi,'branch order');require(nat(b['slot_start'])==cursor,'contiguous triples')
   n=nat(b['lane_count']);require(n>0 and nat(b['slot_count'])==3*n,'exact branch slot count');require(b['slot_order']==['beta','base_left','base_right'],'lane slot order')
   side=b['projection_side'];require(side is None or type(side)is int and side in (0,1),'projection option')
   branches.append({'slotStart':cursor,'laneCount':n,'projection':side});a=c=0
   for _ in range(n):
    w,l,r=inp(),inp(),inp();a=emit(['add',a,emit(['mul',w,l])]);c=emit(['add',c,emit(['mul',w,r])])
   if side is not None:a=c=(a,c)[side]
   even=emit(['add',even,a]);odd=emit(['add',odd,c])
  require(branches,'nonempty source branches');fi=first[(q['component'],q['query_ordinal'])]
  require(nat(q['first_fold_row'])==fi and q['fold_operand_slots']==[7*fi,7*fi+1],'actual firstfold link')
  require(nat(q['expected_slot_start'])==cursor,'expected target slots');metadata.append({'branches':branches,'expectedStart':cursor})
  left,right=inp(),inp();outputs.append([emit(['sub',even,left]),emit(['sub',odd,right])])
 expected={'input_count':cursor,'nodes':nodes,'outputs':outputs,'output_order':['virtual_even-first_fold_a','virtual_odd-first_fold_b']}
 require(dag==expected,'all emitted nodes/outputs exactly match source metadata')
 require(dep['input_count']==dep['fold_dag']['input_count']+cursor,'whole flat vector coverage')
 require(dep['fold_dag']['input_count']==7*len(foldrows)==1792,'actual global source offset')
 return metadata

def source_eval(metadata,values,offset,field):
 add,sub,mul,ZERO=field.add,field.sub,field.mul,field.ZERO;result=[]
 for query in metadata:
  total=[ZERO,ZERO]
  for branch in query['branches']:
   pair=[ZERO,ZERO];start=offset+branch['slotStart']
   for lane in range(branch['laneCount']):
    w,l,r=values[start+3*lane:start+3*lane+3];pair=[add(pair[0],mul(w,l)),add(pair[1],mul(w,r))]
   side=branch['projection']
   if side is not None:pair=[pair[side],pair[side]]
   total=[add(total[i],pair[i]) for i in range(2)]
  result += [sub(total[i],values[offset+query['expectedStart']+i]) for i in range(2)]
 return result

def dag_eval(dag,values,offset,field):
 result=[]
 for i,node in enumerate(dag['nodes']):
  if node[0]=='const':v=tuple(node[1:])
  elif node[0]=='input':v=values[offset+node[1]]
  else:
   require(all(type(j)is int and 0<=j<i for j in node[1:]),'acyclic actual edges')
   v={'add':field.add,'sub':field.sub,'mul':field.mul}[node[0]](result[node[1]],result[node[2]])
  result.append(v)
 return [result[i] for pair in dag['outputs'] for i in pair]

def main():
 p=argparse.ArgumentParser();p.add_argument('--reference-dir',required=True);p.add_argument('--dependency',type=Path,required=True);p.add_argument('--output-directory',type=Path,required=True);a=p.parse_args();sys.path.insert(1,a.reference_dir)
 import check_whir_handoff as field
 dep=json.loads(a.dependency.read_text());start=time.monotonic();meta=rebuild(dep);count=dep['input_count'];cases=[];comparisons=0
 for seed in range(6):
  if seed==0:values=[field.ZERO]*count
  elif seed==1:values=[field.ONE]*count
  else:values=[tuple(int.from_bytes(hashlib.sha384(f'{seed}/{i}/{j}'.encode()).digest()[:8],'little')%2013265921 for j in range(4)) for i in range(count)]
  left=dag_eval(dep['source_dag'],values,1792,field);right=source_eval(meta,values,1792,field);require(left==right and len(left)==32,'arbitrary-vector32output identity');comparisons+=len(left)
 def reject(name,change):
  bad=copy.deepcopy(dep);change(bad)
  try:rebuild(bad)
  except (ValueError,KeyError,IndexError,TypeError):cases.append(name)
  else:raise AssertionError('accepted '+name)
 reject('omitted query',lambda d:d['source_provenance'].pop())
 reject('duplicated query',lambda d:d['source_provenance'].__setitem__(1,d['source_provenance'][0]))
 reject('missing output',lambda d:d['source_dag']['outputs'].pop())
 reject('reversed even odd output',lambda d:d['source_dag']['outputs'][0].reverse())
 reject('wrong operand input node',lambda d:d['source_dag']['nodes'][1].__setitem__(1,1))
 reject('wrong multiply edge',lambda d:d['source_dag']['nodes'][4].__setitem__(2,3))
 reject('overlapping branch slots',lambda d:d['source_provenance'][0]['branches'][1].__setitem__('slot_start',0))
 reject('false lane count',lambda d:d['source_provenance'][0]['branches'][0].__setitem__('lane_count',1))
 reject('Boolean projection index',lambda d:d['source_provenance'][0]['branches'][0].__setitem__('projection_side',True))
 reject('wrong projection',lambda d:d['source_provenance'][0]['branches'][0].__setitem__('projection_side',1))
 reject('wrong target slot',lambda d:d['source_provenance'][0].__setitem__('expected_slot_start',0))
 reject('wrong firstfold target',lambda d:d['source_provenance'][0].__setitem__('fold_operand_slots',[7,8]))
 reject('wrong flat operand offset',lambda d:d['fold_dag'].__setitem__('input_count',0))
 out=a.output_directory;out.mkdir(parents=True,exist_ok=True);(out/'metadata.json').write_text(json.dumps(meta,separators=(',',':')))
 report={'status':'PASS','queries':len(meta),'source_outputs':32,'branches':sum(len(q['branches']) for q in meta),'lane_pairs':sum(b['laneCount'] for q in meta for b in q['branches']),'nodes':len(dep['source_dag']['nodes']),'source_input_slots':dep['source_dag']['input_count'],'global_offset':1792,'arbitrary_vector_cases':6,'output_comparisons':comparisons,'negative_cases':cases,'seconds':time.monotonic()-start,'limits':['Native-derived provenance/headers remain trusted output of original component checks, not a new prover-selected certificate.','All emitted DAG nodes and outputs regenerated, including exact left-associated operation order.','Executable captured-instance check, not closed kernel proof. Lean route theorem supplies conditional structural-certificate implication.','No Merkle/FS/QROM/PQ128 security claim.']}
 (out/'report.json').write_text(json.dumps(report,indent=2));print(json.dumps(report,indent=2))
if __name__=='__main__':main()
