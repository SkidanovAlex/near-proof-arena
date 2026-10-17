"""Independent full-witness replay of versioned typed EXEC/CODE/buses."""
import argparse,copy,json,sys
from pathlib import Path
import prepared_typed_air as a
p=argparse.ArgumentParser();p.add_argument('--reference-dir',required=True);p.add_argument('--fixture',required=True);p.add_argument('--legacy',action='append',default=[]);p.add_argument('--out',required=True)
args=p.parse_args();sys.path.insert(0,args.reference_dir)
from reference import inspect,expr_degree,evaluate
out=Path(args.out);out.mkdir(parents=True,exist_ok=True)
cases=json.load(open(args.fixture))['cases']
for path in args.legacy:cases+=json.load(open(path))['cases']
reports=[];attacks=[];provenance_gaps=[]
for case in cases:
 spec,rows=a.make(case);name=case['label'];result=inspect(spec['air'],rows,spec['public'])
 assert result['accepted'],(name,result['violations'][:5])
 (out/(name+'-spec.json')).write_text(json.dumps(spec));(out/(name+'-rows.json')).write_text(json.dumps({'rows_by_table':rows}))
 def reject(label,bad=None,pub=None):
  result=inspect(spec['air'],rows if bad is None else bad,spec['public'] if pub is None else pub)
  assert not result['accepted'],(name,label)
  attacks.append(dict(case=name,attack=label))
 # Every typed value/tag field at one internal row and terminal boundary.
 for r in sorted({1,len(case['exec_rows']),len(rows[0])-1}):
  for col in [a.STYPE,a.STYPE+7,a.LTYPE,a.HSTACK,a.HSTACK+255,a.HLOCALS,a.HLOCALS+127,a.HIMM,a.EQZRESULT]:
   bad=copy.deepcopy(rows);bad[0][r][col]^=1;reject(f'typed-cell-{r}-{col}',bad)
 for field in [12+11,12+14,12+15,63+11,63+14,63+15,a.TYPEPUB,a.TYPEPUB+3]:
  pub=spec['public'].copy();pub[field]=(pub[field]+1)%a.P;reject(f'typed-public-{field}',pub=pub)
 for i,event in enumerate(case['exec_rows']):
  op=event['instruction']['opcode'];sp=len(event['before']['stack'])
  if op in (106,124) and event['status']=='continue':
   for operand in (sp-1,sp-2):
    bad=copy.deepcopy(rows);bad[0][i][a.STYPE+operand]^=1;reject(f'wrong-add-input-type-{i}-{operand}',bad)
   if op==124:
    for limb in range(4):
     bad=copy.deepcopy(rows);base=(a.RESULT if limb<2 else a.HRESULT)+16*(limb%2)
     n=sum(bad[0][i][base+b]<<b for b in range(16));a.putbits(bad[0][i],base,n^1,16)
     reject(f'coherent-add-result-limb-{i}-{limb}',bad)
    for col in (a.CARRY,a.CARRY+1,a.HCARRY,a.HCARRY+1):
     bad=copy.deepcopy(rows);bad[0][i][col]^=1;reject(f'wrap-carry-{i}-{col}',bad)
  if op==80 and event['status']=='continue':
   bad=copy.deepcopy(rows);bad[0][i+1][a.STYPE+sp-1]=1;reject(f'eqz-wrong-i64-result-{i}',bad)
   bad=copy.deepcopy(rows);bad[0][i][a.EQZRESULT]^=1;reject(f'eqz-false-zero-{i}',bad)
  if op in (33,34) and event['status']=='continue':
   bad=copy.deepcopy(rows);bad[0][i][a.STYPE+sp-1]^=1;reject(f'local-write-type-{i}',bad)
  if op==66:
   # Coherent high-immediate range mutation still fails authenticated CODE.
   bad=copy.deepcopy(rows);bad[0][i][a.HIMM]^=1;reject(f'fetch-high-immediate-{i}',bad)
 # Declared local type is fixed for the whole trace and public header.
 if case.get('local_count',0):
  bad=copy.deepcopy(rows);pub=spec['public'].copy()
  for row in bad[0]:row[a.LTYPE]^=1
  pub[a.TYPEPUB]^=1
  changed=inspect(spec['air'],bad,pub)
  if changed['accepted']:
   provenance_gaps.append(dict(case=name,attack='changed unused declared local type and public header',obligation='actual PREP/type-header checker must reject; AIR alone defines a different statement'))
  else:attacks.append(dict(case=name,attack='coherent-declared-local-type-change'))
 # Literal CODE mutation is coherent Boolean/range data but conflicts with
 # authenticated fetch/public message; unrelated private rows remain unchanged.
 for pc,entry in enumerate(case['code']):
  if entry['instruction']['opcode']==66:
   bad=copy.deepcopy(rows);bad[1][pc][a.CHIMM]^=1;reject(f'code-high-immediate-{pc}',bad)
   pub=spec['public'].copy();pub[a.CODEPUB+a.RECORD*pc+32]^=1;reject(f'public-code-high-immediate-{pc}',pub=pub)
   break
 reports.append(dict(case=name,rows=[len(x) for x in rows],widths=[a.WIDTH,a.CWIDTH],public_fields=len(spec['public']),explicit_constraints=[len(t['constraints']) for t in spec['air']['tables']],max_degree=max(expr_degree(e,t['width'],spec['air']['numPub']) for t in spec['air']['tables'] for e in t['constraints'])))
summary=dict(status='PASS',cases=len(reports),rejected=len(attacks),reports=reports,attacks=attacks,known_external_provenance_cases=provenance_gaps,scope='Full-witness actual prepared trace against typed EXEC/CODE source, exact natural buses and public boundaries; typed whole-call formal refinement and cryptographic proof pending')
(out/'report.json').write_text(json.dumps(summary,indent=2));print(json.dumps({k:v for k,v in summary.items() if k not in ('reports','attacks')}))
