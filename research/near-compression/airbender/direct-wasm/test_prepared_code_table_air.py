"""Independent canonical V2 evaluation of the actual prepared execution fixture."""
import argparse,copy,json,sys
from pathlib import Path
import prepared_code_table_air as a
ap=argparse.ArgumentParser();ap.add_argument('--reference-dir',required=True);ap.add_argument('--fixture',required=True);ap.add_argument('--out',required=True);args=ap.parse_args()
sys.path.insert(0,args.reference_dir)
from reference import inspect,expr_degree
out=Path(args.out);out.mkdir(parents=True,exist_ok=True)
reports=[];attacks=[];parity=[]
for case in json.load(open(args.fixture))['cases']:
    spec,rows=a.make(case); result=inspect(spec['air'],rows,spec['public']);assert result['accepted'],result['violations'][:2]
    name=case['label'];(out/(name+'-spec.json')).write_text(json.dumps(spec));(out/(name+'-rows.json')).write_text(json.dumps({'rows_by_table':rows}))
    parity.append(dict(label=name,spec=spec,rows_by_table=rows))
    def reject(label,bad=None,pub=None,local_valid=False):
        rs=rows if bad is None else bad;ps=spec['public'] if pub is None else pub
        r=inspect(spec['air'],rs,ps);assert not r['accepted'],(name,label)
        if local_valid:assert not any(x[0]=='constraint' for x in r['violations']),(name,label,r['violations'][:3])
        attacks.append(dict(case=name,attack=label,local_constraints_still_valid=local_valid))
        if name=='wrap':parity.append(dict(label=name+':'+label,spec={**spec,'public':ps},rows_by_table=rs))
    # Canonical public code tuple mutations. All CODE rows are authenticated,
    # including never-executed instructions after an early gas failure.
    for i in range(len(case['code'])):
        pub=spec['public'][:];pub[a.CODEPUB+a.RECORD*i+10]+=1
        reject('public-fee-'+str(i),pub=pub,local_valid=True)
    bad=copy.deepcopy(rows);bad[1][-1]=bad[1][0][:];reject('duplicate-CODE-key',bad)
    bad=copy.deepcopy(rows);bad[1][1],bad[1][2]=bad[1][2],bad[1][1];reject('reordered-CODE',bad)
    bad=copy.deepcopy(rows);bad[1][1]=[0]*a.CWIDTH;reject('missing-CODE-active-hole',bad)
    for target in (0,len(case['code'])-1):
        bad=copy.deepcopy(rows);count=sum(bad[1][target][a.COUNT+i]<<i for i in range(25))
        a.putbits(bad[1][target],a.COUNT,count+1,25);reject('wrong-fetch-count-'+str(target),bad,local_valid=True)
    bad=copy.deepcopy(rows);bad[1][-1][a.COUNT]=1;reject('padding-CODE-receives',bad)
    # Change immutable metadata in EXEC. Local execution semantics unchanged;
    # exact fetch multiset must reject it against the independently bound CODE.
    bad=copy.deepcopy(rows);bad[0][0][a.KIND:a.KIND+6]=[0]*6
    kind=case['code'][0]['charge']['kind'];bad[0][0][a.KIND+(kind+1)%5]=1
    reject('EXEC-charge-kind-forgery',bad,local_valid=True)
    bad=copy.deepcopy(rows);bad[0][0][a.FN]=1;reject('EXEC-wrong-function',bad)
    bad=copy.deepcopy(rows);a.putbits(bad[0][0],a.PC,1,32);reject('EXEC-wrong-PC',bad)
    bad=copy.deepcopy(rows);bad[0][-1][a.DONE]=0;reject('EXEC-nonterminal-final',bad)
    bad=copy.deepcopy(rows);bad[0][0][a.GAS]=2;reject('EXEC-nonboolean-gas',bad)
    if len(case['exec_rows'])>2:
        event=case['exec_rows'][1];stack=[a.val(x) for x in event['before']['stack']];stack[-1]^=7
        bad=copy.deepcopy(rows);bad[0][1]=a.row_at(case['code'],1,stack,event['before']['gas']['g'],False,False)
        reject('coherent-wrong-stack',bad)
    for i in range(12,66):
        pub=spec['public'][:];pub[i]+=1;reject('boundary-'+str(i),pub=pub,local_valid=True)
    repeated=[i for i,row in enumerate(rows[1]) if sum(row[a.COUNT+j]<<j for j in range(25))>1]
    assert repeated, 'padding must exercise repeated lookup multiplicity'
    reports.append(dict(label=name,instructions=len(case['code']),log_rows=spec['log_rows'],rows=[len(t) for t in rows],
      widths=[t['width'] for t in spec['air']['tables']],constraints=[len(t['constraints']) for t in spec['air']['tables']],
      degrees=[max(expr_degree(e,t['width'],spec['air']['numPub']) for e in t['constraints']) for t in spec['air']['tables']],
      public_fields=len(spec['public']),public_canonical_u32_bytes=4*len(spec['public']),repeated_fetch_pc=repeated))
report=dict(status='PASS',cases=reports,negative_count=len(attacks),negative_cases=attacks,
 limitations=['Operand stack8 and function0 remain bounded.','New AIR whole-step Lean refinement not yet proved.','Actual prepare descriptor provenance is exported; generalized verifier-side checker still required.','Public CODE is linear-size and not included in reported proof bytes.','Reference full-witness evaluation is not cryptographic proof verification.'])
(out/'report.json').write_text(json.dumps(report,indent=2)+'\n');(out/'source-parity-input.json').write_text(json.dumps(parity))
print(json.dumps({k:v for k,v in report.items() if k!='negative_cases'}))
