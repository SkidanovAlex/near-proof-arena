"""Independent V2 evaluator over actual prepared control-flow execution traces.

Negative tests are witness/statement checks, not cryptographic proof-verifier
claims. All semantic inputs come from actual Lean prepare/step/runCall export.
"""
import argparse,copy,json,sys
from pathlib import Path
import prepared_control_air as a
ap=argparse.ArgumentParser();ap.add_argument('--reference-dir',required=True);ap.add_argument('--fixture',required=True);ap.add_argument('--legacy');ap.add_argument('--out',required=True);args=ap.parse_args()
sys.path.insert(0,args.reference_dir)
from reference import inspect,expr_degree
out=Path(args.out);out.mkdir(parents=True,exist_ok=True)
cases=json.load(open(args.fixture))['cases']
if args.legacy:cases+=json.load(open(args.legacy))['cases']
reports=[];attacks=[]
for case in cases:
    spec,rows=a.make(case);result=inspect(spec['air'],rows,spec['public'])
    assert result['accepted'],(case['label'],result['violations'][:3])
    name=case['label'];(out/(name+'-spec.json')).write_text(json.dumps(spec));(out/(name+'-rows.json')).write_text(json.dumps({'rows_by_table':rows}))
    def reject(label,bad=None,pub=None,local_valid=False):
        result=inspect(spec['air'],rows if bad is None else bad,spec['public'] if pub is None else pub)
        assert not result['accepted'],(name,label)
        if local_valid:assert not any(v[0]=='constraint' for v in result['violations']),(name,label,result['violations'][:3])
        attacks.append(dict(case=name,attack=label,local_constraints_still_valid=local_valid))
    # Every CODE target limb is authenticated, including skipped instructions.
    for pc in range(len(case['code'])):
        pub=spec['public'][:];pub[a.CODEPUB+a.RECORD*pc+27]+=1
        reject('public-target-'+str(pc),pub=pub,local_valid=True)
    for idx in range(12,66):
        pub=spec['public'][:];pub[idx]+=1;reject('public-boundary-'+str(idx),pub=pub,local_valid=True)
    for i,event in enumerate(case['exec_rows']):
        if event['instruction']['opcode']!=13 or event['status']!='continue':continue
        before=event['before'];values=[a.val(v) for v in before['stack']]
        taken=bool(values[-1]);target=before['frames'][0]['labels'][0][0]
        assert event['after']['frames'][0]['pc']==(target if taken else event['pc']+1)
        # Coherent changed condition witness recomputes inverse and bit rows.
        changed=values[:];changed[-1]=0 if taken else 1
        bad=copy.deepcopy(rows);bad[0][i]=a.row_at(case['code'],event['pc'],changed,before['gas']['g'],False,False,before['frames'][0]['labels'])
        reject('coherent-opposite-condition',bad)
        # Next row has valid descriptor and local arithmetic, but wrong chosen PC.
        after=event['after'];other=event['pc']+1 if taken else target
        bad=copy.deepcopy(rows);bad[0][i+1]=a.row_at(case['code'],other,[a.val(v) for v in after['stack']],after['gas']['g'],False,False,after['frames'][0]['labels'])
        reject('coherent-wrong-branch-PC',bad)
        bad=copy.deepcopy(rows);bad[0][i][a.NONZERO]^=1;reject('forged-nonzero-selector',bad)
        bad=copy.deepcopy(rows);bad[0][i][a.INVERSE]=(bad[0][i][a.INVERSE]+1)%a.P
        if taken:reject('forged-condition-inverse',bad)
        bad=copy.deepcopy(rows);a.putbits(bad[0][i],a.LTARGET,target+1,32);reject('coherent-wrong-label-target',bad)
        bad=copy.deepcopy(rows);bad[0][i][a.HEIGHT:a.HEIGHT+9]=[0]*9;bad[0][i][a.HEIGHT]=1;reject('coherent-wrong-saved-height',bad)
        if taken:
            vals=[a.val(v) for v in after['stack']]+[13]
            bad=copy.deepcopy(rows);bad[0][i+1]=a.row_at(case['code'],target,vals,after['gas']['g'],False,False,after['frames'][0]['labels'])
            reject('taken-branch-retains-discarded-word',bad)
            vals=[a.val(v) for v in after['stack']];vals[0]^=1
            bad=copy.deepcopy(rows);bad[0][i+1]=a.row_at(case['code'],target,vals,after['gas']['g'],False,False,after['frames'][0]['labels'])
            reject('taken-branch-corrupts-preserved-prefix',bad)
    for i,event in enumerate(case['exec_rows']):
        if event['instruction']['opcode']==11 and event['status']=='continue':
            bad=copy.deepcopy(rows);bad[0][i+1][a.DONE]=1;reject('nested-end-returns-function',bad)
        if event['instruction']['opcode']==2 and event['status']=='continue':
            bad=copy.deepcopy(rows);bad[0][i+1][a.LABEL]=0;reject('block-not-pushed',bad)
    reports.append(dict(label=name,instructions=len(case['code']),executed=len(case['exec_rows']),log_rows=spec['log_rows'],widths=[t['width'] for t in spec['air']['tables']],constraints=[len(t['constraints']) for t in spec['air']['tables']],degrees=[max(expr_degree(e,t['width'],spec['air']['numPub']) for e in t['constraints']) for t in spec['air']['tables']],public_fields=len(spec['public']),error=case['error']))
report=dict(status='PASS',cases=reports,negative_count=len(attacks),negative_cases=attacks,limitations=['Single defined function, stack8 and one nested void block remain bounded.','Loops, deeper branches, local variables and calls are unsupported.','Supported control AIR-to-runCall/public-output refinement is proved separately; these tests do not establish cryptographic acceptance-to-HoldsP.','Public CODE including prepared end target has linear size; actual PREP remains outside AIR.','Full witness reference checks are not cryptographic proof verification.'])
(out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k!='negative_cases'}))
