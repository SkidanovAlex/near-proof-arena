"""Actual independent V2 evaluator checks and coherent bounded-machine attacks."""
import argparse,copy,json,sys
from pathlib import Path
import prepared_function_air as a
ap=argparse.ArgumentParser();ap.add_argument('--reference-dir',required=True);ap.add_argument('--fixture',required=True);ap.add_argument('--report',required=True);args=ap.parse_args()
sys.path.insert(0,args.reference_dir)
import scheduled_bus_whir as protocol
# The existing independent canonical np-air-v2 full witness interpreter.
reference=protocol.public_messages.__globals__
inspect=reference['inspect'] if 'inspect' in reference else None
if inspect is None:
    sys.path.insert(0,str(Path(args.reference_dir).parent/'generic-air'))
    from reference import inspect
cases=json.load(open(args.fixture))['cases'];accepted=[];attacks=[]
for case in cases:
    spec,rows=a.make(case)
    assert protocol.validate(spec)==[6]
    assert inspect(spec['air'],[rows],spec['public'])['accepted']
    accepted.append(case['label'])
    def reject(label,changed=None,pub=None):
        result=inspect(spec['air'],[changed if changed is not None else rows],pub if pub is not None else spec['public'])
        assert not result['accepted'],label
        attacks.append(case['label']+':'+label)
    for field in range(8,8+2*a.MSG):
        pub=spec['public'][:];pub[field]=(pub[field]+1)%a.P
        reject('boundary-field-'+str(field),pub=pub)
    for pc in range(len(case['code'])):
        pub=spec['public'][:];pub[a.CODEPUB+10*pc+6]+=1
        # Fee changes to unexecuted PC after an abort are legitimately irrelevant.
        if pc<len(case['exec_rows']):reject('prepared-fee-'+str(pc),pub=pub)
    bad=copy.deepcopy(rows);bad[-1][a.DONE]=0;reject('nonterminal-final',bad)
    if len(case['exec_rows'])==5:
        for clock in (1,2,3):
            before=case['exec_rows'][clock]['before'];stack=[a.val(v) for v in before['stack']]
            stack[-1]=(stack[-1]+7)%2**32
            bad=copy.deepcopy(rows);bad[clock]=a.row_at(case['code'],clock,stack,before['gas']['g'],False,False)
            reject('coherent-stack-'+str(clock),bad)
        pub=spec['public'][:];pub[a.CODEPUB+4]=(pub[a.CODEPUB+4]+1)%65536
        reject('code-immediate',pub=pub)
        bad=copy.deepcopy(rows);bad[2][a.SP+2]=0;bad[2][a.SP+1]=1;reject('stack-underflow',bad)
        bad=copy.deepcopy(rows);bad[2][a.PC+2]=0;bad[2][a.PC+3]=1;reject('skip-add-fetch',bad)
        bad=copy.deepcopy(rows);bad[0][a.GAS]=2;reject('nonboolean-gas',bad)
report=dict(status='PASS',honest_cases=accepted,negative_count=len(attacks),negative_cases=attacks,
            width=a.WIDTH,constraints=len(a.air()['tables'][0]['constraints']),degree=6,
            public_fields=len(spec['public']),real_boundary_buses=2,
            limitations=['Public CODE derivation from original Wasm is checked outside AIR.','No Lean whole-machine refinement theorem yet.','Fixed16instruction/8i32stack no-host subset.','Not a D3 transition proof or security claim.'])
Path(args.report).write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items() if k!='negative_cases'}))
