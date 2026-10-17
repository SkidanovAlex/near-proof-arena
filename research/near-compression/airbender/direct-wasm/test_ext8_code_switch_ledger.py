"""Check arithmetic against independently transcribed upstream log formulas.
Passing this test does not validate the theorem-to-protocol mapping.
"""
import argparse,json,math,gzip
from fractions import Fraction as F
from pathlib import Path
import screen_ext8_code_switch as m


def main():
    p=argparse.ArgumentParser();p.add_argument('--report',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    checks=0
    for regime in ('upstream_unique','upstream_johnson'):
        for logB in (2,3,4,7,8):
            for k in (1,2,4):
                B=1<<logB;D=1<<18;bits=227;nextB=B*(1<<(k-1));q=m.query_count(regime,B,bits)
                t,passed,ledger=m.slots(regime,D,B,k,nextB,q,bits)
                log_field=8*math.log2(m.P);log_message=18-k
                expected=log_field-log_message-logB
                if regime=='upstream_johnson':expected=log_field-math.log2(2*10.5**5/3)-log_message-2.5*logB
                assert abs(ledger['mca_bits']-expected)<1e-10
                factor=(1+1/B)/2 if regime=='upstream_unique' else 1.05/math.sqrt(B)
                assert factor**q<=2.0**(-bits)*(1+1e-12) and factor**(q-1)>2.0**(-bits)
                L=1 if regime=='upstream_unique' else 10*nextB
                error=lambda n:F(L*(L-1),2)*F((D>>k)-1,m.FIELD)**n
                assert t>=1 and error(t)<=F(1,1<<bits)
                assert t==1 or error(t-1)>F(1,1<<bits)
                assert passed['mixing']==(F((t+q*(1<<k))*L,m.FIELD)<=F(1,1<<bits));checks+=1
    t,checks_unique,ledger=m.slots('upstream_unique',32,4,2,8,16,128)
    assert t==1 and all(checks_unique.values())
    assert abs(ledger['mca_bits']+math.log2(float(F(32,m.FIELD))))<1e-10
    t,bad,_=m.slots('upstream_johnson',1<<18,256,1,256,57,227)
    assert t==2 and not bad['mca']
    report=json.loads(gzip.decompress(a.report.read_bytes()) if a.report.suffix=='.gz' else a.report.read_bytes());runs=0
    for record in report['records']:
        for run in record['runs']:
            bound=sum((F(s['conditional_error_upper']) for s in run['stages']),F(0))
            assert bound==F(run['conditional_error_upper'])
            assert run['charged_terms']==sum(2*s['fold_bits']+3 for s in run['stages'])
            assert run['conditional_budget_pass']==(run['conditional_slots_pass'] and bound<=F(1,1<<record['target_bits']))
            assert all(s['queries']==m.query_count(record['regime'],s['blowup'],run['slot_bits']) for s in run['stages'])
            runs+=1
    result=dict(status='PASS',independent_formula_cases=checks,exact_ledger_runs=runs,unique_known_case=True,johnson_field_budget_rejection=True,scope='Arithmetic/source-formula validation only; no theorem mapping or quantum certificate.')
    a.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))

if __name__=='__main__':main()
