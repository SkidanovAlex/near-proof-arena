"""Exact arithmetic for the existing source-query interface, not full attacks."""
import argparse,json
from fractions import Fraction
from pathlib import Path

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
    # One fixed zero candidate; source-query values agree on96of128seeds.
    source=[0]*96+[1]*32;matches=sum(value==0 for value in source);assert matches==96
    ratio=Fraction(matches,len(source));target=Fraction(1,2**128);q=0
    while ratio**q>target:q+=1
    assert q==309 and ratio**(q-1)>target and ratio**q<=target
    rows=[]
    for queries in (4,8,32,64,128,308,309):
        probability=ratio**queries
        rows.append(dict(queries=queries,numerator=str(probability.numerator),denominator=str(probability.denominator),
            meets128_ideal_query_bits=probability<=target))
    assert ratio**4==Fraction(81,256)
    report=dict(status='EXACT_INTERFACE_BUDGET_CHECK',seeds=128,agreements=96,strict_threshold=97,min_queries128_ideal=309,
        four_query_pass_fraction='81/256',cases=rows,
        formal_theorems=['rate_shift_truthful_ood_iff','rate_shift_truthful_ood_query_count','rate_shift_source_threshold_sharp'],
        scope='Tight count for same-candidate/source-query interface when old functional and truthful OOD equation hold. Not a full protocol attack or lower bound on WHIR/rate-shift designs; earlier oracle/fold relations can supply stronger premises. No quantum security claim.')
    args.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items() if k!='cases'}))
if __name__=='__main__':main()
