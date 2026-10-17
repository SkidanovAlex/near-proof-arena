#!/usr/bin/env python3
"""Conditional resource ledger for C*(Q^2 eps+3(Q^3+Q)/2^kappa).
C is symbolic: user parameter logC is a chosen upperbound log2C, not a measured
reduction constant. Not instantiated security for our current transcript.
"""
import argparse,json
from pathlib import Path
from fractions import Fraction as F
P=2013265921;E=1048572

def first(pred):
    for n in range(1,4097):
        if pred(n):return n
    raise ValueError('budget')
def case(b,c):
    Q=2**b;target=130+2*b+c
    k=first(lambda k:E*2**target<=P**k)
    q=first(lambda q:3**q*2**target<=4**q)
    digest=first(lambda n:3*(Q**3+Q)*2**(129+c)<=2**n)
    extraction=F(E,P**8)*Q**2*2**c
    return dict(adversary_queries_log2=b,assumed_reduction_constant_log2_upper_bound=c,
      target_final_advantage='2^-128',each_field_query_term_target_bits=target,
      minimum_arithmetic_extension_degree=k,minimum_current_tail_queries=q,minimum_hash_bits_for_hash_half_budget=digest,
      Ext8_extraction_with_Q_squared=dict(numerator=extraction.numerator,denominator=extraction.denominator),
      Ext8_field_quarter_budget_pass=extraction<=F(1,2**130),
      SHA384_hash_half_budget_pass=3*(Q**3+Q)*2**(129+c)<=2**384)
if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
    out=dict(formula='epsilonQ <= C*(Q^2*epsilonRBR+3*(Q^3+Q)/2^kappa)',
      applicability='Shape of FRI Cor4.3 upperbound after replacing its Θconstant by explicitC. Must establish actual reductionconstant and protocol hypotheses; currently notinstantiated.',
      cases=[case(b,c) for c in (0,8) for b in (32,64,128)],
      ledger='Each field/query term<=2^-(130+2logQ+logC) allocates combinedQ²term<=2^-129; hash<=2^-129. Upstream errors not allocated.',
      interpretation='128bit workfactor concerns cost for constant success, not advantage2^-128 after2^128queries. This report deliberately specifies both resource and advantage. C=1 scenarios are nominal optimistic reference, not certifiedconstants.',
      extensions='Minimumdegrees7/9/14 etc are arithmetic only; onlyExt8 currently certified/executable here. Do not infer polynomial irreducibility or implementation at otherdegrees.')
    a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps([{k:v for k,v in x.items() if k!='Ext8_extraction_with_Q_squared'} for x in out['cases']],indent=2))
