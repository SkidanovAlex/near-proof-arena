"""Conditional work-factor screen, not an instantiated QROM reduction.
Uses the existing ledger shape C*(Q^2*epsilon+3*(Q^3+Q)/2^h).
Q includes verification/reduction oracle overhead, not only adversary queries.
"""
import hashlib
import json
from fractions import Fraction as F
from pathlib import Path
from pq384_ext8_reference import P
ROOT=Path(__file__).resolve().parents[2]


def bound(Q,epsilon,h,C):
    return C*(Q*Q*epsilon+F(3*(Q**3+Q),2**h))


def first(predicate):
    return next(i for i in range(1,4097) if predicate(i))


def main():
    path=ROOT/'results/code-switch-algebra-ledger.json'
    ledger=json.loads(path.read_text());rows=[]
    for r in ledger['records']:
        A=F(r['algebra_numerator']);tail=sum((F(s['query']) for s in r['stages']),F(0))
        for c in (0,8):
            C=2**c;epsilon=A/P**8+tail
            b=0
            while bound(2**(b+1),epsilon,384,C)<=F(1,2):b+=1
            assert bound(2**b,epsilon,384,C)<=F(1,2)
            assert bound(2**(b+1),epsilon,384,C)>F(1,2)
            Q=2**128
            # Allocate <=1/4 to Q²*epsilon and <=1/4 to hashing.
            target=F(1,4*C*Q*Q)
            # Half of epsilon budget to algebra, half to query tails.
            extension=first(lambda e:A/P**e<=target/2)
            h=first(lambda h:F(3*C*(Q**3+Q),2**h)<=F(1,4))
            n=len(r['stages']);required=[]
            schedule=json.loads((ROOT/'results/weighted-code-switch-screen.json').read_text())
            stages=next(x for x in schedule['results'] if x['regime']=='johnson' and x['query_bits_per_stage']==r['query_bits_per_stage'])['best']['path']
            for s in stages:
                import math
                factor=F(21,20*math.isqrt(s['rate']))
                q=first(lambda q:factor**q<=target/(2*n))
                assert q==1 or factor**(q-1)>target/(2*n)
                required.append(q)
            rows.append(dict(old_query_bits_per_stage=r['query_bits_per_stage'],assumed_log2_C=c,
                nominal_max_integer_log2_Q_for_half_success=b,
                minimum_arithmetic_extension_for_half_epsilon_budget=extension,
                minimum_hash_bits_for_quarter_success_budget=h,
                isolated_required_stage_queries_at_logQ128=required,
                target_log2_Q=128,target_success_probability='1/2',
                source_algebra_frozen=True))
    out=dict(status='CONDITIONAL_WORK_FACTOR_SCREEN_NOT_SECURITY_CERTIFICATE',rows=rows,
        input_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
        formula='C*(Q^2*epsilon+3*(Q^3+Q)/2^h)',
        primary_source='https://www.pratyush.site/publication/soundnessnotions/soundnessNotions.pdf',
        primary_source_sha256='e95696372fd879e8ac3c0a2d2612cfa3d168bc50d8b68fcceb19b745a3bd27a1',
        theorem_route='BCS compilation of round-by-round sound IOP; CMS19 Theorem8.6 via Soundness Notions Corollary1.6. Exact constants and compiler correspondence uninstantiated.',
        obligations=['Define doomed states at every transcript boundary and show false statements begin doomed.',
          'For every fixed doomed prefix and every next prover message, bound escape over the next independent challenge.',
          'Show all accepting terminal transcripts are non-doomed; connect to full NEAR transition semantics.',
          'Prove adaptive committed-oracle extraction and the implemented transcript is the required BCS transform.',
          'Instantiate explicit reduction constants, verifier overhead, hash domains and uniform challenge sampling.',
          'Establish knowledge soundness separately if recursive extraction requires it.'],
        scope='Nominal C=1 and256 sensitivity; neither is a certified constant. Partial error is hypothetically substituted for RBR epsilon, NOT justified by existing total-path bounds. '
          'Failure to certify is not an attack or a security upper bound. New extension/hash/query minima hold other algebra counts fixed; changing parameters requires recomputation. '
          'Only Ext8 implemented here. Larger extension, digest and source/auxiliary widths change proof size. SHA384 is not upgraded by this report. No gate changed.')
    (ROOT/'results/code-switch-qrom-workfactor.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(rows,indent=2))

if __name__=='__main__':main()
