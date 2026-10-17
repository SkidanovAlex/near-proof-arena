"""Couple existing conditional security budgets to binary PCS geometry.

This is a design screening calculation, not a security or size certificate.
No new field implementation or Fiat-Shamir reduction is assumed established.
"""
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path
from estimate_ext8_multiproof_geometry import measure
from qrom_resource_ledger import case, first, P, E

ROOT = Path(__file__).resolve().parents[2]

def priced(degree, queries, extension, digest_bytes, seed):
    raw = measure(degree, queries, seed)
    field_bytes = 4 * extension
    leaf_bytes = sum(row['unique_openings'] * (8 if i == 0 else 2 * field_bytes)
                     for i, row in enumerate(raw['levels']) if row['degree'] > 1)
    hash_bytes = sum(row['frontier_hashes'] * digest_bytes for row in raw['levels'])
    fixed = (degree.bit_length()-1) * (3*field_bytes+digest_bytes)+field_bytes+digest_bytes
    return fixed+leaf_bytes+hash_bytes

def run():
    # Preserve the existing model exactly for its implemented field/hash widths.
    for degree in (32,1024,131072,262144):
        for seed in range(8):
            assert priced(degree,314,8,48,seed)==measure(degree,314,seed)['estimated_payload_bytes']
    profiles = [dict(name='interactive_only_existing_ext8', queries=314, extension=8,
                     digest_bytes=48, security='Isolated replay bound; no QROM certification')]
    for b in (32,64,128):
        ledger=case(b,0)
        profiles.append(dict(name=f'conditional_Q2pow{b}_advantage2powminus128_C1',
            queries=ledger['minimum_current_tail_queries'],
            extension=max(8,ledger['minimum_arithmetic_extension_degree']),
            digest_bytes=max(48,(ledger['minimum_hash_bits_for_hash_half_budget']+7)//8),
            security='Uninstantiated reduction; arithmetic field/hash sizes only'))
    # Nominal 128-bit constant-success query-workfactor scenario:
    # epsilonQ <= 1/2 at Q=2^128. Each interactive constituent gets 1/8,
    # leaving 1/4 for the hash term. Applicability and C=1 remain unproved.
    Q=2**128
    target=3+2*128
    extension=first(lambda k:E*2**target<=P**k)
    queries=first(lambda q:3**q*2**target<=4**q)
    digest_bits=first(lambda n:3*(Q**3+Q)*4<=2**n)
    profiles.append(dict(name='conditional_Q2pow128_advantage_half_C1',queries=queries,
        extension=extension,digest_bytes=(digest_bits+7)//8,
        security='Constant-success query-workfactor scenario; reduction and constant NOT established'))
    for profile in profiles:
        profile['sizes']=[]
        for log_degree in range(5,19):
            degree=2**log_degree
            sizes=[priced(degree,profile['queries'],profile['extension'],profile['digest_bytes'],s) for s in range(8)]
            profile['sizes'].append(dict(degree=degree,min_bytes=min(sizes),max_bytes=max(sizes),
                remaining_at_max_bytes=300000-max(sizes)))
        profile['largest_tested_degree_all_seeds_below_limit']=max(
            (r['degree'] for r in profile['sizes'] if r['max_bytes']<300000),default=None)
    inputs=['estimate_ext8_multiproof_geometry.py','qrom_resource_ledger.py']
    return dict(status='DESIGN_SCREEN_ONLY',byte_limit=300000,profiles=profiles,
        source_sha256={n:hashlib.sha256(Path(__file__).with_name(n).read_bytes()).hexdigest() for n in inputs},
        exclusions=['Framing and trusted statement transport','GKR and recursive verifier overhead',
            'Full NEAR witness validation and 1-Petagas execution','Upstream errors and actual quantum reduction constants'],
        conclusions=['Current binary-fold geometry exceeds the entire byte budget at large tested dimensions even before composition.',
            'Do not fund serialization-only optimization as the primary route to the requested target.',
            'Rate-shift remains a research candidate, pending scalable extraction and prior-domain transfer; this model does not evaluate its size.'],
        cautions=['Simulated seeds are neither universal lower bounds nor worst-case size guarantees.',
            'Degrees are PCS coefficient counts, not a demonstrated mapping from Petagas.',
            '128-bit workfactor is not the same requirement as advantage2^-128 at a specified query budget.',
            'Only Ext8/SHA384 are implemented in this comparison; larger widths are hypothetical.',
            'No proof of impossibility for binary protocols or alternative parameterizations.'])

if __name__=='__main__':
    report=run()
    scenario=report['profiles'][-1]
    Q=2**128
    k=scenario['extension'];q=scenario['queries'];h=8*scenario['digest_bytes']
    field=Q*Q*F(E,P**k);query=Q*Q*F(3,4)**q;hash_term=3*F(Q**3+Q,2**h)
    assert field<=F(1,8) and query<=F(1,8) and hash_term<=F(1,4)
    assert field+query+hash_term<=F(1,2)
    assert Q*Q*F(E,P**(k-1))>F(1,8)
    assert Q*Q*F(3,4)**(q-1)>F(1,8)
    assert 3*F(Q**3+Q,2**(h-8))>F(1,4)
    report['independent_check']=dict(status='PASS',method='Fraction arithmetic checks allocated terms and minimal integer parameters independently of integer search predicates.',implemented_protocol_security=False)
    report['analysis_source_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    output=ROOT/'results/compression-feasibility.json'
    output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps([dict(name=p['name'],queries=p['queries'],extension=p['extension'],
        digest_bytes=p['digest_bytes'],largest_tested_degree=p['largest_tested_degree_all_seeds_below_limit'],
        large_sizes=[r for r in p['sizes'] if r['degree']>=131072]) for p in report['profiles']],indent=2))
