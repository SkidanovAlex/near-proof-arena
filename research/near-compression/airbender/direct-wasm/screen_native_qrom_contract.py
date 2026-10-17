"""Exact conditional U-6 budget screen; never a security certificate.

SWIRL Cor. 4.2.6 gives Theta(Q * epsilon_fs), not a concrete constant.
We screen C * (Qeff**2 * epsilon_rbr + 3*Qeff*(Qeff**2+1)/2**384)
with explicit hypothetical C and verifier-query overhead. No theorem
applicability, recursive extraction bound or implementation is inferred.
"""
from fractions import Fraction
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / 'results/native-literal-security-comparison/qrom-contract.json'


def minimum_bits(bound):
    """Smallest nonnegative b with 2^-b <= bound; exact rational arithmetic."""
    assert bound > 0
    b = max(0, bound.denominator.bit_length() - bound.numerator.bit_length())
    while Fraction(1, 2**b) > bound:
        b += 1
    assert Fraction(1, 2**b) <= bound
    assert b == 0 or Fraction(1, 2**(b-1)) > bound
    return b


def main():
    target = Fraction(1, 2**128)
    algebra_budget = hash_budget = target / 4
    rows = []
    for constant in (1, 16, 256):
        for overhead in (0, 2**64):
            q = 2**64 + overhead
            rbr_limit = algebra_budget / (constant*q*q)
            degree = 1
            while Fraction(1, 2013265921**degree) > rbr_limit:
                degree += 1
            hash_numerator = 3*constant*q*(q*q+1)
            hash_error = Fraction(hash_numerator, 2**384)
            rows.append(dict(
                hypothetical_reduction_constant=constant,
                hypothetical_verifier_query_overhead=overhead,
                effective_query_bound=q,
                required_rbr_bits=minimum_bits(rbr_limit),
                rbr_error_limit=str(rbr_limit),
                optimistic_min_babybear_extension_degree_for_unit_numerator=degree,
                required_hash_bits=minimum_bits(hash_budget/hash_numerator),
                sha384_compiler_hash_error=str(hash_error),
                sha384_compiler_hash_budget_pass=hash_error <= hash_budget,
                residual_budget=str(target/2),
                security_certified=False))
    # Verify the evidence we attach to these hypothetical budgets, including
    # the actual serialized parent and its archived report's hash commitment.
    measured = []
    for suffix in ('', '-rate3', '-rate5'):
        folder = ROOT / ('results/native-literal-query128'+suffix)
        raw = (folder/'report.json').read_bytes()
        report = json.loads(raw)
        proof = (folder/'parent.proof').read_bytes()
        assert hashlib.sha256(proof).hexdigest() == report['sha256']['parent.proof']
        assert len(proof) == report['parent_bytes']
        assert report['security']['hash'] == 'Poseidon2'
        parent = next(x for x in report['native_vk_component_estimates']
                      if x['stage'] == 'parent')
        measured.append(dict(
            artifact=folder.name, report_sha256=hashlib.sha256(raw).hexdigest(),
            parent_bytes=len(proof), native_min_component_bits=parent['min_component'],
            selected_hash_contract_met=False, security_certified=False))
    result = dict(
        status='CONDITIONAL_BUDGET_SCREEN_NOT_CERTIFICATE',
        contract=dict(adversary_quantum_hash_queries=2**64,
                      maximum_failure_probability=str(target), hash='SHA-384',
                      proof_size_stretch_bytes_exclusive=300000,
                      source='docs/zk-formal/V3-D3A-STUDY.md U-6/U-7'),
        conditional_formula='C*(Qeff^2*epsilon_rbr + 3*Qeff*(Qeff^2+1)/2^384)',
        budget_allocation='quarter algebra, quarter compiler hash, half unresolved residual',
        field_screen_scope='Only the optimistic 1/field_cardinality term; no extension construction or complete proximity/LogUp bound.',
        sources=[dict(url='https://openvm.dev/swirl.pdf',
                      locator='Corollary 4.2.6, equations 4.9 and 4.10'),
                 dict(url='https://par.nsf.gov/servlets/purl/10510337',
                      locator='Fiat-Shamir Security of FRI and Related SNARKs, Corollary 4, p.32')],
        sensitivities=rows, measured_profiles=measured,
        unresolved=['explicit reduction constant and verifier-query overhead',
                    'compiler and transcript applicability to pinned implementation',
                    'quantum recursive knowledge extraction and resource accounting',
                    'all residual errors and adaptive statement budget',
                    'SHA-384 implementation at every proof layer and random-oracle assumption',
                    'actual-key RBR bounds after larger field/hash implementation',
                    'acceptance-to-execution Lean theorem and full NEAR workload'],
        security_certified=False)
    OUT.write_text(json.dumps(result, indent=2)+'\n')
    for r in rows:
        print('C=', r['hypothetical_reduction_constant'],
              'overhead=', r['hypothetical_verifier_query_overhead'],
              'RBR bits=', r['required_rbr_bits'],
              'hash bits=', r['required_hash_bits'])
    print('Measured artifacts verified:', len(measured), '; certification: false')


if __name__ == '__main__':
    main()
