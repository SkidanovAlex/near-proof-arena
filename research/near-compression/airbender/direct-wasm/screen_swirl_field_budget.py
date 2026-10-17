"""Exact necessary field-budget screens, NOT a SWIRL security calculator.

Replay two ungrounded terms from pinned SWIRL calculator: 3/|E| for
ordinary GKR and 2*columns/|E| for stacking (optimistically list size one).
The QROM column applies our hypothetical C Q^2 epsilon budget with C=1;
it does not assert that this compiler theorem applies to SWIRL.
"""
from fractions import Fraction
import gzip
import hashlib
import json
import math
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / 'results/swirl-security-review'
P = 2013265921


def main():
    sources = json.loads((OUT / 'sources.json').read_text())
    for source in sources['files']:
        raw = gzip.decompress((OUT / source['snapshot']).read_bytes())
        assert hashlib.sha256(raw).hexdigest() == source['sha256_raw']
    records = []
    for name, numerator in [('gkr_degree3', 3),
                            ('recursion_stacking_2000_columns', 4000),
                            ('app_stacking_30000_columns', 60000)]:
        for extension in range(4, 13):
            error = Fraction(numerator, P**extension)
            rbr_pass = error <= Fraction(1, 2**128)
            qrom_pass = 2**256 * error <= Fraction(1, 4)
            # Independently check the threshold decisions by integer arithmetic.
            assert rbr_pass == (numerator * 2**128 <= P**extension)
            assert qrom_pass == (numerator * 2**258 <= P**extension)
            records.append(dict(term=name, extension=extension,
                                optimistic_error=str(error),
                                rbr_bits=-math.log2(error),
                                rbr128_term_budget_pass=rbr_pass,
                                conditional_Q128_quarter_budget_pass=qrom_pass))
    result = dict(
        status='CONDITIONAL_PARTIAL_SCREEN', sources_revision=sources['revision'],
        source_pins_verified=len(sources['files']), records=records,
        scope='Necessary term-budget checks only; no attack or complete security bound.',
        exclusions=['other SWIRL terms', 'list sizes greater than one',
                    'hash/permutation security', 'quantum Fiat-Shamir applicability',
                    'grinding quantum analysis', 'recursive composition',
                    'extension construction and implementation', 'proof bytes',
                    'full NEAR semantics and capacity'],
        security_certified=False)
    (OUT / 'field-budget.json').write_text(json.dumps(result, indent=2)+'\n')
    for name in dict.fromkeys(r['term'] for r in records):
        rows = [r for r in records if r['term'] == name]
        print(name, 'min tested extension for RBR128:',
              next(r['extension'] for r in rows if r['rbr128_term_budget_pass']),
              'conditional Q128:', next(r['extension'] for r in rows
                                       if r['conditional_Q128_quarter_budget_pass']))


if __name__ == '__main__':
    main()
