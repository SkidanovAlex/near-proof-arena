"""Conditional query-budget screen for the measured SWIRL root geometry.

No QROM theorem is instantiated here. We apply the research assumption
C*Q^2*epsilon with Q=2^128 to the pinned m=1 agreement formula. All
authentication and all column-opening replacement work are free. This is
a finite configuration screen, not an attack or a universal lower bound.
"""
from fractions import Fraction as F
import json
import gzip
import hashlib
import math
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / 'results/swirl-security-review/query-payload'
P = 2013265921


def mass_bounds(log_rate, log_domain):
    # Exact rational enclosure of sqrt(rate), including irrational rate128.
    scale = 10**40
    radicand = (1 << log_rate) * scale**2
    low = math.isqrt(radicand)
    high = low if low*low == radicand else low+1
    assert low*low <= radicand <= high*high
    alpha_low, alpha_high = F(3*scale, 2*high), F(3*scale, 2*low)
    domain = 1 << log_domain
    residue = P % domain
    def mass(alpha):
        return alpha*F(P-residue, P) + F(min(alpha*domain, residue), P)
    return mass(alpha_low), mass(alpha_high)


def minimal_queries(lo, hi, target):
    q = 0
    while hi**q > target:
        q += 1
    # Both endpoints certify the SAME minimum; no floating-point rounding.
    assert hi**q <= target
    assert q > 0 and lo**(q-1) > target
    return q


def main():
    sources = json.loads((OUT / 'sources.json').read_text())
    for a in sources['artifacts']:
        raw = gzip.decompress((OUT / a['file']).read_bytes())
        assert hashlib.sha256(raw).hexdigest() == a['raw_sha256']
    census = json.loads((ROOT / 'results/swirl-security-review/census/counts.json').read_text())
    d = next(r for r in census['records'] if r['stage'] == 'root_geometry_babybear_hash')
    shape = json.loads((OUT / 'shape.json').read_text())
    raw = gzip.decompress((OUT / 'query-shape.log.gz').read_bytes())
    assert hashlib.sha256(raw).hexdigest() == shape['log_sha256']
    assert shape['old_queries'] == [61,30,20]
    assert shape['first_base_per_query'] == 240
    assert shape['later_values_per_query'] == [16,16]
    column_count = 2694
    fixed_base = d['bf'] - 61*240
    fixed_ext = d['ef'] - column_count - 16*(30+20)
    assert (fixed_base, fixed_ext) == (17,1214)
    bounds = [mass_bounds(r,n) for r,n in zip([4,7,10],[20,19,18])]
    rows = []
    for log_c in (0,8):
        for grinding_credit in (0,15):
            for allocation, divisor in [('relaxed_half_each',2),('query_quarter_split_three',12)]:
                target = F(2**grinding_credit, divisor*2**(256+log_c))
                queries = [minimal_queries(lo,hi,target) for lo,hi in bounds]
                for extension in (5,9,10,12):
                    base_count = fixed_base + 240*queries[0]
                    extension_count = fixed_ext + 16*sum(queries[1:])
                    byte_count = d['framing'] + 4*base_count + 4*extension*extension_count
                    rows.append(dict(log2_C=log_c, nominal_grinding_credit=grinding_credit,
                                     allocation=allocation, queries=queries, extension=extension,
                                     base_elements=base_count, extension_elements=extension_count,
                                     all_auth_and_column_reduction_free_bytes=byte_count,
                                     fails_size_even_with_free_components=byte_count>=300000))
    result = dict(status='CONDITIONAL_QUERY_PAYLOAD_SCREEN', rows=rows,
                  exact_interval_minima_verified=True, security_certified=False,
                  exclusions=['Full QROM applicability and losses', 'All hash security terms',
                              'All authentication bytes', 'All column-replacement bytes',
                              'Changed recursive circuit layout', 'NEAR and VM public binding'],
                  notes=['15-bit credit is hypothetical, not a quantum grinding theorem.',
                         'Relaxed half-each grants the whole success budget to each term.',
                         'Failure concerns this accounting and fixed geometry, not an attack.'])
    (OUT / 'report.json').write_text(json.dumps(result,indent=2)+'\n')
    for row in rows:
        if row['extension']==9 and row['log2_C']==0:
            print(json.dumps(row))


if __name__ == '__main__':
    main()
