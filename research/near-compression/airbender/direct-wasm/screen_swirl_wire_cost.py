"""Fixed-slot sensitivity of measured SWIRL proofs; no security certificate.

Changing extension degree, hash parameters or queries changes the verifier
relation itself. These projections keep that work frozen, deliberately, and
cannot establish feasibility or a universal lower bound for a redesigned PCS.
"""
import gzip
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / 'results/swirl-security-review/census'


def main():
    data = json.loads((OUT / 'counts.json').read_text())
    for artifact in data['artifacts']:
        raw = gzip.decompress((OUT / artifact['file']).read_bytes())
        assert hashlib.sha256(raw).hexdigest() == artifact['raw_sha256']
    rows = []
    for d in data['records']:
        assert d['bytes'] == d['framing'] + 4*d['bf'] + 16*d['ef'] + 32*d['digests']
        assert d['unique_digests'] <= 65536  # two-byte dictionary references
        for extension in (4, 5, 8, 9, 10, 12):
            for digest_bytes in (32, 49, 52, 64):
                fixed = d['framing'] + 4*d['bf'] + 4*extension*d['ef']
                ordinary = fixed + digest_bytes*d['digests']
                ideal_dictionary = fixed + digest_bytes*d['unique_digests']
                dictionary = ideal_dictionary + 4 + 2*d['digests']
                rows.append(dict(stage=d['stage'], extension=extension,
                                 digest_bytes=digest_bytes, ordinary_bytes=ordinary,
                                 dictionary_bytes=dictionary,
                                 dictionary_free_references_bytes=ideal_dictionary))
    report = dict(status='FIXED_SLOT_SENSITIVITY_ONLY', rows=rows,
                  security_certified=False,
                  caveats=['No larger extension or hash implementation',
                           'No new query schedule or quantum soundness analysis',
                           'Frozen verifier layout and duplicate pattern',
                           'Dictionary codec is modeled, not implemented',
                           'Frontier multiproofs can differ from digest dictionaries',
                           'No NEAR public binding or complete root wrapper'])
    (OUT / 'cost-screen.json').write_text(json.dumps(report, indent=2)+'\n')
    for row in rows:
        if row['stage'] == 'root_geometry_babybear_hash' and row['extension'] in (4,9) and row['digest_bytes'] in (32,52):
            print(json.dumps(row))


if __name__ == '__main__':
    main()
