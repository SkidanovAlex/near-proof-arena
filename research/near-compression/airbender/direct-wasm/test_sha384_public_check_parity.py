"""Independent executable Lean/Python statement-check parity; no proof checks.

The Lean fixture refuses raw noncanonical field encodings. Those cases are
checked separately against the Python wrapper, never reduced modulo P.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys

p = argparse.ArgumentParser()
p.add_argument('--root', type=Path, required=True, help='root research/near-compression package')
p.add_argument('--statement', type=Path, required=True)
p.add_argument('--out', type=Path, required=True)
a = p.parse_args()
sys.path.insert(0, str(a.root / 'airbender/direct-wasm'))
from verify_sha384_direct import check_public
from pq384_primitives import P

statement = json.loads(a.statement.read_text())
public = statement.get('spec', statement)['public']
assert check_public(public)
a.out.mkdir(parents=True, exist_ok=True)
cases = []
def add(label, values, expected):
    cases.append(dict(label=label, public=values, expected=expected))
def changed(i, value):
    values = public.copy(); values[i] = value
    return values
add('actual-statement', public, True)
for i in range(48):
    add(f'digest-{i}-256', changed(i, 256), False)
    add(f'digest-{i}-P-minus-one', changed(i, P-1), False)
    # A different byte digest is valid syntax, not a valid hash proof.
    add(f'digest-{i}-different-byte', changed(i, public[i] ^ 1), True)
for i in range(48, 88):
    add(f'suffix-{i}-increment', changed(i, public[i]+1), False)
add('truncated', public[:-1], False)
add('appended', public+[0], False)
raw = []
for i in (0, 48, 52, 87):
    for name, value in [('negative', -1), ('field-alias', public[i]+P),
                        ('bool', bool(public[i])), ('float', float(public[i])),
                        ('string', str(public[i]))]:
        raw.append(dict(label=f'raw-{i}-{name}', public=changed(i, value)))
def accepts(values):
    try:
        return check_public(values)
    except ValueError:
        return False
fixture = a.out / 'cases.json'
fixture.write_text(json.dumps(cases, indent=2)+'\n')
lean = Path(__file__).resolve().parents[2] / 'SHA384DirectPublicCheckExport.lean'
output = subprocess.check_output(['lake','env','lean','--run',str(lean),str(fixture.resolve())], cwd=a.root)
results = json.loads(output)
assert len(results) == len(cases)
for case, result in zip(cases, results):
    assert result['label'] == case['label']
    assert result['accepted'] == accepts(case['public']) == case['expected'], case['label']
    if result['accepted']:
        assert result['decoded_digest'] == case['public'][:48]
for case in raw:
    assert not accepts(case['public']), case['label']
(a.out/'lean-results.json').write_bytes(output)
(a.out/'raw-cases.json').write_text(json.dumps(raw,indent=2)+'\n')
report = dict(status='PASS', canonical_cases=len(cases),
              accepted=sum(c['expected'] for c in cases),
              rejected=sum(not c['expected'] for c in cases),
              raw_encoding_rejections=len(raw),
              statement_sha384=hashlib.sha384(a.statement.read_bytes()).hexdigest(),
              scope='Exact public syntax parity only; changed byte digests remain eligible. No proof acceptance or hash security claim.')
(a.out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report))
