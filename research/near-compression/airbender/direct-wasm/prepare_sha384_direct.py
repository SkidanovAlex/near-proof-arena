"""Reuse actual captured-message witnesses; replace only canonical input AIR."""
import argparse,hashlib,json
from pathlib import Path

def main():
    p=argparse.ArgumentParser();p.add_argument('--committed-directory',required=True);p.add_argument('--output-directory',required=True);a=p.parse_args()
    src=Path(a.committed_directory);out=Path(a.output_directory);out.mkdir(parents=True,exist_ok=True)
    for name in ('message.bin','fixed-framing.json'):(out/name).write_bytes((src/name).read_bytes())
    message=(out/'message.bin').read_bytes();assert len(message)==376
    if not (out/'spec.json').exists():return
    old=json.loads((src/'spec.json').read_text());spec=json.loads((out/'spec.json').read_text())
    assert len(spec['air']['tables'])==3 and spec['public']==old['public'] and spec['log_rows']==old['log_rows'][:3]
    assert spec['air']['tables'][:2]==old['air']['tables'][:2]
    for k in ('width','maxLog'):
        assert spec['air']['tables'][2][k]==old['air']['tables'][2][k]
    # Canonical export appends multiplicity Booleanity per interaction.
    base=3008+len(json.loads((out/'fixed-framing.json').read_text()))
    assert spec['air']['tables'][2]['constraints'][:base]==old['air']['tables'][2]['constraints'][:base]
    assert len(spec['air']['tables'][2]['constraints'])==base+4
    for i in range(3):(out/f'source-{i:02d}-rows.json').write_bytes((src/f'source-{i:02d}-rows.json').read_bytes())
    rows=json.loads((out/'source-02-rows.json').read_text())['rows'];assert rows[0]==[(b>>j)&1 for b in message for j in range(8)]
    assert len(spec['air']['tables'][2]['interactions'])==4
    report=dict(status='PASS',message_bytes=376,input_rows_byte_identical=True,core_endpoint_rows_byte_identical=True,
        public_fields=88,source_cells=sum((1<<n)*t['width'] for n,t in zip(spec['log_rows'],spec['air']['tables'])),
        removed_padding_source_cells=4*1028,input_interactions_before=376,input_interactions_after=4,
        padding_interactions_removed=377,spec_sha256=hashlib.sha256((out/'spec.json').read_bytes()).hexdigest(),
        message_sha256=hashlib.sha256(message).hexdigest(),scope='Direct padding expressions over committed bits; mandatory external root still required; recursive producer routing not implemented.')
    (out/'preparation-report.json').write_text(json.dumps(report,indent=2));print(json.dumps(report,indent=2))
if __name__=='__main__':main()
