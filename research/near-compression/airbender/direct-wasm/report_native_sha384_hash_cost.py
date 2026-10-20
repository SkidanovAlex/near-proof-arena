"""Compare actual verified native Wasm artifacts; no security/performance inference."""
from pathlib import Path
import json,hashlib
ROOT=Path(__file__).resolve().parents[2]
rows=[]
for suffix in ['', '-batched', '-compact']:
    p=ROOT/('results/native-literal-sha384-ext12'+suffix)
    r=json.loads((p/'report.json').read_text())
    for name,digest in r['sha256'].items():
        assert hashlib.sha256((p/name).read_bytes()).hexdigest()==digest,(p,name)
    assert r['witness_independent_replay'] and r['public_mutations_rejected']==6
    assert not r['security']['certified']
    assert r['security']['query_target_bits']==268 and r['security']['grinding_bits']==0
    assert r['wire_census']['total']==sum(v for k,v in r['wire_census'].items() if k!='total')
    assert (p/'child.proof').stat().st_size==r['child_bytes']
    assert (p/'public.bin').read_bytes()==(ROOT/'results/native-literal-field-screen/public.bin').read_bytes()
    cost=r['verifier_hash_cost']
    assert sum(cost['compression_blocks'])==cost['total_compression_blocks']
    rows.append(dict(profile=p.name,report_sha256=hashlib.sha256((p/'report.json').read_bytes()).hexdigest(),
        proof_bytes=r['child_bytes'],transmitted_bytes=r['total_child_plus_request_bytes'],
        calls=cost['calls'],blocks=cost['compression_blocks'],total_blocks=cost['total_compression_blocks']))
assert rows[-1]['blocks'][1]==rows[-1]['calls'][1] # Fixed104-byte node messages, one padded block.
result=dict(rows=rows,compression_blocks_saved=rows[0]['total_blocks']-rows[-1]['total_blocks'],
    fraction_saved=1-rows[-1]['total_blocks']/rows[0]['total_blocks'],
    scope='Counts from actual standalone engine.verify calls; not timings or recursive AIR costs. Versioned transcripts have different challenges.',
    unchanged_proof_size=len({r['proof_bytes'] for r in rows})==1,security_certified=False)
out=ROOT/'results/native-literal-sha384-ext12-compact/hash-cost-comparison.json'
out.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
