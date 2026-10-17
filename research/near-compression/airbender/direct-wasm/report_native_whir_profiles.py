"""Reconcile finite actual-Wasm parameter experiment; no security certification."""
from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parents[2]
rows=[]
for suffix in ['ext12-compact','rate7','alllist','alllist-rate7']:
    p=ROOT/('results/native-literal-sha384-'+suffix)
    raw=(p/'report.json').read_bytes();r=json.loads(raw)
    for name,h in r['sha256'].items():assert hashlib.sha256((p/name).read_bytes()).hexdigest()==h,(p,name)
    assert r['witness_independent_replay'] and r['public_mutations_rejected']==6
    sec=r['security'];assert sec['query_target_bits']==268 and sec['grinding_bits']==0 and not sec['certified']
    assert sec['native_component_min_bits']>=268
    assert (p/'public.bin').read_bytes()==(ROOT/'results/native-literal-field-screen/public.bin').read_bytes()
    rows.append(dict(profile=p.name,parameters=sec.get('parameters',dict(n_stack=16,k=3,log_blowup=5,all_list=0)),
        native_bytes=r['child_bytes'],whir_bytes=r['wire_census']['whir'],
        native_min_component_bits=sec['native_component_min_bits'],
        verification_sha384_blocks=r['verifier_hash_cost']['total_compression_blocks'],
        report_sha256=hashlib.sha256(raw).hexdigest()))
p=ROOT/'results/native-literal-alllist-rate7-dictionary';wire=json.loads((p/'report.json').read_text())
assert wire['native_bytes']==rows[-1]['native_bytes']
assert hashlib.sha256((p/'child.dictionary').read_bytes()).hexdigest()==wire['wire_sha256']
result=dict(rows=rows,best_tested_dictionary_bytes=wire['wire_bytes'],
    best_tested_transmitted_bytes=wire['total_wire_plus_request_bytes'],
    strict_sub300000_pass=wire['total_wire_plus_request_bytes']<300000,
    security_certified=False,
    decision='Retain all-list/blowup128 candidate; next investigate shared Merkle openings, not a broad parameter sweep.',
    limits=['finite profiles, not global optimum','native estimates not a concrete QROM certificate',
        'no controlled latency/memory benchmark','direct bounded Wasm child, not recursive or full NEAR'])
out=ROOT/'results/native-literal-sha384-alllist-rate7/profile-comparison.json'
out.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
