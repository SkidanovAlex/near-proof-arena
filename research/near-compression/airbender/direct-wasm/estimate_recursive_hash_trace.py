"""Exact dense trace accounting for the current SHA384 compression gadget.

No runtime, peak RAM, gate count, secure parameter, or recursive proof-size
claim is inferred from these products. Streaming may reduce resident memory.
"""
import hashlib
import json
from pathlib import Path

root=Path(__file__).resolve().parents[2]
inputs=['results/pq384-seed-hash-reuse.json','results/sha384-compression-baseline/fixture-report.json']
reuse,fixture=[json.loads((root/p).read_text()) for p in inputs]
assert reuse['status']=='PASS' and fixture['formal_air_evaluation']
rows,width=fixture['rows'],fixture['width']
assert (rows,width)==(128,6944)
def cost(blocks):
    r=blocks*rows;cells=r*width
    return dict(compression_blocks=blocks,trace_rows=r,base_field_cells=cells,
                raw_u32_trace_bytes=4*cells,raw_u32_trace_gib=4*cells/(1<<30))
report=dict(status='exact layout accounting',input_hashes={p:hashlib.sha256((root/p).read_bytes()).hexdigest() for p in inputs},
    current_gadget=dict(rows_per_block=rows,width=width),
    configured_verifier_all_calls=cost(reuse['totals']['blocks']),
    identical_hash_inputs_shared=cost(reuse['totals']['unique_blocks']),
    fullproof_sha256=reuse['proof_sha256'],
    limits=['Only existing Q8 Ext4 seed-profile hash work; excludes trusted setup',
            'Dense base-field source trace bytes only, not actual peak memory or prover runtime',
            'Excludes FFT extension, auxiliaries, commitments and every non-hash verifier operation',
            'Sharing requires explicit equality/routing constraints and is not implemented',
            'Current one-table-per-block multiblock layout is a semantic prototype; this does not establish scalable aggregation',
            'Secure query counts and extension parameters remain unimplemented and uncertified'])
(root/'results/recursive-hash-trace-accounting.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
