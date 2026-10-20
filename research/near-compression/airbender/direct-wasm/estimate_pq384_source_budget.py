"""Exact current codec sizes across D1 source shapes, NOT a proof benchmark.

Excludes AIR rounds, auxiliary openings, roots/framing and other proof data.
Q8 is the implemented diagnostic. Q445 is an illustrative path-cost scenario,
not a proposed or proved secure parameter profile.
"""
import json,sys
from pathlib import Path
from pq384_batched_codec import expected_size
spec=json.loads(Path(sys.argv[1]).read_text());cases=[]
for ti,(table,log_rows) in enumerate(zip(spec['air']['tables'],spec['log_rows'])):
    width=table['width'];options=[]
    for power in range(21):
        packing=1<<power;degree=(1<<log_rows)*packing
        if not (128<=degree<=262144 and (width+packing-1)//packing<=64):continue
        size=expected_size(log_rows,width,packing);rounds=degree.bit_length()-7
        fixed=6+1024+96*rounds;assert (size-fixed)%8==0
        options.append(dict(packing=packing,degree=degree,lanes=(width+packing-1)//packing,
                            rounds=rounds,opening_bytes_q8=size,
                            illustrative_path_bytes_q445=fixed+445*((size-fixed)//8)))
    assert options,'unsupported source table'
    best=min(options,key=lambda o:o['opening_bytes_q8'])
    cases.append(dict(table_index=ti,rows=1<<log_rows,width=width,
                      column_claim_bytes=16*width,best_q8_shape=best))
report=dict(scope='Size arithmetic for separate current-format source openings; no combined proof produced',
            tables=len(cases),source_opening_bytes_q8=sum(c['best_q8_shape']['opening_bytes_q8'] for c in cases),
            source_column_claim_bytes=sum(c['column_claim_bytes'] for c in cases),
            illustrative_q445_at_q8_shapes=sum(c['best_q8_shape']['illustrative_path_bytes_q445'] for c in cases),
            excluded=['AIR sumcheck/shift rounds','auxiliary openings and claims','roots and framing','recursion','fullWasm/host tables'],
            security_claim=None,cases=cases)
print(json.dumps(report,indent=2))
