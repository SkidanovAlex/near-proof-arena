"""Actual source-column seam in a 2048-row pooled bank; no PCS integration."""
import argparse,gzip,hashlib,json,random,time
from pathlib import Path
import pq384_ext8_reference as f
import pq384_ext8_input_weights as w
import ext8_pooled_weights as pool


def load_seam(source_directory,opening):
    rng=random.Random(92841)
    expected=json.loads(gzip.decompress(Path('results/ext8-affine-q309/prover-report.json.gz').read_bytes()))['source_sha256']
    source=[]
    for i in (0,1):
        raw=(source_directory/f'source-{i:02d}-rows.json').read_bytes();assert hashlib.sha256(raw).hexdigest()==expected[i]
        source.append(json.loads(raw)['rows'])
    cfg=json.loads(opening.read_text());branches=[cfg['branches'][0],cfg['branches'][2]]
    assert [(b['log_rows'],b['width']) for b in branches]==[(11,5234),(5,1666)]
    # Physical lane 40 covers global columns5120..5247: 114 from table0,14 from table1.
    start=5120;packing=128;offsets=[0,5234];terms=[];rows=[[rng.randrange(f.P) for _ in range(packing)] for _ in range(2048)]
    for ti,(b,offset,data) in enumerate(zip(branches,offsets,source)):
        low=max(start,offset);high=min(start+packing,offset+b['width']);assert low<high
        current=[x for pair in b['lanes'] for x in pair[0]][:b['width']]
        nxt=[x for pair in b['lanes'] for x in pair[1]][:b['width']]
        terms.append(dict(offset=low-start,width=high-low,row_point=b['row_point'],current=current[low-offset:high-offset],next=nxt[low-offset:high-offset]))
        for r,row in enumerate(data):rows[r][low-start:high-start]=row[low-offset:high-offset]
    return rows,terms,expected[:2],hashlib.sha256(opening.read_bytes()).hexdigest()


def main():
    p=argparse.ArgumentParser();p.add_argument('--source-directory',type=Path,required=True);p.add_argument('--opening',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    started=time.perf_counter();rng=random.Random(92841)
    rows,terms,expected,opening_hash=load_seam(a.source_directory,a.opening)
    start=5120;packing=128
    start_check=time.perf_counter();direct=pool.direct_claim(rows,terms);coefficient=pool.coefficient_claim(rows,terms,packing);assert direct==coefficient
    coefficient_seconds=time.perf_counter()-start_check
    point=[tuple(rng.randrange(f.P) for _ in range(8)) for _ in range(18)]
    start_check=time.perf_counter();dense=pool.lane_weights(terms,11,128,0,128)
    assert w.mle(dense,point)==pool.lane_weight_mle(terms,11,128,0,128,point)
    beta_seconds=time.perf_counter()-start_check
    output=dict(status='PASS',physical_rows=2048,physical_columns=128,global_column_start=start,
                logical_blocks=[dict(rows=1<<len(t['row_point']),columns=t['width'],offset=t['offset']) for t in terms],
                unused_short_table_cells='Seeded nonzero/random values; no padding assumption',coefficient_identity=True,compact_beta_identity=True,
                coefficient_seconds=coefficient_seconds,beta_seconds=beta_seconds,total_seconds=time.perf_counter()-started,
                source_sha256=expected,opening_sha256=opening_hash,
                scope='Actual table0/table1 seam and retained GKR weight descriptor. Not a new pooled commitment, PCS proof, full input-opening check or security certificate.')
    a.output.write_text(json.dumps(output,indent=2)+'\n');print(json.dumps(output,indent=2))

if __name__=='__main__':main()
