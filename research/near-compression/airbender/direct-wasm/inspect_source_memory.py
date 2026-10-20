"""Source-backed allocation accounting for rs_commit, not measured peak RSS.

Excludes serde JSON, row/vector headers, allocator overhead, auxiliaries and
simultaneous jobs. FFT and tree construction occur in different phases.
"""
import argparse
import json
from pathlib import Path


def account(log_rows, width, packing):
    if any(type(v) is not int for v in (log_rows,width,packing)):
        raise ValueError('integer shape')
    if not 1 <= log_rows <= 25 or width < 1 or packing < 1 or packing & (packing-1):
        raise ValueError('source shape')
    n=1<<log_rows;d=n*packing
    if d>1<<25:
        raise ValueError('rs_commit domain limit')
    lanes=(width+packing-1)//packing;half=2*d
    rows=4*n*width
    leaves=half*lanes*8
    fft=4*d*8
    tree=(2*half-1)*48
    coefficients=d*lanes*4
    return dict(rows=n,width=width,packing=packing,lanes=lanes,
        decoded_row_payload_bytes=rows,leaf_payload_bytes=leaves,
        one_fft_buffer_bytes=fft,all_merkle_digest_bytes=tree,
        construction_payload_peak_lower_bound=rows+leaves+max(fft,tree),
        cache_bytes_excluding_manifest=coefficients+leaves+tree,
        disk_backed_proposal=dict(retained_fft_buffer_bytes=fft,
            caveat='Requires new disk-backed leaf transpose, streamed tree builder and non-JSON row reader; not implemented.'))


def main():
    p=argparse.ArgumentParser();p.add_argument('statement',type=Path);p.add_argument('output',type=Path);a=p.parse_args()
    s=json.loads(a.statement.read_text())['spec']
    tables=s['air']['tables']
    if not len(tables)==len(s['log_rows'])==len(s['source_packings']):raise ValueError('table shapes')
    result=dict(status='source-derived accounting; not RSS measurement',
        source='airbender/direct-wasm/pq384-native/src/bin/rs_commit.rs',
        tables=[dict(table=i,**account(h,t['width'],packing)) for i,(h,t,packing) in enumerate(zip(s['log_rows'],tables,s['source_packings']))],
        excluded=['serde_json input Value and temporary clone','Vec headers and allocator overhead','auxiliary commitments','prover work after source commitment','parallel table jobs'],
        unchanged_protocol_requirement='Disk-backed implementation must preserve exact context, root, leaf order and every authenticated opening.')
    a.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
