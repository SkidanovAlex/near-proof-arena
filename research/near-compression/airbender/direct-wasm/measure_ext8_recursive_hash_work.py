"""Instrument the actual retained compact verifier; recursion cost only.
Counts exact SHA384 input framing and possible identical-input sharing.
"""
import argparse
from collections import defaultdict
import hashlib
import json
from pathlib import Path
import struct
import sys
import time
import pq384_ext8_weighted_codec as codec
import pq384_primitives as h


def frame(tag,parts):
    return h.PREFIX+struct.pack('<I',len(tag))+tag+struct.pack('<I',len(parts))+b''.join(h.u64(len(p))+p for p in parts)


def measure(fn):
    tags=defaultdict(lambda:dict(calls=0,blocks=0,unique_calls=0,unique_blocks=0))
    seen=set()
    def profile(f,event,arg):
        if event!='call' or f.f_code is not h.hash_parts.__code__:return
        tag,parts=f.f_locals['tag'],f.f_locals['parts']
        raw=frame(tag,parts);blocks=(len(raw)+17+127)//128
        row=tags[tag.decode()];row['calls']+=1;row['blocks']+=blocks
        # Use exact bytes, not a digest, so counting assumes no collisions.
        if raw not in seen:
            seen.add(raw);row['unique_calls']+=1;row['unique_blocks']+=blocks
    start=time.monotonic();sys.setprofile(profile)
    try:result=fn()
    finally:sys.setprofile(None)
    assert result is True
    return dict(tags=dict(tags),totals={k:sum(v[k] for v in tags.values()) for k in ('calls','blocks','unique_calls','unique_blocks')},
                instrumented_seconds=time.monotonic()-start)


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--capture',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
    cfg=json.loads((a.capture/'opening.json').read_text());data=(a.capture/'proof.bin').read_bytes()
    # Check exact framing against the implementation at padding boundaries.
    for n in (0,1,63,64,111,112,127,128,255):
        tag=b'measurement/check';parts=(bytes(n),b'x')
        assert hashlib.sha384(frame(tag,parts)).digest()==h.hash_parts(tag,*parts)
    call=lambda:codec.verify(data,bytes.fromhex(cfg['statement']),bytes.fromhex(cfg['parent']),cfg['branches'],cfg['claim'],queries=cfg['queries'])
    assert call() is True
    measured=measure(call)
    root=Path(__file__).resolve().parents[2]
    fixture=root/'results/sha384-compression-baseline/fixture-report.json'
    gadget=json.loads(fixture.read_text());assert gadget['formal_air_evaluation']
    rows,width=gadget['rows'],gadget['width'];assert (rows,width)==(128,6944)
    trace={}
    for key in ('blocks','unique_blocks'):
        blocks=measured['totals'][key];cells=blocks*rows*width
        trace[key]=dict(compression_blocks=blocks,rows=blocks*rows,base_field_cells=cells,
                        dense_u32_bytes=4*cells,dense_u32_gib=4*cells/2**30)
    report=dict(status='MEASURED_DIAGNOSTIC_VERIFIER_HASH_WORK',queries=cfg['queries'],opening_bytes=len(data),
        input_sha256={name:hashlib.sha256((a.capture/name).read_bytes()).hexdigest() for name in ('proof.bin','opening.json')},
        gadget_sha256=hashlib.sha256(fixture.read_bytes()).hexdigest(),measurement=measured,current_gadget_trace=trace,
        scope='Actual canonical decoder plus full weighted PCS verifier, including expanded duplicate-path rechecks. '
              'External statement/parent/roots/weights/claim are supplied: local/GKR/frontend verification EXCLUDED. '
              'Unique work shares only identical framed hash inputs, not compression prefixes. Sharing requires authenticated routing/equality constraints. '
              'Dense trace bytes are arithmetic accounting, NOT measured RAM/runtime/proof size. Current gadget128x6944 may be improved. '
              'Retained Ext8/q309 profile is diagnostic, not quantum-certified. No recursive proof or secure outer parameters established.')
    a.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(dict(totals=measured['totals'],trace=trace),indent=2))

if __name__=='__main__':main()
