"""Capture exact SHA384 compression reuse in the compact Ext8 verifier.
Reuses the existing native state probe and independent DAG checker.
"""
import argparse
import hashlib
import json
from pathlib import Path
import struct
import sys
import pq384_ext8_weighted_codec as codec
import pq384_primitives as h
from measure_ext8_recursive_hash_work import frame
from measure_sha384_block_dag import Probe, batched
from check_sha384_block_dag import check


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--capture',type=Path,required=True);ap.add_argument('--probe-library',required=True);ap.add_argument('--artifacts',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
    cfg=json.loads((a.capture/'opening.json').read_text());data=(a.capture/'proof.bin').read_bytes()
    probe=Probe(a.probe_library);calls=[];callmap={};nodes={};records=[];pending={}
    def observe(f,event,arg):
        if f.f_code is not h.hash_parts.__code__:return
        if event=='call':
            tag,parts=f.f_locals['tag'],f.f_locals['parts'];key=(tag,parts)
            if key not in callmap:
                raw=frame(tag,parts);padded,states=probe.run(raw);ids=[]
                for i in range(len(states)-1):
                    block=padded[128*i:128*(i+1)]
                    before=struct.pack('>8Q',*states[i]);after=struct.pack('>8Q',*states[i+1]);nodekey=before+block
                    if nodekey not in nodes:nodes[nodekey]=len(records);records.append(nodekey+after)
                    idx=nodes[nodekey];assert records[idx][192:]==after;ids.append(idx)
                callmap[key]=len(calls);calls.append(dict(tag=tag.decode(),parts_hex=[p.hex() for p in parts],message_bytes=len(raw),digest_hex=hashlib.sha384(raw).hexdigest(),nodes=ids,frequency=0))
            idx=callmap[key];calls[idx]['frequency']+=1;pending[id(f)]=idx
        elif event=='return':assert arg==bytes.fromhex(calls[pending.pop(id(f))]['digest_hex'])
    sys.setprofile(observe)
    try:assert codec.verify(data,bytes.fromhex(cfg['statement']),bytes.fromhex(cfg['parent']),cfg['branches'],cfg['claim'],queries=cfg['queries'])
    finally:sys.setprofile(None)
    assert not pending
    raw=b''.join(records);a.artifacts.mkdir(parents=True,exist_ok=True)
    (a.artifacts/'compression-records.bin').write_bytes(raw)
    (a.artifacts/'hash-call-map.json').write_text(json.dumps(calls,separators=(',',':')))
    replay=check(raw,calls,probe)
    old=json.loads((Path(__file__).resolve().parents[2]/'results/ext8-recursive-hash-work.json').read_text())
    assert replay['total_observed_compressions']==old['measurement']['totals']['blocks']
    assert replay['unique_input_compressions']==old['measurement']['totals']['unique_blocks']
    # Existing batched core/endpoint geometry, not the older 128x6944 block table.
    layout=batched(len(records),25)
    report=dict(status='PASS_CAPTURE_AND_INDEPENDENT_REPLAY',queries=cfg['queries'],replay=replay,
        extra_blocks_removed=replay['unique_input_compressions']-len(records),
        batched_core_endpoint_projection=layout,dense_source_gib=4*layout['source_cells']/2**30,
        records_sha256=hashlib.sha256(raw).hexdigest(),calls_sha256=hashlib.sha256((a.artifacts/'hash-call-map.json').read_bytes()).hexdigest(),
        proof_sha256=hashlib.sha256(data).hexdigest(),
        scope='Exact full512bit chaining-state plus128byte block equality, never block-only dedup. '
              'Native probe outputs checked against hashlib digests for all calls; artifact checker replays states/routes. '
              'Uses existing5234column core and1668column endpoint geometry in25block batches. '
              'Source storage projection excludes routing/auxiliary tables,LDE,commitments and nonhash work; not peak memory or recursive proof size. '
              'External local/GKR/statement obligations excluded. Capture/route checks are Python, not new Lean certificates. '
              'No new hash profile, proof acceptance rule, or security claim.')
    a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))

if __name__=='__main__':main()
