#!/usr/bin/env python3
"""Replay an existing verifier and capture exact hash invocation order."""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import sys
import time


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    p=argparse.ArgumentParser()
    p.add_argument('--reference-dir',type=Path,required=True)
    p.add_argument('--input-directory',type=Path,required=True)
    p.add_argument('--dag-directory',type=Path,required=True)
    p.add_argument('--output-directory',type=Path,required=True)
    a=p.parse_args()
    sys.path.insert(0,str(a.reference_dir))
    import pq384_primitives as primitive
    import pq384_seed_gkr_bus as bus
    proofpath=a.input_directory/'proof.json'
    statementpath=a.input_directory/'statement.json'
    mappath=a.dag_directory/'hash-call-map.json'
    recordpath=a.dag_directory/'compression-records.bin'
    original=json.loads((a.dag_directory/'report.json').read_text())
    assert sha(proofpath)==original['source_proof_sha256']
    assert sha(statementpath)==original['source_statement_sha256']
    assert sha(recordpath)==original['records_sha256']
    calls=json.loads(mappath.read_text())
    keys={(c['tag'].encode('ascii'),tuple(bytes.fromhex(x) for x in c['parts_hex'])):i for i,c in enumerate(calls)}
    assert len(keys)==len(calls)
    proof=json.loads(proofpath.read_text());statement=json.loads(statementpath.read_text())
    config=bus.configure(statement['spec']['air']) # original capture excludes setup
    events=[];pending={};first=[];seen=set();code=primitive.hash_parts.__code__
    def observe(frame,event,arg):
        if frame.f_code is not code:return
        if event=='call':
            key=(frame.f_locals['tag'],frame.f_locals['parts'])
            assert key in keys,'hash input absent from captured inventory'
            index=keys[key]
            events.append(index)
            if index not in seen:first.append(index);seen.add(index)
            assert id(frame) not in pending
            pending[id(frame)]=index
        elif event=='return':
            index=pending.pop(id(frame))
            assert arg==bytes.fromhex(calls[index]['digest_hex'])
    start=time.monotonic()
    sys.setprofile(observe)
    try:
        assert bus.verify(proof,statement['spec'],[bytes.fromhex(x) for x in statement['roots']],config)
    finally:sys.setprofile(None)
    elapsed=time.monotonic()-start
    assert not pending
    assert first==list(range(len(calls)))
    histogram=Counter(events)
    assert all(histogram[i]==c['frequency'] for i,c in enumerate(calls))
    assert len(events)==13698
    # Explicit distinct spaces: occurrence ordinal, unique-call ID, block step, node ID.
    uses=[[occurrence,call,step,node] for occurrence,call in enumerate(events) for step,node in enumerate(calls[call]['nodes'])]
    assert len(uses)==41542
    assert sum(len(c['nodes']) for c in calls)==32587
    out=a.output_directory;out.mkdir(parents=True,exist_ok=True)
    eventpath=out/'occurrence-call-ids.json';usepath=out/'ordered-occurrence-uses.json'
    eventpath.write_text(json.dumps(events,separators=(',',':'))+'\n')
    usepath.write_text(json.dumps(uses,separators=(',',':'))+'\n')
    # Imported implementation manifest captures the actual Python verifier used.
    dependencies=[]
    reference=a.reference_dir.resolve()
    for module in tuple(sys.modules.values()):
        file=getattr(module,'__file__',None)
        if not file:continue
        path=Path(file).resolve()
        if path.suffix=='.py' and path.is_relative_to(reference):
            dependencies.append({'path':str(path),'sha256':sha(path)})
    dependencies.sort(key=lambda x:x['path'])
    report={'schema':'sha384-occurrence-order-v1','status':'PASS','verifier_accepts':True,
      'calls':len(events),'unique_calls':len(calls),'occurrence_steps':len(uses),
      'unique_call_steps':sum(len(c['nodes']) for c in calls),'first_seen_unique_order_preserved':True,
      'histograms_exact':True,'configured_replay_seconds':elapsed,
      'ordered_use_columns':['occurrence_ordinal','unique_call_id','block_step','global_node_id'],
      'files':[{'path':str(path),'sha256':sha(path),'bytes':path.stat().st_size} for path in
          [proofpath,statementpath,mappath,recordpath,eventpath,usepath,Path(__file__)]],
      'loaded_verifier_sources':dependencies,
      'scope':['Configured original JSON verifier only; setup excluded exactly as original DAG capture.',
        'No new proof generated. Original chronological invocation order observed, not inferred from frequencies.',
        'Unique-call-step and original-occurrence-step spaces remain separate.',
        'This is executable provenance evidence, not a Lean refinement of capture or a recursive/security theorem.']}
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:report[k] for k in ['status','calls','unique_calls','occurrence_steps','unique_call_steps','configured_replay_seconds']}))

if __name__=='__main__':main()
