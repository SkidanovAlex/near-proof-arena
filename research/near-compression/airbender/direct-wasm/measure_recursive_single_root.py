"""Measured hash cost, separately configured GKR and complete operand-free core."""
import argparse,json,sys,time
from pathlib import Path
from collections import defaultdict

def main():
 p=argparse.ArgumentParser();p.add_argument('--reference-dir',required=True);p.add_argument('--proof-directory',type=Path,required=True);a=p.parse_args();sys.path.insert(1,a.reference_dir)
 import recursive_single_root_conjunction as c
 import recursive_single_root_gkr_engine as g
 import pq384_primitives as h
 proof=json.loads((a.proof_directory/'proof.json').read_text());dep=json.loads((a.proof_directory/'derived-dependency.json').read_text());layout,binding,_,_=c.compile_layout(dep,proof['rs_root'])
 def capture(fn):
  tags=defaultdict(lambda:{'calls':0,'framed_bytes':0,'compression_blocks':0})
  def trace(frame,event,arg):
   if event=='call' and frame.f_code is h.hash_parts.__code__:
    tag=frame.f_locals['tag'];parts=frame.f_locals['parts'];n=len(h.PREFIX)+8+len(tag)+sum(8+len(x) for x in parts);r=tags[tag.decode()];r['calls']+=1;r['framed_bytes']+=n;r['compression_blocks']+=(n+17+127)//128
  start=time.monotonic();sys.setprofile(trace)
  try:fn()
  finally:sys.setprofile(None)
  return {'tags':dict(tags),'calls':sum(x['calls'] for x in tags.values()),'compression_blocks':sum(x['compression_blocks'] for x in tags.values()),'instrumented_seconds':time.monotonic()-start}
 report={'status':'PASS','configured_gkr_only':capture(lambda:g.verify(layout,binding,proof['gkr'])),'complete_core':capture(lambda:c.verify_derived(proof,dep)),'scope':'Core includes native-derived fixed-operand/DAG statement hashing, output challenges, GKR and PCS. No full trace or trace root. Original inner native derivation counted separately in public_verifier. No recursion/security certification.'}
 info=json.loads((a.proof_directory/'report.json').read_text());inners=[json.loads(Path(x).read_text()) for x in info['inner_paths']];statements=[json.loads(Path(x).read_text()) for x in info['statement_paths']]
 report['public_verifier']=capture(lambda:c.verify(proof,inners,statements))
 report['required_runtime_expanded_total_bytes']=info['proof_json_bytes']+info['original_expanded_inner_proof_file_bytes']+info['trusted_statement_file_bytes']
 report['required_extra_metadata_bytes']=0
 (a.proof_directory/'hash-cost.json').write_text(json.dumps(report,indent=2));print(json.dumps(report,indent=2))
if __name__=='__main__':main()
