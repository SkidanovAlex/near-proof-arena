"""Check selected actual transcript frames/scans against the Lean model.

Fixtures test the bridge on concrete inputs, not a Python/Rust refinement theorem.
The generic operational and framing theorems live in FusedGKRTranscript.lean.
"""
import gzip,json,struct,subprocess
from pathlib import Path
from check_binius_hash_graph import ROOT
from pq384_primitives import PREFIX
OUT=ROOT/'results/swirl-security-review/fused-transcript-lean'

def main():
    OUT.mkdir(exist_ok=True)
    graph=json.loads((OUT.parent/'fused-gkr-candidate/graph.json').read_text())
    def resolve(ref):
        kind,value=ref
        return bytes.fromhex(value if kind=='literal' else graph['inputs'][value] if kind=='input' else graph['nodes'][value]['digest'])
    def arr(bs):return '['+','.join(map(str,bs))+']'
    lines=['import NearCompression.FusedGKRTranscript','open NearCompression',
           'set_option maxRecDepth 8192','set_option maxHeartbeats 2000000']
    for i in [0,1,436]:
        draw=graph['draws'][i];assert draw['blocks']==1
        scan=draw['scans'][0];node=graph['nodes'][scan['hash_node']]
        parts=list(map(resolve,node['parts']));tag=node['tag'].encode()
        seed,payload=parts[1],parts[3];round_=int.from_bytes(parts[5],'little');counter=int.from_bytes(parts[8],'little')
        assert round_==i and counter==0
        wire=PREFIX+struct.pack('<I',len(tag))+tag+struct.pack('<I',len(parts))+b''.join(struct.pack('<Q',len(x))+x for x in parts)
        digest=bytes.fromhex(node['digest'])
        lines.append(f'theorem actualFrame_{i} : fusedGKRFrame {arr(seed)} {arr(payload)} {round_} {counter} = {arr(wire)} := by decide')
        lines.append(f'theorem actualWords_{i} : sha384DigestWords {arr(digest)} = {arr(scan["words"])} := by decide')
        lines.append(f'theorem actualScan_{i} : fusedGKRScanLoop (fun _ => {arr(digest)}) 1 0 4 = some ⟨{arr(draw["values"])},{scan["rejected"]},1,{arr(digest)}⟩ := by simp [fusedGKRScanLoop, actualWords_{i}, sha384ScanWords, sha384AcceptWord, sha384SampleLimit, sha384SamplePrime]')
    names=['fused_gkr_frame_injective','fused_gkr_scan_spec','fused_gkr_draw_spec',
        'fused_gkr_failure_preserves_state','fused_gkr_success_advances_once',
        'fused_gkr_double_commit_rejected','fused_gkr_no_commit_no_draw']
    for name in names:lines.append('#print axioms '+name)
    for i in [0,1,436]:
        lines.extend(['#print axioms actualFrame_'+str(i),'#print axioms actualScan_'+str(i)])
    path=OUT/'ActualFrames.lean';path.write_text('\n'.join(lines)+'\n')
    p=subprocess.run(['lake','env','lean',str(path)],cwd=ROOT,capture_output=True,text=True)
    log=p.stdout+p.stderr;(OUT/'lean.log.gz').write_bytes(gzip.compress(log.encode(),mtime=0))
    assert p.returncode==0,log[-3000:]
    assert 'sorryAx' not in log and 'native_decide' not in log
    report=dict(status='GENERIC_THEOREMS_AND_SELECTED_FRAME_SCAN_PARITY_CHECKED',generic_theorems=names,
        concrete_frame_indices=[0,1,436],concrete_scan_indices=[0,1,436],axiom_output=log,
        limitations=['No SHA384 correctness or random-oracle/QROM theorem added.',
                    'No universal Python/Rust refinement; selected concrete frame/scan agreement only.',
                    'Model treats hash as a function; actual hash circuit and sampler circuit composition remains open.',
                    'No full NEAR1Pgas, PQ128 certificate or complete recursive verifier.'])
    (OUT/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(log)

if __name__=='__main__':main()
