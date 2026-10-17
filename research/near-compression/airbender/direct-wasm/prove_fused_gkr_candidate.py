"""Fresh candidate GKR and routed hash graph; no native PCS continuation yet."""
import copy,gzip,json,subprocess,tempfile,time
from pathlib import Path
import pq384_terminal_gkr as old
from fused_gkr_transcript import candidate
from pq384_gkr4_native import Kernel
from prove_swirl_binary_root import context,SOURCE
from prove_swirl_native_dag import fixture
from prove_swirl_weighted_dag import split_obligation,check_residual_fixture
OUT=SOURCE.parent/'fused-gkr-candidate'

def main():
    OUT.mkdir(exist_ok=True)
    data=fixture(SOURCE/'point-capture.jsonl.gz',SOURCE/'openings.json.gz',OUT,SOURCE/'dag.jsonl.gz')
    _,layout,slots,private,known,claim,_=data
    layout2,slots2,known2,claim2,statement,_=context()
    assert (layout,slots,known,claim)==(layout2,slots2,known2,claim2)
    g=candidate()
    with tempfile.TemporaryDirectory() as tmp:
        lib=Path(tmp)/'kernel.so'
        subprocess.run(['rustc','--edition=2024','--crate-type','cdylib','-O',str(Path(__file__).with_name('native-folded')/'kernel_gkr4.rs'),'-o',str(lib)],check=True)
        start=time.perf_counter();proof,ob=g.prove(layout,statement,private,claim,kernel=Kernel(lib));seconds=time.perf_counter()-start
    assert g.verify(layout,statement,proof,claim)==ob
    graph=g.last_transcript.graph()
    pcs=split_obligation(ob,slots,known);check_residual_fixture(pcs,private)
    negatives=0
    for mode in ['statement','coefficient','old-profile','old-verifier']:
        bad=copy.deepcopy(proof);s=statement;verifier=g
        if mode=='statement':s=bytes([s[0]^1])+s[1:]
        if mode=='coefficient':bad['layers'][0]['rounds'][0][0]=g.add(bad['layers'][0]['rounds'][0][0],g.ONE)
        if mode=='old-profile':bad['profile']=old.PROFILE.decode()
        if mode=='old-verifier':verifier=old
        try:verifier.verify(layout,s,bad,claim)
        except ValueError:negatives+=1
        else:raise AssertionError(mode)
    oldproof=json.loads(gzip.decompress((OUT.parent/'binary-root-gkr/proof.json.gz').read_bytes()))
    oldproof['profile']=g.PROFILE.decode()
    try:g.verify(layout,statement,oldproof,claim)
    except ValueError:negatives+=1
    else:raise AssertionError('relabelled old transcript accepted')
    assert g.verify(layout,statement,proof,claim)==ob
    assert g.last_transcript.graph()==graph
    for name,value in [('proof',proof),('pcs-obligation',pcs),('graph',graph)]:
        (OUT/(name+'.json.gz')).write_bytes(gzip.compress(json.dumps(value).encode(),mtime=0))
    (OUT/'graph.json').write_text(json.dumps(graph,separators=(',',':'))+'\n')
    report=dict(status='NEW_TRANSCRIPT_GKR_AND_RESIDUAL_CHECKED',prover_seconds=seconds,
        draws=len(graph['draws']),hash_calls=len(graph['nodes']),compression_blocks=sum(n['blocks'] for n in graph['nodes']),
        negative_checks=negatives,profile=g.PROFILE.decode(),
        scope='New transcript protocol. Actual GKR verified; residual checked against full witness, no native PCS continuation.',
        limitations=['No QROM security/composition proof, no PQ128, no full NEAR, no Lean transcript refinement.',
                    'Hash graph is host-derived; circuit proof remains a separate obligation.'])
    (OUT/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))

if __name__=='__main__':main()
