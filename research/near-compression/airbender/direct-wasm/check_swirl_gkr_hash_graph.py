"""Join routed hash challenges to the saved optimized arithmetic circuit."""
import copy,gzip,hashlib,json,types
from pathlib import Path
import pq384_terminal_gkr as g
from prove_swirl_binary_root import context,OUT as GKR
from swirl_binary_transcript import unpack_v2
from swirl_bundle_codec import decode_gkr
from swirl_gkr_hash_graph import derive
from compile_swirl_gkr_verifier import Circuit
from prove_swirl_weighted_dag import split_obligation
OUT=GKR.parent/'gkr-hash-graph'


def export_scans(graph):
    lean=['import NearCompression.SHA384TranscriptDraw','open NearCompression']
    for i,record in enumerate(graph['draws']):
        for j,scan in enumerate(record['scans']):
            words=str(scan['words']);accepted=str(scan['accepted']);needed=scan['needed'];bad=scan['rejected']
            digest=list(bytes.fromhex(graph['nodes'][scan['hash_node']]['digest']))
            done='true' if len(scan['accepted'])==needed else 'false'
            lean += [f'theorem actualDigest_{i}_{j} : sha384DigestWords {digest} = {words} := by decide',
                     f'theorem actualScan_{i}_{j} : (sha384ScanWords {needed} {words}).values = {accepted} ∧',
                     f'    (sha384ScanWords {needed} {words}).rejected = {bad} ∧',
                     f'    (sha384ScanWords {needed} {words}).done = {done} := by',
                     '  simp [sha384ScanWords, sha384AcceptWord, sha384SampleLimit, sha384SamplePrime]']
    lean += ['#print axioms actualDigest_0_0','#print axioms actualScan_0_0']
    (OUT/'ActualScans.lean').write_text('\n'.join(lean)+'\n')


def main():
    layout,slots,known,claim,statement,_=context()
    proof=decode_gkr(layout,unpack_v2((GKR.parent/'binary-root-bundle/proof.bin').read_bytes())[1])
    graph=derive(layout,statement,proof,claim)
    expected=[]
    def draw(t):
        r=g.draw(t);expected.append(r);return r
    verifier=types.FunctionType(g.verify.__code__,dict(g.verify.__globals__,draw=draw),argdefs=g.verify.__defaults__)
    obligation=verifier(layout,statement,proof,claim)
    assert list(graph['challenges'].values())==expected
    assert derive(layout,statement,proof,claim,graph['nodes'])==graph
    a=json.loads(gzip.decompress((GKR.parent/'bdd-gkr-verifier/circuit.json.gz').read_bytes()))
    c=Circuit();c.nodes=[tuple(x) for x in a['nodes']];c.inputs=a['inputs']
    inputs={'claim':claim,**{f'known/{i}':v for i,v in known.items()},**graph['challenges']}
    for k,part in enumerate(proof['layers']):
        for j,row in enumerate(part['rounds']):
            for i,v in enumerate(row):inputs[f'proof/{k}/round/{j}/{i}']=v
        for i,v in enumerate(part['inputs']):inputs[f'proof/{k}/input/{i}']=v
    values=c.evaluate(inputs);residual=split_obligation(obligation,slots,known)
    assert all(values[i]==g.ZERO for i in a['checks'])
    assert values[a['residual']]==residual['claim']
    assert [(i,values[w]) for i,w in a['pcs']]==[(x['slot'],x['weight']) for x in residual['coordinates']]
    negatives=[]
    for label in ['wrong_digest','wrong_parent','wrong_tag','wrong_payload_route','truncated','extra']:
        nodes=copy.deepcopy(graph['nodes'])
        if label=='wrong_digest':nodes[3]['digest']='00'*48
        elif label=='wrong_parent':nodes[3]['parts'][0]=['hash',0]
        elif label=='wrong_tag':nodes[3]['tag']='transcript/squeeze'
        elif label=='wrong_payload_route':nodes[2]['parts'][2]=['input','claim']
        elif label=='truncated':nodes.pop()
        else:nodes.append(nodes[-1])
        try:derive(layout,statement,proof,claim,nodes)
        except ValueError:negatives.append(label)
        else:raise AssertionError(label)
    OUT.mkdir(exist_ok=True)
    export_scans(graph)
    (OUT/'graph.json.gz').write_bytes(gzip.compress(json.dumps(graph,separators=(',',':')).encode(),mtime=0))
    report=dict(status='HASH_GRAPH_TO_GKR_ARITHMETIC_PARITY',hash_nodes=len(graph['nodes']),
        compression_blocks=sum(n['blocks'] for n in graph['nodes']),challenge_inputs=len(expected),
        scans=sum(len(x['scans']) for x in graph['draws']),rejected_words=sum(x['rejected'] for x in graph['draws']),
        equality_checks=len(a['checks']),pcs_coordinates=len(a['pcs']),negative_checks=negatives,
        limitations=['SHA384 recomputed by host; no recursive hash proof.',
                     'Range/byte/scan constraints not lowered to AIR; generated Lean scan checks are concrete fixtures.',
                     'Statement/prefix and native weighted PCS remain external.',
                     'No Python refinement, cryptographic composition, PQ128 or full NEAR theorem.'])
    (OUT/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(report)


if __name__=='__main__':main()
