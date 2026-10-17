"""Coverage and framing budget for transporting independent 64-block proofs.
Does not extrapolate measured q8 bytes into a security bound or universal limit.
"""
import gzip
import hashlib
import json
from pathlib import Path
import pq384_ext8_auxiliary as aux
import scheduled_bus_whir as algebra

ROOT=Path(__file__).resolve().parents[2]


def main():
    files=['results/sha384-nibble64/codec-report.json','results/sha384-nibble64/statement.json.gz',
           'results/switch-full-verifier-hash-work.json','results/ext8-switch-execution-q309/report.json',
           'results/derived-transcript-bindings.json','results/ext8-switch-execution-q309/codec-report.json']
    def read(name):
        raw=(ROOT/name).read_bytes();return json.loads(gzip.decompress(raw) if name.endswith('.gz') else raw)
    proof,statement,work,bundle,derived,codec=map(read,files);spec=statement['spec'];tables=spec['air']['tables']
    assert proof['fresh_verifier_passed'] and proof['blocks']==64 and proof['queries']==8
    wire=(ROOT/'results/sha384-nibble64/compression.bin').read_bytes()
    assert len(wire)==proof['proof_bytes'] and hashlib.sha256(wire).hexdigest()==proof['proof_sha256']
    header=8+2*48*len(tables)
    finals=32*sum(aux.layout(t)['finals'] for t in tables)
    local=32*sum(n*(algebra.table_degree(t,spec['air']['numPub'])+2) for t,n in zip(tables,spec['log_rows']))
    fixed=header+finals+local
    assert fixed<proof['nonopening_bytes']
    blocks=work['measurement']['totals']['unique_blocks'];chunks=(blocks+63)//64
    comparisons=[]
    for component,removed in [('entire_opening',codec['opening_bytes']),('entire_compression_envelope',bundle['compression_envelope_bytes']),('entire_bundle',bundle['combined_bytes'])]:
        allowance=299999-(bundle['combined_bytes']-removed)
        comparisons.append(dict(component=component,allowance_bytes=allowance,
            measured_q8_hash_only_proof_bytes=proof['proof_bytes'],headroom_bytes=allowance-proof['proof_bytes'],
            covers_replaced_verifier=False))
    # This is a bound on a specific fixed codec transport, not on recursive proofs.
    scenarios=[]
    for name,n in [('unchanged_whole_input_deduplicated_verifier',blocks),
                   ('optimistically_erased_derived_transcript_work',derived['optimistic_hash_screen']['remaining_unique_blocks'])]:
        count=(n+63)//64
        scenarios.append(dict(name=name,sha384_compression_blocks=n,independent_64_slot_envelopes=count,
            mandatory_header_roots_finals_local_bytes=count*fixed,
            exceeds_300000_before_GKR_PCS_and_call_binding=count*fixed>=300000))
    report=dict(status='INDEPENDENT_NIBBLE_CHUNK_TRANSPORT_REJECTED',
        measured_proof_bytes=proof['proof_bytes'],queries=8,
        mandatory_bytes_per_fixed_spec_envelope=dict(header_and_roots=header,finals=finals,local_rounds=local,total=fixed),
        replacement_comparisons=comparisons,scenarios=scenarios,
        coverage=dict(implemented=['64 independent SHA384 compression state/message/result relations',
            'phase scheduling, word routing, fixed lookup relations and bounded additions within that relation'],
            missing=['bind private boundary root to exact verifier hash calls and their multiplicities',
            'SHA message framing, padding, IV, chaining and digest truncation for those calls',
            'derive Fiat-Shamir challenges from the authenticated transcript',
            'verify Merkle index/path/root equations and PCS fold/query equations',
            'local/GKR algebraic checks and source-to-auxiliary opening obligations',
            'outer proof soundness, adaptive QROM accounting and PQ128 parameters',
            'full near-chunk-v3 semantics and 1 Petagas capacity']),
        decision='Do not transport one existing envelope per hash batch or launch larger SHA-only proving as a substitute for full-verifier recursion. A next viable candidate must jointly prove the closed verifier, amortize fixed messages globally, and account for call routing plus arithmetic; validate its complete byte/security ledger before full-scale proving.',
        scope='Exact lower bound only for concatenating independent envelopes with this fixed 64-slot specification. Workload is the recorded verifier after whole-input hash deduplication, not a minimum over new algorithms, block/state sharing or transcript redesign. Optimistic scenario is an assumed workload, not an implemented protocol. This does not rule out joint proofs, recursive aggregation, different AIR/codec, or a redesigned verifier. q8 and hash-only coverage cannot establish PQ128 or full NEAR feasibility.',
        sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in [Path(__file__),Path(aux.__file__),Path(algebra.__file__),ROOT/'airbender/direct-wasm/ext8_execution_codec.py']+[ROOT/name for name in files]+[ROOT/'results/sha384-nibble64/compression.bin']})
    (ROOT/'results/nibble-full-verifier-screen.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:report[k] for k in ['status','mandatory_bytes_per_fixed_spec_envelope','replacement_comparisons','scenarios']},indent=2))


if __name__=='__main__':main()
