"""Static relation-count bounds and packing screen; does not change the live AIR."""
from collections import Counter
import gzip
import hashlib
import json
from pathlib import Path
import sha384_nibble_circuit as circuit
import plan_sha384_nibble_rows as planner
import sha384_nibble_lookup_air as lookup
import pq384_ext8_auxiliary as aux

ROOT=Path(__file__).resolve().parents[2]


def main():
    blocks=64;g=circuit.compile_graph()
    counts=Counter(op for op,_,_,_ in g.gates if op in lookup.OPS)
    assert sum(counts.values())==18688
    counts['range']=len(planner.plan(g)[2]);assert counts['range']==2800
    spec=json.loads(gzip.decompress((ROOT/'results/sha384-nibble64/statement.json.gz').read_bytes()))['spec']
    trials=[];saved_cells=saved_packed_cells=saved_lanes=0
    for index,op in enumerate((*lookup.OPS,'range'),3):
        old=spec['air']['tables'][index];old_bits=len(old['interactions'][0]['mult'])
        bound=counts[op]*blocks;bits=max(1,bound.bit_length());assert bound<1<<bits
        new=lookup.fixed_table(op,bits);n=1<<old['maxLog']
        assert old==lookup.fixed_table(op,old_bits)
        geometries={}
        for key,ow,nw in [('source',old['width'],new['width']),('auxiliary',8*aux.layout(old)['aux_columns'],8*aux.layout(new)['aux_columns'])]:
            before=planner.geometry(n,ow);after=planner.geometry(n,nw)
            assert before['within_current_degree_lane_caps'] and after['within_current_degree_lane_caps']
            geometries[key]=dict(before=before,after=after)
            saved_cells+=n*(ow-nw)
            saved_packed_cells+=before['degree']*before['lanes']-after['degree']*after['lanes']
            saved_lanes+=before['lanes']-after['lanes']
        trials.append(dict(operation=op,static_requests_per_block=counts[op],per_value_natural_multiplicity_upper_bound=bound,old_bits=old_bits,new_bits=bits,geometry=geometries))
    report=dict(status='STATIC_MULTIPLICITY_PACKING_SCREEN',blocks=blocks,trials=trials,
        source_aux_cells_saved=saved_cells,packed_base_coefficients_saved=saved_packed_cells,lanes_saved=saved_lanes,
        decision='Packing retains savings. Candidate for compiler specialization after completing baseline proof measurement; no optimized proof launched.',
        required_semantic_contract='For each canonical scheduled block, operation-tagged source requests equal the static graph counts. Under exact natural bus balance, any received tuple multiplicity is bounded by the total requests to its relation. No honest-witness maximum is used. Universal compiler/routing correctness and cryptographic extraction of natural balance are still unproved.',
        scope='Static graph-count and exact geometry screen only. No revised compiler, witness, succinct proof, Lean theorem, PQ128 or proof-byte saving demonstrated.',
        sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in [Path(__file__),Path(circuit.__file__),Path(planner.__file__),Path(lookup.__file__),Path(aux.__file__),ROOT/'results/sha384-nibble64/statement.json.gz']})
    (ROOT/'results/nibble-multiplicity-screen.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k not in ('trials','sha256')},indent=2))


if __name__=='__main__':main()
