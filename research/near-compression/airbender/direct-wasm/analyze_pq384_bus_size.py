"""Exact complete transport byte accounting, not a security estimate."""
import argparse,json
from pathlib import Path
import pq384_global_bus as bus
import pq384_global_bus_codec as codec
import pq384_global_codec as pcs

def main():
    ap=argparse.ArgumentParser();ap.add_argument('directory',type=Path);ap.add_argument('binary',type=Path);ap.add_argument('output',type=Path);a=ap.parse_args()
    proof=json.loads((a.directory/'proof.json').read_text());trusted=json.loads((a.directory/'statement.json').read_text());spec=trusted['spec'];roots=[bytes.fromhex(r) for r in trusted['roots']]
    st,t,alpha,gamma=bus.begin(spec,roots);ars=[bytes.fromhex(r) for r in proof['aux_roots']];bus.initialize_aux(t,spec,ars,proof['finals'])
    totals=dict(transport_magic=len(codec.MAGIC),source_roots=48*len(roots),aux_roots=48*len(ars),
                bus_finals=16*sum(map(len,proof['finals'])),air_sumcheck=0,shift_sumcheck=0,column_claim_vectors=0,
                opening_length_frames=0,pcs_headers_terminal=0,pcs_leaves=0,pcs_siblings=0)
    tables=[]
    for ti,part in enumerate(proof['tables']):
        argslist=bus.verify_table_reduction(part,spec,st,t,alpha,gamma,ti,proof['finals'][ti],[roots[ti],ars[ti]])
        airbytes=16*sum(map(len,part['constraint_rounds']));shiftbytes=16*sum(map(len,part['shift_reduction']['rounds']))
        claimsbytes=16*(len(part['column_claims'])+len(part['shift_reduction']['current_evals'])+len(part['shift_reduction']['next_evals']))
        totals['air_sumcheck']+=airbytes;totals['shift_sumcheck']+=shiftbytes;totals['column_claim_vectors']+=claimsbytes
        branches=[]
        for opening,args in zip(part['openings'],argslist):
            stages=pcs.header(args,spec['terminal_degree'],opening['rounds'],opening['terminal']);_,fixed,_=pcs.limits(args,spec['terminal_degree'])
            leaves=sum(len(set(indices))*4*words for _,_,_,indices,words in stages)
            siblings=sum(len(pcs.mp.boundary(n,indices))*48 for _,_,n,indices,_ in stages)
            wire=pcs.encode(opening,terminal_degree=spec['terminal_degree'],**args);assert len(wire)==fixed+leaves+siblings
            totals['opening_length_frames']+=8;totals['pcs_headers_terminal']+=fixed;totals['pcs_leaves']+=leaves;totals['pcs_siblings']+=siblings
            stage_sizes=[]
            for stage,(_,_,n,indices,words) in enumerate(stages):
                stage_sizes.append(dict(stage=stage,leaf_count=n,leaf_words=words,
                    distinct_queries=len(set(indices)),
                    leaf_bytes=len(set(indices))*4*words,
                    sibling_bytes=len(pcs.mp.boundary(n,indices))*48))
            branches.append(dict(width=args['width'],packing=args['packing'],bytes=len(wire),
                                 stages=stage_sizes))
        tables.append(dict(table=ti,air_bytes=airbytes,shift_bytes=shiftbytes,claim_bytes=claimsbytes,branches=branches))
    assert bus.global_fingerprint_balance(spec,proof['finals'],alpha,gamma)
    size=a.binary.stat().st_size;assert sum(totals.values())==size
    report=dict(status='PASS',whole_transport_bytes=size,components=totals,tables=tables,
        scope='Current33tableQ8diagnostic transport, including sourcecommitments; no securedprofile or1Pgasextrapolation')
    a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(totals,indent=2))
if __name__=='__main__':main()
