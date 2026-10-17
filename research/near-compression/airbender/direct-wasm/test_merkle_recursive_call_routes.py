"""Differential private-path routing with actual SHA384 compression states."""
import argparse
import copy
import json
from pathlib import Path
from merkle_recursive_call_routes import PROFILE,compile_routes,witness_rows,residuals,flatten_equations,check_routing
from measure_sha384_block_dag import Probe
from pq384_primitives import P,merkle_tree,merkle_path,verify_path
from packed_claim_handoff import packing_context


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--probe-library',required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
    probe=Probe(a.probe_library);cases=equations=flattened=negatives=missing_air=0;shapes={};example=None
    for context in (b'x',packing_context(8,179,16),b'c'*255):
        for leaf_size in (0,2,8,64):
            for depth in range(1,5):
                count=1<<depth;leaves=[bytes((i*31+j*7)%256 for j in range(leaf_size)) for i in range(count)]
                root,layers=merkle_tree(leaves,context)
                for index in range(count):
                    path=merkle_path(layers,index)
                    assert verify_path(root,context,count,index,leaves[index],path)
                    statement=dict(profile=PROFILE,context_hex=context.hex(),root_hex=root.hex(),leaf_hex=leaves[index].hex(),leaf_count=count,index=index)
                    program,rows=witness_rows(statement,path,probe)
                    assert check_routing(statement,rows)
                    assert len(program['private_pairs'])==24*depth
                    private=[rows[r][c] for c in range(179) for r in range(len(rows))]
                    actual=[(sum(private[i]*w for i,w in eq['terms'])-eq['constant'])%P for eq in flatten_equations(program)]
                    assert actual==residuals(program,rows)
                    flattened+=len(actual);equations+=len(program['equations']);cases+=1
                    shapes[(len(context),leaf_size,depth)]=dict(context_bytes=len(context),leaf_bytes=leaf_size,depth=depth,
                        calls=len(program['calls']),compression_blocks=program['use_count'],use_rows=program['row_count'],
                        linear_equations=len(program['equations']),private_sibling_limbs=len(program['private_pairs']))
                    # Public inputs determine the relation; swapping root/index cannot retain acceptance.
                    for key,value in [('root_hex',('00' if root[0] else '01')+root.hex()[2:]),('index',index^1)]:
                        bad=dict(statement);bad[key]=value
                        assert not check_routing(bad,rows);negatives+=1
                    if index==0:
                        bad=copy.deepcopy(rows);bad[0][3]^=1
                        assert not check_routing(statement,bad);negatives+=1
                        badpath=list(path);badpath[0]=bytes([path[0][0]^1])+path[0][1:]
                        _,badrows=witness_rows(statement,badpath,probe)
                        assert not check_routing(statement,badrows);negatives+=1
                        # Routing alone intentionally cannot authenticate compression results.
                        # A changed free sibling limb with stale states passes routing: the
                        # compression/use AIR must reject it in the future composed proof.
                        hole=program['private_pairs'][0];bad=copy.deepcopy(rows)
                        bad[hole['row']][hole['column']]^=1
                        assert check_routing(statement,bad);missing_air+=1
                    if len(context)==197 and leaf_size==8 and depth==1 and index==0:
                        example=dict(statement=statement,program=program,rows=rows)
    invalid=[dict(example['statement'],index=True),dict(example['statement'],leaf_count=3),
             dict(example['statement'],context_hex='00'*2),dict(example['statement'],leaf_hex='00'),
             dict(example['statement'],root_hex='AA'*48),dict(example['statement'],calls=[])]
    for statement in invalid:
        try:compile_routes(statement)
        except ValueError:negatives+=1
        else:raise AssertionError('invalid public statement accepted')
    report=dict(status='ROUTING_PARITY_PASS_NOT_RECURSIVE_PROOF',actual_path_cases=cases,
        routing_equations_checked=equations,flat_vector_equations_checked=flattened,
        mutation_and_shape_rejections=negatives,compression_air_necessity_counterexamples=missing_air,
        growth_shapes=list(shapes.values()),complete_recursive_proof=False,
        public_inputs=['root','context','leaf_count','index','claimed_leaf'],private_inputs=['sibling_message_limbs','SHA384 compression/use witness'],
        scope='Actual source context plus boundary contexts; all positions at depths1..4. Public-only route compiler binds IV, full chaining state, framing, padding, digest-to-message limbs and root. Tests use native SHA384 states checked against hashlib. Routing is not compression correctness or a PCS proof. Next: same-root GKR/PCS and actual compression AIR acceptance; no outer bytes, PQ128, or full NEAR claim.')
    a.output.mkdir(parents=True,exist_ok=True)
    (a.output/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    (a.output/'example.json').write_text(json.dumps(example,separators=(',',':'))+'\n')
    def words(limbs):
        return [sum(limbs[4*i+j]<<(16*j) for j in range(4)) for i in range(len(limbs)//4)]
    nodes=[]
    for row in example['rows'][:example['program']['use_count']]:
        block=b''.join(w.to_bytes(8,'big') for w in words(row[35:99]))
        nodes.append(words(row[3:35])+list(block)+words(row[99:131]))
    config=dict(base=0,count=len(nodes),fanout_bits=1,nodes=nodes,uses=list(range(len(nodes))))
    (a.output/'chunk-config.json').write_text(json.dumps(config,separators=(',',':'))+'\n')
    print(json.dumps({k:v for k,v in report.items() if k!='growth_shapes'},indent=2))


if __name__=='__main__':main()
