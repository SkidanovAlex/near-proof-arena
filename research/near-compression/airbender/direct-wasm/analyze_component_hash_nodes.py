"""Exact full512-bit chaining-state+block DAG for a captured verifier pair.
No block-only merging, cache soundness or recursive proof claim.
"""
import argparse
from collections import Counter,defaultdict
import hashlib,json,struct,sys
from pathlib import Path

def main():
    p=argparse.ArgumentParser();p.add_argument('--reference-dir',required=True);p.add_argument('--capture-dir',type=Path,required=True);p.add_argument('--probe-library',required=True);p.add_argument('--output-dir',type=Path,required=True);a=p.parse_args();sys.path.insert(0,a.reference_dir)
    from measure_sha384_block_dag import Probe
    from inventory_pq384_hash_families import framed
    from pq384_primitives import PREFIX
    calls=json.loads((a.capture_dir/'hash-calls.json').read_text());events=json.loads((a.capture_dir/'hash-occurrences.json').read_text());frequency=Counter(i for _,i in events);probe=Probe(a.probe_library)
    nodes={};records=[];mapped=[];bytag=defaultdict(lambda:{'calls':0,'total_blocks':0,'blocks_unique_inputs':0,'nodes':set()});block_only={};bad_block_reuse=0
    for ci,c in enumerate(calls):
        tag=bytes.fromhex(c['tag_hex']);parts=tuple(bytes.fromhex(x) for x in c['parts_hex']);message=framed(PREFIX,tag,parts)
        assert hashlib.sha384(message).hexdigest()==c['digest_hex']
        padded,states=probe.run(message);ids=[]
        for j in range(len(states)-1):
            block=padded[128*j:128*(j+1)];before=struct.pack('>8Q',*states[j]);after=struct.pack('>8Q',*states[j+1]);key=before+block
            if block in block_only and block_only[block]!=before:bad_block_reuse+=1
            else:block_only[block]=before
            if key not in nodes:nodes[key]=len(records);records.append(key+after)
            index=nodes[key];assert records[index][192:]==after;ids.append(index)
        mapped.append(ids);v=bytag[tag.decode()];v['calls']+=frequency[ci];v['total_blocks']+=len(ids)*frequency[ci];v['blocks_unique_inputs']+=len(ids);v['nodes'].update(ids)
    component_nodes=defaultdict(set)
    for component,ci in events:component_nodes[component].update(mapped[ci])
    assert len(component_nodes)>=2
    shared=set.intersection(*component_nodes.values())
    report={'status':'PASS','full_hash_inputs':len(calls),'total_compression_invocations':sum(len(mapped[i]) for _,i in events),'blocks_of_unique_complete_hash_inputs':sum(map(len,mapped)),'unique_full_state_block_nodes':len(nodes),'nodes_shared_across_all_components':len(shared),'component_node_counts':{str(k):len(v) for k,v in component_nodes.items()},'block_bytes_reencountered_with_different_state':bad_block_reuse,'by_tag':{k:{**{n:x for n,x in v.items() if n!='nodes'},'distinct_full_state_block_nodes':len(v['nodes'])} for k,v in bytag.items()},'limits':['Native probe checked final digest for each complete input; full intermediate state is8uint64, never truncated48bytes.','Exact measured equality sharing; no constrained routing or cache soundness theorem.','Static layout hashes remain accounted; removing them needs separately versioned verifier or explicit shared-use authentication.','No outer recursive proof or quantum security claim.']}
    a.output_dir.mkdir(parents=True,exist_ok=True);(a.output_dir/'compression-records.bin').write_bytes(b''.join(records));(a.output_dir/'call-node-ids.json').write_text(json.dumps(mapped,separators=(',',':')));(a.output_dir/'report.json').write_text(json.dumps(report,indent=2));print(json.dumps({k:v for k,v in report.items() if k!='by_tag'},indent=2))
if __name__=='__main__':main()
