"""Independent artifact replay against full frames and compression states.

Validates record/input consistency, not that captured frames implement a
recursive verifier. Frequency provenance remains the accepted-run measurement.
"""
import argparse,collections,copy,hashlib,json,struct
from pathlib import Path
from measure_sha384_block_dag import Probe
from inventory_pq384_hash_families import framed
PREFIX=b'NEAR-PQ384-PRIMITIVES-V1'

def check(raw,calls,probe):
    assert len(raw)>0 and len(raw)%256==0
    records=[raw[i:i+256] for i in range(0,len(raw),256)];assert len({r[:192] for r in records})==len(records)
    used=set();seen=set();edges=set();total=0;blocks=0
    for c in calls:
        assert type(c['frequency'])is int and c['frequency']>0
        tag=c['tag'].encode('ascii');parts=tuple(bytes.fromhex(v) for v in c['parts_hex']);assert (tag,parts) not in seen;seen.add((tag,parts))
        message=framed(PREFIX,tag,parts);assert len(message)==c['message_bytes'];assert hashlib.sha384(message).hexdigest()==c['digest_hex']
        padded,states=probe.run(message);assert len(c['nodes'])==len(states)-1
        for i,node in enumerate(c['nodes']):
            assert type(node)is int and 0<=node<len(records);used.add(node)
            expected=struct.pack('>8Q',*states[i])+padded[128*i:128*(i+1)]+struct.pack('>8Q',*states[i+1]);assert records[node]==expected
        edges.update(zip(c['nodes'],c['nodes'][1:]));total+=c['frequency']*len(c['nodes']);blocks+=len(c['nodes'])
    assert used==set(range(len(records)))
    outgoing=collections.defaultdict(list);indegree=[0]*len(records)
    for x,y in edges:outgoing[x].append(y);indegree[y]+=1
    queue=collections.deque(i for i,d in enumerate(indegree) if not d);visited=0
    while queue:
        i=queue.popleft();visited+=1
        for j in outgoing[i]:
            indegree[j]-=1
            if indegree[j]==0:queue.append(j)
    assert visited==len(records),'observed graph contains a cycle'
    return dict(unique_records=len(records),unique_hash_inputs=len(calls),unique_input_compressions=blocks,total_observed_compressions=total,unique_edges=len(edges),observed_graph_acyclic=True)

def main():
    p=argparse.ArgumentParser();p.add_argument('--directory',required=True);p.add_argument('--probe-library',required=True);a=p.parse_args();d=Path(a.directory);raw=(d/'compression-records.bin').read_bytes();calls=json.loads((d/'hash-call-map.json').read_text());probe=Probe(a.probe_library);result=check(raw,calls,probe);negative=[]
    def reject(name,r,c):
        try:check(r,c,probe)
        except (AssertionError,ValueError,IndexError,KeyError):negative.append(name)
        else:raise AssertionError(name)
    node=calls[0]['nodes'][0]
    for offset,name in [(0,'input-state'),(64,'block-byte'),(192,'output-state')]:
        changed=bytearray(raw);changed[256*node+offset]^=1;reject(name,bytes(changed),calls)
    for name,index in [('negative-node',-1),('out-of-range-node',len(raw)//256)]:
        changed=copy.deepcopy(calls);changed[0]['nodes'][0]=index;reject(name,raw,changed)
    changed=copy.deepcopy(calls);changed[0]['digest_hex']='00'*48;reject('digest',raw,changed)
    reject('duplicate-record',raw+raw[:256],calls);reject('partial-record',raw[:-1],calls)
    result.update(status='PASS',negative_tests=negative,records_sha256=hashlib.sha256(raw).hexdigest(),scope='All captured frames independently replayed to exact state/block/output records; capture frequency provenance still comes from source verifier execution, not this checker.')
    (d/'independent-check.json').write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2))
if __name__=='__main__':main()
