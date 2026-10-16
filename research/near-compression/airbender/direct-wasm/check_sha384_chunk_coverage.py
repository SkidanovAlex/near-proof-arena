#!/usr/bin/env python3
"""Structural ordered-use coverage; no cryptographic or compression proof."""
import argparse
import hashlib
import json
from collections import Counter
from pathlib import Path


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate(nodes, payloads, buckets, capacity, total):
    assert type(capacity) is int and capacity > 0
    assert len(nodes) == len(payloads)
    assert len(buckets) == (total + capacity - 1) // capacity
    seen = set()
    for owner, bucket in enumerate(buckets):
        previous = -1
        for ordinal, node, payload in bucket:
            assert type(ordinal) is int and 0 <= ordinal < len(nodes)
            assert ordinal > previous and ordinal not in seen
            assert type(node) is int and 0 <= node < total
            assert node // capacity == owner
            assert nodes[ordinal] == node and payloads[ordinal] == payload
            seen.add(ordinal)
            previous = ordinal
    assert seen == set(range(len(nodes)))
    return True


def run(call_path, record_path, capacity):
    calls = json.loads(call_path.read_text())
    raw = record_path.read_bytes()
    assert len(raw) % 256 == 0
    records = [raw[i:i+256] for i in range(0, len(raw), 256)]
    nodes, payloads, labels = [], [], []
    occurrence_counts = Counter()
    for call, item in enumerate(calls):
        frequency = item['frequency']
        assert type(frequency) is int and frequency > 0
        for step, node in enumerate(item['nodes']):
            assert type(node) is int and 0 <= node < len(records)
            nodes.append(node)
            payloads.append(records[node])  # all eight A/C words and entire M
            labels.append([call, step])
            occurrence_counts[node] += frequency
    buckets = [[] for _ in range((len(records)+capacity-1)//capacity)]
    for ordinal, (node, payload) in enumerate(zip(nodes, payloads)):
        buckets[node//capacity].append((ordinal, node, payload))
    validate(nodes, payloads, buckets, capacity, len(records))
    recovered = [None]*len(nodes)
    for bucket in buckets:
        for ordinal, node, payload in bucket:
            recovered[ordinal] = (labels[ordinal], node, payload)
    assert recovered == list(zip(labels, nodes, payloads))
    negatives = []
    def reject(name, change):
        altered = [list(bucket) for bucket in buckets]
        change(altered)
        try:
            validate(nodes, payloads, altered, capacity, len(records))
        except (AssertionError, IndexError):
            negatives.append(name)
        else:
            raise AssertionError('accepted mutation '+name)
    owner = next(i for i,b in enumerate(buckets) if len(b)>1)
    item = buckets[owner][0]
    reject('omitted use', lambda b: b[owner].pop(0))
    reject('duplicate use ordinal', lambda b: b[owner].append(item))
    reject('reordered uses', lambda b: b[owner].reverse())
    reject('wrong chunk', lambda b: b[(owner+1)%len(b)].append(b[owner].pop(0)))
    reject('wrong global node', lambda b: b[owner].__setitem__(0,(item[0],(item[1]+1)%len(records),item[2])))
    for offset, name in [(0,'input state'),(64,'message'),(192,'output state'),(248,'hidden output word')]:
        changed=bytearray(item[2]);changed[offset]^=1
        reject('changed '+name,lambda b,p=bytes(changed):b[owner].__setitem__(0,(item[0],item[1],p)))
    reject('relabelled ordinal',lambda b:b[owner].__setitem__(0,(len(nodes),item[1],item[2])))
    unique_counts = Counter(nodes)
    assert set(unique_counts) == set(range(len(records)))
    for node in unique_counts:
        assert unique_counts[node] <= occurrence_counts[node]
    chunk_rows=[{'chunk':i,'base':capacity*i,'nodes':min(capacity,len(records)-capacity*i),
                 'declared_uses':len(bucket),'original_occurrence_uses':sum(occurrence_counts[n] for n in range(capacity*i,min(capacity*(i+1),len(records))))}
                for i,bucket in enumerate(buckets)]
    return {'schema':'sha384-chunk-ordinal-coverage-v1','status':'PASS',
            'call_map_sha256':digest(call_path),'records_sha256':digest(record_path),
            'unique_calls':len(calls),'original_call_occurrences':sum(c['frequency'] for c in calls),
            'nodes':len(records),'capacity':capacity,'chunks':chunk_rows,
            'declared_unique_call_step_uses':len(nodes),
            'original_occurrence_steps':sum(occurrence_counts.values()),
            'max_declared_node_fanout':max(unique_counts.values()),
            'max_original_node_fanout':max(occurrence_counts.values()),
            'negative_cases':negatives,'payload_bytes_checked_per_use':256,
            'boundary':'Only structural partition/reconstruction checked. No per-chunk proof or commitment binding established. Original chronological occurrence order is unavailable in this input; frequencies are counted separately and never substituted for declared unique-call-step uses.'}


if __name__ == '__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--call-map',type=Path,required=True)
    parser.add_argument('--records',type=Path,required=True)
    parser.add_argument('--capacity',type=int,default=25)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    assert 0 < args.capacity <= 25
    report=run(args.call_map,args.records,args.capacity)
    report['source_sha256']=digest(Path(__file__))
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k not in ('chunks','boundary')}))
