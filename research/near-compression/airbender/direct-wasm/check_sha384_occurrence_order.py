#!/usr/bin/env python3
"""Independent structural check; chronology authenticity comes from captured replay."""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path


def check(calls,events,uses):
    assert all(type(c) is int and 0<=c<len(calls) for c in events)
    assert Counter(events)==Counter({i:c['frequency'] for i,c in enumerate(calls)})
    assert list(dict.fromkeys(events))==list(range(len(calls)))
    cursor=0
    for occurrence,index in enumerate(events):
        for step,node in enumerate(calls[index]['nodes']):
            assert uses[cursor]==[occurrence,index,step,node]
            cursor+=1
    assert cursor==len(uses)
    # Deterministic chunk subsequences retain original occurrence ordering.
    nodes=[r[3] for r in uses]
    chunks={node//25:[] for node in nodes}
    for ordinal,node in enumerate(nodes):chunks[node//25].append(ordinal)
    recovered=[None]*len(nodes)
    for owner,ordinals in chunks.items():
        assert ordinals==sorted(set(ordinals))
        for ordinal in ordinals:
            assert nodes[ordinal]//25==owner
            recovered[ordinal]=uses[ordinal]
    assert recovered==uses
    return len(chunks)


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--call-map',type=Path,required=True)
    p.add_argument('--capture-directory',type=Path,required=True);a=p.parse_args()
    calls=json.loads(a.call_map.read_text());d=a.capture_directory
    events=json.loads((d/'occurrence-call-ids.json').read_text())
    uses=json.loads((d/'ordered-occurrence-uses.json').read_text())
    chunks=check(calls,events,uses)
    rejected=[]
    def negative(name,ee,uu):
        try:check(calls,ee,uu)
        except (AssertionError,IndexError):rejected.append(name)
        else:raise AssertionError('accepted '+name)
    negative('omitted call',events[:-1],uses)
    negative('duplicated call',events+[events[0]],uses)
    negative('omitted step',events,uses[:-1])
    negative('duplicated step',events,uses+[uses[0]])
    negative('reordered steps',events,[uses[1],uses[0]]+uses[2:])
    for col,label in enumerate(['occurrence','unique call','step','node']):
        wrong=[list(uses[0])]+uses[1:];wrong[0][col]+=1
        negative('wrong '+label,events,wrong)
    report={'status':'PASS','calls':len(events),'steps':len(uses),'chunks':chunks,
       'negative_cases':rejected,'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
       'scope':'Structural consistency only. A coordinated reordering preserving histogram and first-seen order requires authenticated replay provenance to distinguish; this checker does not prove chronology.'}
    (d/'independent-check.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
