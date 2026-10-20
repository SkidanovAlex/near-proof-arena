#!/usr/bin/env python3
"""Cross-check Python/Rust SHA384 primitives on real D1 statement/row data."""
import argparse
import json
from pathlib import Path
import struct
import subprocess
import tempfile

import pq384_primitives as p


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('native',type=Path)
    ap.add_argument('prepared',type=Path)
    ap.add_argument('report',type=Path)
    a=ap.parse_args()
    statement=(a.prepared/'spec.json').read_bytes()
    leaves=json.loads((a.prepared/'source-00-rows.json').read_text())['rows'][:8]
    context=p.hash_parts(b'statement/spec',statement)
    events=[{'kind':'commit','label':'source-roots','payload_hex':context.hex()},
            {'kind':'draw','label':'bus','count':2,'coefficients':10,'max_blocks':4096},
            {'kind':'draw','label':'round-challenges','count':32,'coefficients':16,'max_blocks':4096},
            {'kind':'draw','label':'forced-budget-failure','count':4096,'coefficients':64,'max_blocks':1},
            {'kind':'commit','label':'after-failure','payload_hex':'00010203'},
            {'kind':'draw','label':'query','count':7,'coefficients':1,'max_blocks':4096}]
    transcript=p.Transcript(statement);expected=[]
    for event in events:
        label=event['label'].encode()
        if event['kind']=='commit':
            transcript.commit(label,bytes.fromhex(event['payload_hex']))
            expected.append({'seed':p.digest_words(transcript.seed)})
        else:
            before=transcript.seed
            try:
                values,stats=transcript.draw(label,event['count'],event['coefficients'],event['max_blocks'])
                expected.append({'values':values,**stats,'seed':p.digest_words(transcript.seed)})
            except ValueError as e:
                assert transcript.seed==before
                expected.append({'error':str(e),'seed':p.digest_words(transcript.seed)})
    payloads=[p.field_words(row) for row in leaves]
    root,layers=p.merkle_tree(payloads,context)
    paths=[p.merkle_path(layers,i) for i in range(len(leaves))]
    with tempfile.TemporaryDirectory(prefix='near-pq384-parity-') as tmp:
        source=Path(tmp)/'input.json';output=Path(tmp)/'output.json'
        source.write_text(json.dumps({'statement_hex':statement.hex(),'context_hex':context.hex(),
                                      'leaves':leaves,'events':events}))
        subprocess.run([str(a.native.resolve()),str(source),str(output)],check=True)
        actual=json.loads(output.read_text())
    assert actual=={'events':expected,'root':p.digest_words(root),
                    'paths':[[p.digest_words(h) for h in path] for path in paths]}
    assert sum(e.get('rejected_words',0) for e in expected)>0
    rejected=[]
    def reject(label,call):
        try:call()
        except ValueError:rejected.append(label)
        else:raise AssertionError('accepted '+label)
    for i,(leaf,path) in enumerate(zip(payloads,paths)):
        assert p.verify_path(root,context,len(leaves),i,leaf,path)
        reject('leaf mutation',lambda i=i,leaf=leaf,path=path:p.verify_path(root,context,8,i,leaf+b'\0',path))
        reject('index substitution',lambda i=i,leaf=leaf,path=path:p.verify_path(root,context,8,i^1,leaf,path))
        reject('context substitution',lambda i=i,leaf=leaf,path=path:p.verify_path(root,context+b'\0',8,i,leaf,path))
        reject('truncated digest',lambda i=i,leaf=leaf,path=path:p.verify_path(root[:32],context,8,i,leaf,path))
        reject('truncated path',lambda i=i,leaf=leaf,path=path:p.verify_path(root,context,8,i,leaf,path[:-1]))
    for word,expected_value in [(0,0),(p.P-1,p.P-1),(p.P,0),(2*p.P-1,p.P-1),(2*p.P,None),((1<<32)-1,None)]:
        assert p.accept_word(word)==expected_value
    reject('noncanonical field leaf',lambda:p.field_words([p.P]))
    reject('nonword sample',lambda:p.accept_word(1<<32))
    reject('legacy256bit digest',lambda:p.digest_words(bytes(32)))
    assert p.hash_parts(b'x',b'ab',b'c')!=p.hash_parts(b'x',b'a',b'bc')
    assert p.hash_parts(b'x',b'abc')!=p.hash_parts(b'y',b'abc')
    t1=p.Transcript(statement);t2=p.Transcript(statement)
    assert t1.draw(b'same',2,4)[0]!=t2.draw(b'same',4,2)[0]
    old=t1.seed;t1.draw(b'same',2,4);assert t1.seed!=old
    result={'status':'PASS','hash':'SHA-384','digest_words':12,
            'python_rust_events_equal':len(events),'actual_d1_row_leaves':len(leaves),
            'merkle_paths_verified':len(paths),'mutations_rejected':len(rejected),
            'sample_rejections_observed':sum(e.get('rejected_words',0) for e in expected),
            'sampler_word_limit':p.LIMIT,'sampler_preimages_per_residue':2,
            'native_root_words':actual['root'],'test_events':events,'expected_events':expected,
            'limitations':['New standalone primitive version; not integrated into the D1 PCS/prover.',
                           'Leaf test commits raw rows, not a Reed-Solomon proximity proof.',
                           'Coefficient counts10/16 are test dimensions, not selected field extensions.',
                           'No hash-uniformity, QROM or128bitsecurity theorem.']}
    a.report.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('test_events','expected_events')}))


if __name__=='__main__':main()
