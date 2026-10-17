"""Exact SHA384 transcript census for the saved compressed-root GKR.

No transcript optimization or security change. Static layout hashing may be
precomputed only when that layout is fixed in the trusted verifier key.
"""
import collections,gzip,hashlib,json,struct,types
from pathlib import Path
import pq384_primitives as p
import pq384_terminal_gkr as g
from prove_swirl_root_public_dag import context,OUT as GKR,SOURCE
from prove_swirl_weighted_dag import split_obligation

OUT=GKR.parent/'gkr-transcript-census'


def main():
    layout,slots,known,claim,statement,description=context()
    proof=json.loads(gzip.decompress((GKR/'proof.json.gz').read_bytes()))
    expected=g.verify(layout,statement,proof,claim)
    events=[];draws=[]
    def hp(tag,*parts):
        wire=p.PREFIX+struct.pack('<I',len(tag))+tag+struct.pack('<I',len(parts))
        wire+=b''.join(p.u64(len(x))+x for x in parts)
        digest=hashlib.sha384(wire).digest()
        assert digest==p.hash_parts(tag,*parts)
        events.append(dict(tag=tag.decode(),part_lengths=list(map(len,parts)),bytes=len(wire),
                           blocks=(len(wire)+17+127)//128,digest=digest.hex(),wire=wire.hex()))
        return digest
    def clone(f,**changes):return types.FunctionType(f.__code__,dict(f.__globals__,**changes),argdefs=f.__defaults__)
    cls=type('CapturedTranscript',(),{name:clone(getattr(p.Transcript,name),hash_parts=hp)
                                     for name in ('__init__','commit','draw')})
    begin=clone(g.begin,hash_parts=hp,Transcript=cls)
    def draw(t):
        result,meta=t.draw(b'gkr-challenge',1,4)
        draws.append(dict(value=result[0],**meta));return tuple(result[0])
    verify=clone(g.verify,begin=begin,draw=draw)
    actual=verify(layout,statement,proof,claim)
    assert actual==expected
    original_events=events.copy()
    from swirl_fixed_gkr_verifier import prepare
    fixed=prepare(layout,hash_function=hp,transcript_type=cls)
    events.clear()
    # Caller mutation after preparation cannot replace the frozen trusted key.
    old_root=layout['root'];layout['root']=old_root+1
    try:assert fixed(statement,proof,claim)==expected
    finally:layout['root']=old_root
    assert events==original_events[1:]
    specialized_blocks=sum(e['blocks'] for e in events)
    for changed_claim in [g.add(claim,g.ONE)]:
        try:fixed(statement,proof,changed_claim)
        except ValueError:pass
        else:raise AssertionError('changed claim accepted')
    events[:]=original_events
    # These three raw SHA384 calls occur outside g.verify in the existing driver.
    prefix=gzip.decompress((SOURCE/'public-prefix-log.txt.gz').read_bytes())
    descriptor=json.dumps(description,sort_keys=True,separators=(',',':')).encode()
    binding=json.dumps(dict(profile='nearproof-prefix-gkr-to-whir-v1',statement=description,gkr_proof=proof),sort_keys=True,separators=(',',':')).encode()
    assert hashlib.sha384(prefix).hexdigest()==description['prefix_log_sha384']
    assert hashlib.sha384(descriptor).digest()==statement
    assert hashlib.sha384(binding).digest()==(GKR.parent/'root-split-continuation/gkr-binding.bin').read_bytes()
    extra=[]
    for tag,wire in [('public-prefix-debug-log',prefix),('statement-description-json',descriptor),('continuation-binding-json',binding)]:
        extra.append(dict(tag=tag,bytes=len(wire),blocks=(len(wire)+144)//128,sha384=hashlib.sha384(wire).hexdigest()))
    assert events[0]['part_lengths']==[len(json.dumps(layout,sort_keys=True,separators=(',',':')).encode())]
    groups=collections.defaultdict(lambda:dict(calls=0,bytes=0,blocks=0))
    for e in events:
        for k in ('bytes','blocks'):groups[e['tag']][k]+=e[k]
        groups[e['tag']]['calls']+=1
    fixed=events[0]['blocks'];total=sum(e['blocks'] for e in events)
    report=dict(status='EXACT_GKR_HASH_PREIMAGES_REPLAYED',fixed_layout_specialization=dict(dynamic_preimages_identical=True,caller_layout_mutation_isolated=True,changed_claim_rejected=True,sha384_blocks=specialized_blocks),calls=len(events),sha384_blocks=total,
        fixed_layout_blocks=fixed,dynamic_transcript_blocks=total-fixed,
        external_hashes=extra,total_dynamic_with_external=total-fixed+sum(e['blocks'] for e in extra),
        challenges=len(draws),squeeze_blocks=sum(d['blocks'] for d in draws),rejected_words=sum(d['rejected_words'] for d in draws),
        groups=dict(groups),unique_preimages=len({e['wire'] for e in events}),
        limitations=['One root Ext4 diagnostic transcript; rejection count is instance-specific.',
                     'Only fixed layout hash can be precomputed without changing current protocol.',
                     'Debug-log/JSON boundary is current diagnostic format, not a production circuit codec.',
                     'Native prefix/PCS Poseidon hashing and arithmetic circuit costs excluded.',
                     'No generated hash proof, recursive closure, PQ128 or full NEAR claim.'])
    OUT.mkdir(exist_ok=True)
    (OUT/'events.json.gz').write_bytes(gzip.compress(json.dumps(dict(events=events,draws=draws),separators=(',',':')).encode(),mtime=0))
    (OUT/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))


if __name__=='__main__':main()
