"""Operational sampler/schedule checks, not Fiat-Shamir security proofs."""
from unittest.mock import patch
from fused_gkr_transcript import candidate,FusedTranscript
import pq384_primitives as p

def main():
    g=candidate();t=FusedTranscript({},b'statement',g.ONE,g)
    def rejects(f):
        try:f()
        except ValueError:return
        raise AssertionError('accepted invalid operation')
    rejects(lambda:t.draw(b'gkr-challenge',1,4))
    t.commit(b'gkr-vector',b'payload');rejects(lambda:t.commit(b'gkr-vector',b'extra'))
    before=t.graph();seed=t.seed;pending=t.pending
    # Retry exhaustion must preserve the pending commit and previous seed/graph.
    import copy
    before=copy.deepcopy(before)
    with patch.object(p,'hash_parts',return_value=b'\xff'*48):
        rejects(lambda:t.draw(b'gkr-challenge',1,4,max_blocks=2))
    assert t.graph()==before and t.seed==seed and t.pending==pending and t.round==0
    # First block wholly rejected; second yields four zeros. Both calls bind counters.
    with patch.object(p,'hash_parts',side_effect=[b'\xff'*48,b'\0'*48]):
        values,meta=t.draw(b'gkr-challenge',1,4,max_blocks=2)
    assert values==[[0,0,0,0]] and meta==dict(blocks=2,rejected_words=12)
    assert t.round==1 and t.pending is None and t.resolve(t.seed)==b'\0'*48
    assert [n['parts'][-1] for n in t.nodes[1:]]==[['literal',p.u64(i).hex()] for i in [0,1]]
    t.commit(b'gkr-vector',b'next')
    rejects(lambda:t.draw(b'wrong',1,4));rejects(lambda:t.draw(b'gkr-challenge',2,4))
    print('PASS: missing/double commit, exhaustion rollback, forced retry, counters, label/shape rejection')

if __name__=='__main__':main()
