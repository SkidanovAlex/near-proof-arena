"""Actual-format counterexample to joint proximity extraction, NOT a false-claim attack.

Commit arbitrary source lanes h(X)=X^D and -h on the real RS domain. Equal
functional weights cancel them. Both weighted-joint verifiers accept the true
zero aggregate, despite each source being far from every degree<D codeword.
Only new /tmp artifacts are written; no reference implementation is modified.
"""
import argparse
import importlib
import json
import pathlib
import struct
import sys


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--reference',required=True,type=pathlib.Path)
    parser.add_argument('--out',required=True,type=pathlib.Path)
    args=parser.parse_args();sys.path.insert(0,str(args.reference));args.out.mkdir(parents=True,exist_ok=True)
    from pq384_primitives import P,field_words,merkle_tree,merkle_path
    from packed_claim_handoff import packing_context
    from pq384_one_fold import ZERO,ONE
    from pq384_cached_prover import FlatTree,flat
    from pq384_global_chain import round_start,disclose,sample
    D=128;N=4*D;n=7;context=packing_context(n,2,1)
    omega=pow(440564289,(1<<27)//N,P)
    points=[pow(omega,i,P) for i in range(N)]
    assert len(set(points))==N
    source=[pow(x,D,P) for x in points]
    leaves=[field_words([source[i],source[i+N//2],(-source[i])%P,(-source[i+N//2])%P]) for i in range(N//2)]
    root,layers=merkle_tree(leaves,context)
    branches=[dict(root=root.hex(),log_rows=n,width=2,packing=1,row_point=[list(ZERO)]*n,
        lanes=[[[list(ONE)],[list(ZERO)]],[[list(ONE)],[list(ZERO)]]])]
    statement=b'structured-batch-kernel-counterexample-v1';parent=b'fixed-public-derived-weight-parent'
    results=[]
    for name in ['pq384_weighted_joint','pq384_derived_weight_joint']:
        protocol=importlib.import_module(name)
        _,degree,_,transcript,claim=protocol.public(statement,parent,branches,list(ZERO))
        assert degree==D
        reduction=[];u=[]
        for _ in range(n):
            wire=[list(ZERO)]*3;r,_,claim=round_start(transcript,wire,claim);u.append(r);reduction.append(wire)
        beta=protocol.betas(branches,[D],D,u)[0]
        assert beta[0]==beta[1]
        trees=[];rounds=[]
        while degree>1:
            wire=[list(ZERO)]*3;r,stage,claim=round_start(transcript,wire,claim);degree//=2
            tree=FlatTree(flat([ZERO]*(4*degree)),protocol.context(stage,degree))
            transcript.commit(b'weighted-joint-next-root',tree.root)
            rounds.append(dict(quadratic=wire,next_root=tree.root.hex()));trees.append(tree)
        terminal=dict(profile='near-pq384-terminal-v1',coefficients=[[list(ZERO)]])
        disclose(transcript,terminal,1)
        queries=[]
        for s in sample(transcript,N):
            i=s%(N//2)
            opening=dict(leaf=list(struct.unpack('<4I',leaves[i])),path=[v.hex() for v in merkle_path(layers,i)])
            queries.append(dict(sources=[opening],folds=[tree.opening(s%tree.half) for tree in trees]))
        proof=dict(profile=protocol.PROFILE,reduction=reduction,rounds=rounds,terminal=terminal,queries=queries)
        assert protocol.verify(proof,statement,parent,branches,list(ZERO))
        try:protocol.verify(proof,statement,parent,branches,list(ONE))
        except ValueError as exc:wrong_claim_rejection=str(exc)
        else:raise AssertionError('changed nonzero claim unexpectedly accepted')
        (args.out/(name+'-proof.json')).write_text(json.dumps(proof,sort_keys=True)+'\n')
        results.append(dict(profile=protocol.PROFILE,accepted_true_zero=True,wrong_nonzero_claim_rejected=wrong_claim_rejection,
                            beta_equal=True,beta_nonzero=beta[0]!=ZERO,queries=len(queries)))
    result=dict(degree_bound=D,domain_size=N,source_polynomial='X^128 and -X^128',
        root=root.hex(),maximum_agreement_with_degree_less_than_D=D,
        minimum_joint_mismatches=N-D,shared_threshold=385,joint_radius_for_threshold=N-385,
        source_is_valid_degree_bound=False,classification='kernel extraction obstruction; not a false-claim attack',profiles=results)
    (args.out/'public.json').write_text(json.dumps(dict(statement_hex=statement.hex(),parent_hex=parent.hex(),branches=branches,claim=list(ZERO)),sort_keys=True)+'\n')
    (args.out/'result.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,sort_keys=True))

if __name__=='__main__':main()
