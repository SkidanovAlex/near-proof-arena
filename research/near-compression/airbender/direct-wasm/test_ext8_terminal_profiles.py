"""Trusted-profile boundary, fail-closed rewrite checks and GKR binding."""
import copy,json
from unittest.mock import patch
import pq384_ext8_reference as f
import pq384_ext8_terminal_gkr as g
import ext8_terminal_profiles as profiles
from test_terminal_linear_rebalance import evaluate


def reject(action):
    try:action()
    except ValueError:return
    raise AssertionError('invalid profile/rewrite/proof accepted')


def main():
    nodes=[('input',0),('input',1),('input',2),('const',*f.base(2))]
    root=0
    for i in range(6):
        n=len(nodes);nodes.extend([('mul',root,3),('add',n,i%3)]);root=n+1
    source=dict(nodes=nodes,root=root,private_input_capacity=4,live_nodes=list(range(len(nodes))),input_blocks=[])
    assert profiles.apply(source) is source
    reject(lambda:profiles.apply(source,'from-proof'))
    good=profiles.apply(source,'affine-v1')
    bad=copy.deepcopy(good);bad['input_blocks']=[{'offset':1}]
    with patch('rebalance_terminal_linear.rebalance',return_value=(bad,{})):
        reject(lambda:profiles.apply(source,'affine-v1'))
    bad=copy.deepcopy(good);n=len(bad['nodes'])
    bad['nodes'] += [('const',*f.ONE),('add',bad['root'],n)];bad['root']=n+1
    with patch('rebalance_terminal_linear.rebalance',return_value=(bad,{})):
        reject(lambda:profiles.apply(source,'affine-v1'))
    private=[f.base(3),f.base(5),f.base(7),f.ZERO];claim=evaluate(source,private)
    layouts=[g.layer_circuit(c) for c in (source,good)]
    assert layouts[0]!=layouts[1]
    for i,layout in enumerate(layouts):
        proof,ob=g.prove(layout,b'profile-boundary-test',private,claim)
        checked=g.verify(layout,b'profile-boundary-test',json.loads(json.dumps(proof)),claim)
        assert checked==ob
        actual=f.ZERO
        for x,w in zip(private,checked['private_weights']):actual=f.add(actual,f.mul(x,w))
        assert actual==checked['private_claim']
        reject(lambda:g.verify(layouts[1-i],b'profile-boundary-test',proof,claim))
    print(json.dumps(dict(status='PASS',profile_gkr_roundtrips=2,cross_layout_rejections=2,
                         unknown_profile_rejected=True,changed_metadata_rejected=True,changed_root_rejected=True)))

if __name__=='__main__':main()
