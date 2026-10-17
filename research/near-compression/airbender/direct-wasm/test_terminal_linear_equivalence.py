"""Adversarial and generated checks of symbolic rewrite validation."""
import copy,json,random
import pq384_ext8_reference as f
from rebalance_terminal_linear import rebalance
from check_terminal_linear_equivalence import validate
from test_terminal_linear_rebalance import evaluate


def circuit(nodes, root=None):
    return dict(nodes=nodes, root=len(nodes)-1 if root is None else root,
                private_input_capacity=3,live_nodes=list(range(len(nodes))))


def rejects(source, target):
    try:
        validate(source,target)
    except ValueError:
        return
    raise AssertionError('invalid rewrite accepted')


def main():
    rng=random.Random(90881)
    for case in range(100):
        nodes=[['input',i] for i in range(3)]
        nodes += [['const',*v] for v in (f.ZERO,f.ONE,f.base(2),tuple(rng.randrange(f.P) for _ in range(8))) ]
        for _ in range(30):
            n=len(nodes);nodes.append([rng.choice(('add','sub','mul')),rng.randrange(n),rng.randrange(n)])
        old=circuit(nodes);new,_=rebalance(old);validate(old,new)
        for _ in range(3):
            inputs=[tuple(rng.randrange(f.P) for _ in range(8)) for _ in range(3)]
            assert evaluate(old,inputs)==evaluate(new,inputs)
        bad=copy.deepcopy(new);n=len(bad['nodes'])
        bad['nodes'] += [('const',*f.ONE),('add',bad['root'],n)]
        bad['root']=n+1;rejects(old,bad)
    base=circuit([['input',0],['input',1],['mul',0,1]])
    for nodes in (
        [['input',0],['input',1],['add',0,1]],
        [['input',0],['input',2],['mul',0,1]],
        [['input',0],['input',1],['mul',0,3]],
        [['input',0],['input',1],['mul',0,-1]],
        [['input',0],['input',1],['unknown',0,1]],
        [['input',0],['input',3],['mul',0,1]],
        [['input',0],['const',f.P,0,0,0,0,0,0,0],['mul',0,1]],
    ):
        rejects(base,circuit(nodes))
    bad=copy.deepcopy(base);bad['root']=-1;rejects(base,bad)
    bad=copy.deepcopy(base);bad['private_input_capacity']=4;rejects(base,bad)
    print(json.dumps(dict(status='PASS',generated_rewrites=100,differential_checks=300,
                         unequal_root_mutations=100,malformed_or_changed_circuits=9)))

if __name__=='__main__':main()
