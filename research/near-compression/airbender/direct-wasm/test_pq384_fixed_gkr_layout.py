"""Actual GKR reductions across varying live constants under one fixed cap."""
import json
import pq384_terminal_gkr as g
from pq384_fixed_gkr_layout import fixed_layer_circuit
from verify_whir_toy import base,ZERO
from check_whir_handoff import add,mul


def circuit(count):
    nodes=[['input',0]]
    root=0
    for i in range(count):
        k=len(nodes);nodes.append(['const',i+1,0,0,0])
        nodes.append(['add',root,k]);root=len(nodes)-1
    return dict(nodes=nodes,live_nodes=list(range(len(nodes))),private_input_capacity=2,root=root)


def main():
    checks=[];private=[base(7),base(11)]
    for count in (1,2,5):
        c=circuit(count);original=g.layer_circuit(c)
        fixed=fixed_layer_circuit(c,input_log=4)
        assert fixed['input_size']==16
        v=g.values(fixed,private);claim=v[-1][fixed['root']]
        assert claim==g.values(original,private)[-1][original['root']]
        proof,ob=g.prove(fixed,b'fixed-envelope-test',private,claim)
        assert g.verify(fixed,b'fixed-envelope-test',proof,claim)==ob
        dot=ZERO
        for w,x in zip(ob['private_weights'],private):dot=add(dot,mul(w,x))
        assert dot==ob['private_claim']
        assert len(proof['layers'][-1]['rounds'])==8
        # A different trusted cap cannot consume the old proof.
        changed=fixed_layer_circuit(c,input_log=5)
        try:g.verify(changed,b'fixed-envelope-test',proof,claim)
        except ValueError:pass
        else:raise AssertionError('changed envelope accepted')
        checks.append(dict(constants=count,old_input_size=original['input_size'],new_input_size=16,
                           final_input_rounds=8))
    for cap in (True,0,26):
        try:fixed_layer_circuit(circuit(1),input_log=cap)
        except ValueError:pass
        else:raise AssertionError('invalid cap')
    try:fixed_layer_circuit(circuit(5),input_log=2)
    except ValueError:pass
    else:raise AssertionError('overflow')
    print(json.dumps(dict(status='PASS',cases=checks,scope='Standalone fixed-input GKR; not integrated AIR/PCS or security proof'),indent=2))

if __name__=='__main__':main()
