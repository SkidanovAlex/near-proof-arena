"""Experimental fixed-input envelope; trusted configuration, not proof metadata.

Separate from existing profiles. The whole returned layout is transcript-bound
by the existing GKR implementation. This does not establish causal sampling,
compiler soundness, PCS authentication or QROM security.
"""
from pq384_primitives import require
from pq384_terminal_gkr import layer_circuit


def fixed_layer_circuit(circuit, *, input_log):
    require(type(input_log) is int and 1<=input_log<=25,'trusted input log')
    layout=layer_circuit(circuit)
    target=1<<input_log
    require(layout['input_size']<=target,'fixed input envelope overflow')
    require(bool(layout['layers']),'fixed envelope requires arithmetic layer')
    old_zero=layout['input_size']-1
    new_zero=target-1
    # Only the first arithmetic layer addresses input positions. Later layers
    # address gate outputs; their zero slot is already index zero.
    layout['layers'][0]=[(op,new_zero if a==old_zero else a,
                            new_zero if b==old_zero else b)
                           for op,a,b in layout['layers'][0]]
    layout['input_size']=target
    layout['fixed_input_profile']='near-pq384-gkr-fixed-input-v1'
    layout['fixed_input_log']=input_log
    return layout
