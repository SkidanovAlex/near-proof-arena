"""Externally selected experimental terminal layouts, never proof-selected."""
PROFILES=('baseline','affine-v1')


def apply(circuit, profile='baseline'):
    if profile == 'baseline':
        return circuit
    if profile != 'affine-v1':
        raise ValueError('unknown terminal profile')
    from rebalance_terminal_linear import rebalance
    from check_terminal_linear_equivalence import validate
    rewritten,_=rebalance(circuit)
    # Check the actual instance, including the private-slot interpretation.
    if {k:v for k,v in circuit.items() if k not in ('nodes','root','live_nodes')} != {
            k:v for k,v in rewritten.items() if k not in ('nodes','root','live_nodes')}:
        raise ValueError('terminal metadata changed')
    validate(circuit,rewritten)
    return rewritten
