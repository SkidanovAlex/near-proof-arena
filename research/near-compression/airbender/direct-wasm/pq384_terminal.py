"""Deterministic small-oracle terminal for a NEW SHA384/Ext4 stage encoding.

The proof discloses coefficients; the verifier reconstructs every oracle leaf.
This is not zero knowledge. It is not yet wired to WHIR, and Ext4 is diagnostic.
Expected root, stage binding, degree, domain and residual come from the enclosing
verifier. Nothing here establishes preceding-round soundness or QROM security.
"""
from pq384_primitives import require, u64, field_words, merkle_tree
from packed_claim_handoff import canonical_ext
from check_whir_handoff import P, add, mul

ZERO=(0,0,0,0)


def terminal_context(stage_binding, degree_bound, domain_size, lanes):
    require(type(stage_binding)is bytes,'stage binding')
    require(type(degree_bound)is int and 1<=degree_bound<=64,'terminal degree cap')
    require(type(domain_size)is int and 4<=domain_size<=256 and
            domain_size&(domain_size-1)==0 and degree_bound<=domain_size,
            'terminal domain')
    require(type(lanes)is int and 1<=lanes<=64,'terminal lanes')
    omega=pow(440564289,(1<<27)//domain_size,P)
    require(pow(omega,domain_size,P)==1 and pow(omega,domain_size//2,P)==P-1,
            'primitive terminal root')
    return (b'NEAR-PQ384-TERMINAL-V1/Ext4-v4=11/natural-domain/lane-pairs/coeff-le-u32'
            +u64(len(stage_binding))+stage_binding
            +b''.join(u64(v) for v in (P,degree_bound,domain_size,lanes,omega))),omega


def matrix(values, lanes, degree_bound, label):
    require(isinstance(values,list) and len(values)==lanes,label+' lane shape')
    require(all(isinstance(row,list) and len(row)==degree_bound for row in values),
            label+' coefficient shape')
    return [[canonical_ext(v) for v in row] for row in values]


def horner(coefficients, x):
    value=ZERO
    for coefficient in reversed(coefficients):value=add(coefficient,mul(value,x))
    return value


def reconstructed_root(coefficients, context, domain_size, omega):
    leaves=[];x=1
    for _ in range(domain_size//2):
        values=[]
        for polynomial in coefficients:
            values.extend(horner(polynomial,(x,0,0,0)))
            values.extend(horner(polynomial,((-x)%P,0,0,0)))
        leaves.append(field_words(values));x=x*omega%P
    return merkle_tree(leaves,context)[0]


def verify_terminal(proof, *, expected_root, stage_binding, degree_bound,
                    domain_size, lanes, weights, claim):
    context,omega=terminal_context(stage_binding,degree_bound,domain_size,lanes)
    require(type(expected_root)is bytes and len(expected_root)==48,'terminal root')
    require(type(proof)is dict and set(proof)=={'profile','coefficients'},'terminal proof fields')
    require(proof['profile']=='near-pq384-terminal-v1','terminal profile')
    coefficients=matrix(proof['coefficients'],lanes,degree_bound,'proof')
    weights=matrix(weights,lanes,degree_bound,'residual')
    claim=canonical_ext(claim)
    require(reconstructed_root(coefficients,context,domain_size,omega)==expected_root,
            'terminal oracle root mismatch')
    residual=ZERO
    for polynomial,ws in zip(coefficients,weights):
        for coefficient,weight in zip(polynomial,ws):residual=add(residual,mul(coefficient,weight))
    require(residual==claim,'terminal residual mismatch')
    return True
