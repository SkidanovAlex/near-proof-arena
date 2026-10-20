"""Ext8 auxiliary witness generation, adapted from bus_auxiliary semantics.
No commitment or security claim; source Booleanity is checked separately.
"""
from pq384_ext8_reference import P,ZERO,ONE,add,sub,mul,power
from pq384_primitives import require

def base(n):return (n%P,)+(0,)*7
def canonical(v):return isinstance(v,(tuple,list)) and len(v)==8 and all(type(x)is int and 0<=x<P for x in v)

def layout(table):
    interactions = table['interactions']
    require(isinstance(interactions, list), 'interaction list')
    chains = 0
    for i in interactions:
        require(type(i['send']) is bool and type(i['bus']) is int and 0 <= i['bus'] < P-1,
                'interaction direction/tag')
        require(isinstance(i['mult'], list) and isinstance(i['msg'], list), 'interaction expressions')
        chains += 2*max(0, len(i['mult'])-1)
    order = [j for j,i in enumerate(interactions) if i['send']] + [j for j,i in enumerate(interactions) if not i['send']]
    return {'chain_columns': chains, 'aux_columns': chains+len(order), 'finals': len(order), 'order': order}


def expr(e, current, nxt, public, selectors):
    require(isinstance(e, list) and len(e) >= 1, 'expression shape')
    op = e[0]
    if op in ('c', 'p'):
        require(len(e) == 2 and type(e[1]) is int and e[1] >= 0, 'constant/public expression')
        return base(e[1]) if op == 'c' else base(public[e[1]] if e[1] < len(public) else 0)
    if op == 'v':
        require(len(e) == 3 and type(e[1]) is int and 0 <= e[1] < len(current) and
                type(e[2]) is int and e[2] in (0, 1), 'column expression')
        return tuple((nxt if e[2] else current)[e[1]])
    if op in ('first', 'last', 'trans'):
        require(len(e) == 1, 'selector expression')
        return tuple(selectors[op])
    if op == '-':
        require(len(e) == 2, 'negation expression')
        return sub(ZERO, expr(e[1], current, nxt, public, selectors))
    require(op in ('+', '*') and len(e) == 3, 'binary expression')
    a, b = (expr(x, current, nxt, public, selectors) for x in e[1:])
    return (add if op == '+' else mul)(a, b)


def fingerprint(interaction, ev, alpha):
    acc, weight = ZERO, ONE
    for e in interaction['msg']:
        acc = add(acc, mul(ev(e), weight)); weight = mul(weight, alpha)
    return add(acc, mul(base(interaction['bus']+1), weight))


def environment_check(table, current, nxt, public, selectors, alpha, gamma):
    require(type(table['width']) is int and table['width'] >= 0 and
            len(current) == len(nxt) == table['width'], 'source column count')
    require(all(canonical(v) for v in list(current)+list(nxt)+[alpha,gamma]), 'canonical extension field')
    require(isinstance(public, list) and all(type(x) is int and 0 <= x < P for x in public), 'canonical public field')
    require(set(selectors) == {'first','last','trans'} and all(canonical(v) for v in selectors.values()), 'selectors')


def evaluate(table, current, next, public, selectors, alpha, gamma, aux_current, aux_next, finals):
    """Exact residual order: chains in interaction order, then send/recv groups.

    Enforces lengths strictly before the source definition's zip/take operations.
    Evaluates at arbitrary extension-valued points; does not assume Boolean bits.
    """
    environment_check(table,current,next,public,selectors,alpha,gamma)
    shape = layout(table)
    require(len(aux_current) == len(aux_next) == shape['aux_columns'] and len(finals) == shape['finals'], 'auxiliary/final count')
    require(all(canonical(v) for v in list(aux_current)+list(aux_next)+list(finals)), 'canonical auxiliary field')
    ev = lambda e: expr(e,current,next,public,selectors)
    residuals, factors, offset = [], [], 0
    for interaction in table['interactions']:
        p0 = sub(gamma, fingerprint(interaction,ev,alpha))
        bits = [ev(e) for e in interaction['mult']]
        if not bits:
            factors.append(ONE); continue
        first = add(ONE,mul(bits[0],sub(p0,ONE)))
        if len(bits) == 1:
            factors.append(first); continue
        k = len(bits)-1
        ps = aux_current[offset:offset+k]
        pis = aux_current[offset+k:offset+2*k]
        previous = [p0]+list(ps)
        residuals.extend(sub(pj,mul(prev,prev)) for pj,prev in zip(ps,previous))
        previous_pi = [first]+list(pis)
        residuals.extend(sub(pi,mul(prev,add(ONE,mul(bit,sub(pj,ONE)))))
                         for pi,prev,bit,pj in zip(pis,previous_pi,bits[1:],ps))
        factors.append(tuple(pis[-1])); offset += 2*k
    for j, index in enumerate(shape['order']):
        a, an, final = aux_current[offset+j], aux_next[offset+j], finals[j]
        residuals.extend((mul(selectors['first'],sub(a,ONE)),
                          mul(selectors['trans'],sub(an,mul(a,factors[index]))),
                          mul(selectors['last'],sub(mul(a,factors[index]),final))))
    return residuals


def generate(table, rows, public, alpha, gamma):
    """Generate without division, including zero factors and empty bit lists.

    Nonboolean source bits are not silently repaired: generation uses source
    arithmetic, while source allConstraints must separately enforce Booleanity.
    """
    shape = layout(table)
    require(isinstance(rows,list) and len(rows) >= 2 and len(rows)&(len(rows)-1) == 0, 'power-of-two rows')
    require(all(isinstance(row,list) and len(row) == table['width'] and
                all(type(x) is int and 0 <= x < P for x in row) for row in rows), 'canonical source rows')
    accumulators = [ONE]*len(shape['order'])
    aux_rows = []
    for r, row in enumerate(rows):
        current, nxt = [base(x) for x in row], [base(x) for x in rows[(r+1)%len(rows)]]
        selectors = {'first':base(int(r==0)), 'last':base(int(r+1==len(rows))), 'trans':base(int(r+1!=len(rows)))}
        environment_check(table,current,nxt,public,selectors,alpha,gamma)
        ev = lambda e: expr(e,current,nxt,public,selectors)
        chains, factors = [], []
        for interaction in table['interactions']:
            p = sub(gamma,fingerprint(interaction,ev,alpha))
            bits = [ev(e) for e in interaction['mult']]
            if not bits:
                factors.append(ONE); continue
            value = add(ONE,mul(bits[0],sub(p,ONE)))
            ps, pis = [], []
            for bit in bits[1:]:
                p = mul(p,p); ps.append(p)
                value = mul(value,add(ONE,mul(bit,sub(p,ONE)))); pis.append(value)
            chains.extend(ps+pis); factors.append(value)
        aux_rows.append(chains+accumulators.copy())
        accumulators = [mul(a,factors[index]) for a,index in zip(accumulators,shape['order'])]
    return {'aux_rows':aux_rows,'finals':accumulators}
