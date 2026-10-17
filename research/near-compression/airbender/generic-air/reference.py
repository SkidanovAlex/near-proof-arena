#!/usr/bin/env python3
"""Full-witness reference interpreter for canonical np-air-v1/v2 exports.

Not a proof verifier: reads every private trace cell and counts every interaction.
The field modulus is trusted configuration (caller must choose a prime). Values
on the wire are canonical natural representatives, never Montgomery encoding.
"""
from collections import Counter

P = 2013265921


def require(ok, message):
    if not ok:
        raise ValueError(message)


def nat(x):
    return type(x) is int and x >= 0


def expr_degree(e, width, num_pub):
    require(isinstance(e, list) and e and isinstance(e[0], str), 'expression shape')
    op = e[0]
    if op in ('c', 'p'):
        require(len(e) == 2 and nat(e[1]), 'constant/public encoding')
        if op == 'p':
            require(e[1] < num_pub, 'public reference bound')
        return 0
    if op == 'v':
        require(len(e) == 3 and nat(e[1]) and e[1] < width and
                type(e[2]) is int and e[2] in (0, 1), 'column reference')
        return 1
    if op in ('first', 'last', 'trans'):
        require(len(e) == 1, 'selector encoding')
        return 1
    if op == '-':
        require(len(e) == 2, 'negation encoding')
        return expr_degree(e[1], width, num_pub)
    require(op in ('+', '*') and len(e) == 3, 'binary expression encoding')
    a, b = (expr_degree(x, width, num_pub) for x in e[1:])
    return max(a, b) if op == '+' else a + b


def evaluate(e, rows, row, public, modulus=P):
    """Expr.evalWith under the source rowEnv, after schema validation."""
    op = e[0]
    if op == 'c':
        return e[1] % modulus
    if op == 'p':
        return public[e[1]] if e[1] < len(public) else 0
    if op == 'v':
        return rows[(row + e[2]) % len(rows)][e[1]]
    if op == 'first':
        return int(row == 0)
    if op == 'last':
        return int(row + 1 == len(rows))
    if op == 'trans':
        return int(row + 1 != len(rows))
    a = evaluate(e[1], rows, row, public, modulus)
    if op == '-':
        return -a % modulus
    b = evaluate(e[2], rows, row, public, modulus)
    return (a + b if op == '+' else a * b) % modulus


def schema(air):
    require(isinstance(air, dict) and air.get('format') in ('np-air-v1', 'np-air-v2'), 'AIR format')
    require(nat(air['numBuses']) and nat(air['numPub']) and isinstance(air['tables'], list), 'AIR shape')
    for table in air['tables']:
        require(nat(table['width']) and nat(table['maxLog']) and 1 <= table['maxLog'] <= 22,
                'table geometry')
        require(isinstance(table['constraints'], list) and isinstance(table['interactions'], list), 'table lists')
        for e in table['constraints']:
            expr_degree(e, table['width'], air['numPub'])
        for interaction in table['interactions']:
            require(nat(interaction['bus']) and interaction['bus'] < air['numBuses'] and
                    type(interaction['send']) is bool, 'interaction bus/direction')
            require(isinstance(interaction['msg'], list) and isinstance(interaction['mult'], list)
                    and len(interaction['mult']) <= 25, 'interaction lists')
            for e in interaction['msg'] + interaction['mult']:
                expr_degree(e, table['width'], air['numPub'])
    if air['format'] == 'np-air-v2':
        require(nat(air['maxPub']) and isinstance(air['pubSegs'], list), 'public segment list')
        for segment in air['pubSegs']:
            require(all(nat(segment[k]) for k in ('bus', 'width', 'countAt', 'start')) and
                    segment['bus'] < air['numBuses'] and segment['width'] > 0 and
                    type(segment['send']) is bool, 'segment geometry')
            require(isinstance(segment['prefix'], list) and all(nat(n) for n in segment['prefix']), 'segment prefix')
            require(all(segment[k] is None or nat(segment[k]) for k in ('startAt', 'indexBase')), 'segment optional index')


def public_messages(air, public, modulus=P):
    """Exact PubSeg.count/startOffset/record/fits, including getD-zero reads.

    Header digits are canonical field representatives, NOT restricted to bytes:
    the source leNat function itself does not impose the byte restriction.
    """
    if air['format'] == 'np-air-v1':
        return []
    def read4(offset):
        return sum((public[offset + k] if offset + k < len(public) else 0) * 256**k for k in range(4))
    result = []
    for segment in air['pubSegs']:
        count = read4(segment['countAt'])
        start = segment['start'] if segment['startAt'] is None else read4(segment['startAt'])
        require(start + count * segment['width'] <= min(len(public), air['maxPub']), 'public segment does not fit')
        for j in range(count):
            message = [v % modulus for v in segment['prefix']]
            if segment['indexBase'] is not None:
                message.append((segment['indexBase'] + j) % modulus)
            offset = start + j * segment['width']
            message.extend(public[offset:offset + segment['width']])
            result.append((segment['bus'], segment['send'], tuple(message)))
    return result


def inspect(air, traces, public, modulus=P):
    """Evaluate all obligations. Shape/encoding errors raise ValueError.

    Does not assert Air.wf's cryptographic degree/fingerprint/multiplicity budgets.
    Those are separate protocol prerequisites, not this full-witness evaluator.
    """
    require(type(modulus) is int and modulus > 2, 'field modulus')
    schema(air)
    require(isinstance(public, list) and all(nat(v) and v < modulus for v in public), 'canonical public field')
    require(isinstance(traces, list) and len(traces) == len(air['tables']), 'trace table count')
    violations, residuals, interaction_values = [], [], []
    counts = Counter()
    for ti, (table, rows) in enumerate(zip(air['tables'], traces)):
        require(isinstance(rows, list) and len(rows) >= 2 and len(rows) & (len(rows)-1) == 0
                and len(rows) <= 2**table['maxLog'], 'trace height')
        require(all(isinstance(row, list) and len(row) == table['width'] and
                    all(nat(v) and v < modulus for v in row) for row in rows), 'trace cells')
        table_residuals, table_interactions = [], []
        for ri in range(len(rows)):
            ev = lambda e: evaluate(e, rows, ri, public, modulus)
            values = [ev(e) for e in table['constraints']]
            table_residuals.append(values)
            violations.extend(['constraint', ti, ri, ci, value] for ci, value in enumerate(values) if value)
            row_interactions = []
            for ii, interaction in enumerate(table['interactions']):
                bits = [ev(e) for e in interaction['mult']]
                # multNat counts a bit iff it equals ONE, not its numeric value.
                multiplicity = sum(2**k for k, bit in enumerate(bits) if bit == 1)
                violations.extend(['multiplicity bit', ti, ri, ii, k, bit]
                                  for k, bit in enumerate(bits) if bit not in (0, 1))
                message = tuple(ev(e) for e in interaction['msg'])
                counts[(interaction['bus'], message)] += multiplicity * (1 if interaction['send'] else -1)
                row_interactions.append({'bits': bits, 'multiplicity': multiplicity, 'message': list(message)})
            table_interactions.append(row_interactions)
        residuals.append(table_residuals)
        interaction_values.append(table_interactions)
    messages = public_messages(air, public, modulus)
    for bus, send, message in messages:
        counts[(bus, message)] += 1 if send else -1
    violations.extend(['bus', bus, list(message), count] for (bus, message), count in sorted(counts.items()) if count)
    return {'accepted': not violations, 'violations': violations, 'residuals': residuals,
            'interactions': interaction_values, 'public_messages': [[b, s, list(m)] for b, s, m in messages]}


def check(air, traces, public, modulus=P):
    result = inspect(air, traces, public, modulus)
    require(result['accepted'], 'AIR obligations fail: ' + repr(result['violations'][:3]))
    return result
