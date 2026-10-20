"""Prover-only partial folding; keeps heterogeneous_bus_whir verifier unchanged.

Avoids recomputing every column MLE for every Boolean suffix in sumcheck.
This is a diagnostic Python implementation, not a production throughput claim.
"""
import copy
import struct
import heterogeneous_bus_whir as protocol
from verify_whir_toy import P, ZERO, ONE, base, add, sub, mul, poly, require
from constraint_sumcheck import encode
import shift_opening as shift


def affine(a, b, r):
    return add(a, mul(r, sub(b, a)))


def fold_rows(rows, r):
    require(len(rows) >= 2 and len(rows) % 2 == 0, 'fold row count')
    return [[affine(a, b, r) for a, b in zip(rows[i], rows[i+1])]
            for i in range(0, len(rows), 2)]


def evaluate_rows(rows, point):
    values = rows
    for r in point:
        values = fold_rows(values, r)
    require(len(values) == 1, 'evaluation dimension')
    return values[0]


def boolean_point(index, n):
    return [base((index >> j) & 1) for j in range(n)]


def prove_shift(rows, point, transcript):
    n = len(point)
    width = len(rows[0])
    require(n > 0 and len(rows) == 2**n and width > 0, 'shift dimensions')
    require(all(len(row) == width and all(type(v) is int and 0 <= v < P for v in row)
                for row in rows), 'canonical rectangular rows')
    columns = [[base(v) for v in row] for row in rows]
    current = evaluate_rows(columns, point)
    nxt = evaluate_rows(columns[1:] + columns[:1], point)
    proof = {'current_evals': [encode(v) for v in current],
             'next_evals': [encode(v) for v in nxt], 'rounds': []}
    alpha, claim = shift.start_claim(proof, point, width, transcript)
    batched = [shift.batch(row, alpha) for row in columns]
    at = []
    for i in range(n):
        values = []
        for node in range(3):
            r = base(node)
            total = ZERO
            for index in range(len(batched)//2):
                x = at + [r] + boolean_point(index, n-i-1)
                value = affine(batched[2*index], batched[2*index+1], r)
                total = add(total, mul(shift.kernel(point, x, alpha, width), value))
            values.append(total)
        cs = shift.interpolate(values)
        require(add(poly(cs, ZERO), poly(cs, ONE)) == claim, 'folded shift identity')
        encoded = [encode(v) for v in cs]
        proof['rounds'].append(encoded)
        transcript.commit_ext(encoded)
        r = transcript.draw(1, True)[0]
        at.append(r)
        claim = poly(cs, r)
        batched = [affine(a, b, r) for a, b in zip(batched[::2], batched[1::2])]
    final = evaluate_rows(columns, at)
    require(claim == mul(shift.kernel(point, at, alpha, width), shift.batch(final, alpha)),
            'folded shift terminal')
    return proof, at, final


def prove(spec, roots, rows_by_table, aux_roots, aux_rows_by_table, finals_by_table, *, protocol_impl=None):
    protocol = protocol_impl if protocol_impl is not None else globals()['protocol']
    words, transcript, alpha, gamma = protocol.begin(spec, roots)
    tables = spec['air']['tables']
    degrees = protocol.validate(spec)
    require(len(rows_by_table) == len(aux_rows_by_table) == len(finals_by_table) == len(tables),
            'witness table count')
    require(all(isinstance(fs, list) and all(protocol.aux.canonical(v) for v in fs)
                for fs in finals_by_table), 'final fields')
    finals = [[encode(v) for v in fs] for fs in finals_by_table]
    protocol.initialize_aux(transcript, tables, aux_roots, finals)
    proof = {'aux_roots': copy.deepcopy(aux_roots), 'finals': finals, 'tables': []}
    handoffs = []
    for ti, (table, degree, source, auxiliary, fs) in enumerate(zip(
            tables, degrees, rows_by_table, aux_rows_by_table, finals_by_table)):
        n = spec['log_rows'][ti]
        require(len(source) == 2**n and all(len(row) == table['width'] and
                all(type(v) is int and 0 <= v < P for v in row) for row in source), 'source rows')
        coordinates = protocol.flatten_aux_rows(table, auxiliary, n)
        rows = [a+b for a, b in zip(source, coordinates)]
        current = [[base(v) for v in row] for row in rows]
        nxt = current[1:] + current[:1]
        mixing, tau = protocol.table_start(transcript, ti, n)
        point, rounds = [], []
        for i in range(n):
            values = []
            for node in range(degree+2):
                r = base(node)
                total = ZERO
                for index in range(len(current)//2):
                    at = point + [r] + boolean_point(index, n-i-1)
                    c = [affine(a, b, r) for a, b in zip(current[2*index], current[2*index+1])]
                    g = [affine(a, b, r) for a, b in zip(nxt[2*index], nxt[2*index+1])]
                    total = add(total, protocol.weighted(spec, ti, alpha, gamma, fs,
                                                        mixing, tau, at, c, g))
                values.append(total)
            encoded = [encode(v) for v in shift.interpolate(values)]
            rounds.append(encoded)
            transcript.commit_ext(encoded)
            r = transcript.draw(1, True)[0]
            point.append(r)
            current, nxt = fold_rows(current, r), fold_rows(nxt, r)
        reduction, at, _ = prove_shift(rows, point, transcript)
        proof['tables'].append({'constraint_rounds': rounds, 'shift_reduction': reduction})
        branches = []
        for branch, root in enumerate((roots[ti], aux_roots[ti])):
            fork = protocol.opening_transcript(transcript, ti, branch)
            branches.append({'root': root, 'statement_words': words, 'log_rows': n,
                             'pre_opening_seed': list(struct.unpack('<8I', fork.seed)),
                             'evaluation_point': [encode(v) for v in at]})
        handoffs.append(branches)
    return proof, handoffs
