"""Ext8 formula candidate: independent row semantics and register rejection.
Does not execute an Ext8 prover or certify native/compiler refinement.
"""
import argparse, copy, hashlib, json, random
from pathlib import Path
import check_bus_program_formulas as generator
import pq384_ext8_reference as f


def evaluate(ast, current, nxt, selectors):
    op = ast[0]
    if op == 'lit': return tuple(ast[1])
    if op == 'current': return f.base(current[ast[1]])
    if op == 'next': return f.base(nxt[ast[1]])
    if op in selectors: return selectors[op]
    return {'add': f.add, 'sub': f.sub, 'mul': f.mul}[op](
        evaluate(ast[1], current, nxt, selectors), evaluate(ast[2], current, nxt, selectors))


def compile_ast(ast, instructions):
    op = ast[0]
    if op == 'lit': row = [0, 0, 0, *ast[1]]
    elif op in ('current', 'next'): row = [1 if op == 'current' else 2, ast[1], 0, *f.ZERO]
    elif op in ('first', 'last', 'trans'): row = [{'first': 3, 'last': 4, 'trans': 5}[op], 0, 0, *f.ZERO]
    else:
        left = compile_ast(ast[1], instructions)
        right = compile_ast(ast[2], instructions)
        row = [{'add': 6, 'sub': 7, 'mul': 8}[op], left, right, *f.ZERO]
    instructions.append(row)
    return len(instructions)-1


def direct(k, current, nxt, selectors, alpha, gamma, finals):
    # Source fixture: receive bus0, msg=current0, k multiplicity bits=current0;
    # send bus1, msg=next0, one multiplicity bit=next0. Reconstruct by tuple
    # slicing, independently of the generator's basis expansion.
    aux = [tuple(current[i:i+8]) for i in range(1, len(current), 8)]
    next_aux = [tuple(nxt[i:i+8]) for i in range(1, len(nxt), 8)]
    p0 = f.sub(gamma, f.add(f.base(current[0]), alpha))
    bit = f.base(current[0]); chain = max(k-1, 0); residuals = []
    if not k: receive = f.ONE
    else:
        receive = f.add(f.ONE, f.mul(bit, f.sub(p0, f.ONE)))
        for j in range(chain):
            prev = p0 if j == 0 else aux[j-1]
            residuals.append(f.sub(aux[j], f.mul(prev, prev)))
        for j in range(chain):
            prev = receive if j == 0 else aux[chain+j-1]
            residuals.append(f.sub(aux[chain+j], f.mul(prev,
                f.add(f.ONE, f.mul(bit, f.sub(aux[j], f.ONE))))))
        if chain: receive = aux[2*chain-1]
    send_p = f.sub(gamma, f.add(f.base(nxt[0]), f.scale(alpha, 2)))
    send = f.add(f.ONE, f.mul(f.base(nxt[0]), f.sub(send_p, f.ONE)))
    for j, factor in enumerate((send, receive)):
        a = aux[2*chain+j]; an = next_aux[2*chain+j]; product = f.mul(a, factor)
        residuals.extend((f.mul(selectors['first'], f.sub(a, f.ONE)),
            f.mul(selectors['trans'], f.sub(an, product)),
            f.mul(selectors['last'], f.sub(product, finals[j]))))
    return residuals


def main():
    parser = argparse.ArgumentParser(); parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--capture', type=Path)
    args = parser.parse_args(); rng = random.Random(8048); comparisons = rejections = cases = 0; capture = []
    for k in (0, 1, 2, 4):
        table = {'width': 1, 'interactions': [
            {'send': False, 'bus': 0, 'msg': [['v', 0, False]], 'mult': [['v', 0, False]]*k},
            {'send': True, 'bus': 1, 'msg': [['v', 0, True]], 'mult': [['v', 0, True]]}]}
        for trial in range(6):
            rand = lambda: tuple(rng.randrange(f.P) for _ in range(8))
            alpha, gamma = (f.ZERO, f.ZERO) if trial == 0 else (rand(), rand())
            finals = [rand(), rand()]
            records, auxiliary = generator.expected(table, [], alpha, gamma, finals, field=f)
            width = 1+8*auxiliary
            current = [rng.randrange(f.P) for _ in range(width)]
            nxt = [rng.randrange(f.P) for _ in range(width)]
            selectors = dict(zip(('first', 'last', 'trans'), (rand(), rand(), rand())))
            if trial == 0:
                current = [0]*width; nxt = [0]*width
            actual = [evaluate(r['formula'], current, nxt, selectors) for r in records]
            assert actual == direct(k, current, nxt, selectors, alpha, gamma, finals)
            expanded, expanded_width = generator.expected(table, [], alpha, gamma, finals, field=f, expanded_messages=True)
            assert expanded_width == auxiliary
            assert [evaluate(r['formula'], current, nxt, selectors) for r in expanded] == actual
            comparisons += len(actual); cases += 1
            certificates = []
            for rec in records:
                ins = []; root = compile_ast(rec['formula'], ins)
                generator.validate_formula(rec['formula'], root, ins, width, {}, coordinate_degree=8)
                if trial < 2:
                    certificates.append(dict(formula=rec['formula'], instructions=ins, root=root,
                        expected=actual[len(certificates)]))
                for mode in ('root-op', 'literal', 'column'):
                    bad = copy.deepcopy(ins)
                    if mode == 'root-op': bad[root][0] = 99
                    elif mode == 'literal':
                        i = next(i for i, x in enumerate(bad) if x[0] == 0)
                        bad[i][3] = (bad[i][3]+1) % f.P
                    else:
                        i = next(i for i, x in enumerate(bad) if x[0] in (1, 2))
                        bad[i][1] = width
                    try: generator.validate_formula(rec['formula'], root, bad, width, {}, coordinate_degree=8)
                    except ValueError: rejections += 1
                    else: raise AssertionError('accepted mutation '+mode)
            if trial < 2:
                capture.append(dict(width=width,current=current,next=nxt,selectors=selectors,residuals=certificates,
                    table=table,public=[],alpha=alpha,gamma=gamma,finals=finals))
    if args.capture:
        args.capture.write_text(json.dumps(capture,separators=(',',':'))+'\n')
    report = {'status': 'PASS', 'cases': cases, 'residual_value_comparisons': comparisons,
        'register_mutation_rejections': rejections, 'expanded_vs_horner_residual_comparisons': comparisons,
        'scope': 'Ext8 candidate formula generation and independent row semantics; no prover/security/refinement claim.',
        'source_sha256': {name: hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest()
            for name in ('test_ext8_bus_formulas.py', 'check_bus_program_formulas.py', 'pq384_ext8_reference.py')}}
    args.output.write_text(json.dumps(report, indent=2)+'\n'); print(json.dumps(report))

if __name__ == '__main__': main()
