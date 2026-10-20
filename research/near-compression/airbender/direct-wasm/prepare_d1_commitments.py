#!/usr/bin/env python3
"""Commit real D1 source and auxiliary tables under the scheduled diagnostic PCS.

This prepares the inputs for the constraint prover; it does not emit a proof.
Every source root precedes bus challenges. Auxiliary columns use those challenges.
"""
import argparse
import array
import hashlib
import json
import os
from pathlib import Path
import struct
import subprocess
import sys
import time

import scheduled_bus_whir as protocol
from constraint_sumcheck import encode


def load_rows(directory, meta, table):
    path = directory / meta['file']
    data = path.read_bytes()
    n, width = struct.unpack_from('<II', data)
    assert n == meta['log_rows'] and width == table['width'] == meta['width']
    assert len(data) == 8 + 4 * (1 << n) * width
    values = array.array('I'); values.frombytes(data[8:])
    if sys.byteorder != 'little': values.byteswap()
    assert max(values, default=0) < protocol.P
    return [list(values[i:i+width]) for i in range(0, len(values), width)]


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('trace', type=Path)
    ap.add_argument('air', type=Path)
    ap.add_argument('commitment_binary', type=Path)
    ap.add_argument('output', type=Path)
    args = ap.parse_args()
    started = time.monotonic()
    trace = args.trace.resolve(); out = args.output.resolve()
    out.mkdir(exist_ok=False)
    report = json.loads((trace/'report.json').read_text())
    air_bytes = args.air.read_bytes()
    assert report['trace_dumped'] and report['status'] == 'PASS'
    assert hashlib.sha256(air_bytes).hexdigest() == report['sha256']['air']
    tape = (trace/'prepared.bin').read_bytes()
    assert hashlib.sha256(tape).hexdigest() == report['sha256']['prepared']
    spec = {'air': json.loads(air_bytes), 'public': list(tape),
            'log_rows': [t['log_rows'] for t in report['tables']]}
    protocol.validate(spec)
    assert len(report['tables']) == len(spec['air']['tables']) == 33
    def save(name, value):
        path = out/name
        path.write_text(json.dumps(value, separators=(',', ':'))+'\n')
        return path
    save('spec.json', spec)
    def commit(name, rows):
        source = save(name+'-rows.json', {'rows': rows})
        target = out/(name+'-commitment.json')
        subprocess.run([str(args.commitment_binary.resolve()), str(source), str(target),
                        '--root-only'], check=True, stdout=subprocess.DEVNULL)
        result = json.loads(target.read_text())
        protocol.check_roots([result['root']], 1)
        assert result['log_rows'] == len(rows).bit_length()-1
        assert result['columns'] == len(rows[0])
        return result['root']
    roots = []
    for ti, (meta, table) in enumerate(zip(report['tables'], spec['air']['tables'])):
        assert meta['index'] == ti
        rows = load_rows(trace, meta, table)
        roots.append(commit(f'source-{ti:02}', rows))
        print(f'committed source table {ti}', flush=True)
    words, transcript, alpha, gamma = protocol.begin(spec, roots)
    save('source-statement.json', {'roots': roots})
    aux_roots, finals = [], []
    for ti, (meta, table) in enumerate(zip(report['tables'], spec['air']['tables'])):
        rows = load_rows(trace, meta, table)
        witness = protocol.aux.generate(table, rows, spec['public'], alpha, gamma)
        coordinates = protocol.flatten_aux_rows(table, witness['aux_rows'], spec['log_rows'][ti])
        aux_roots.append(commit(f'aux-{ti:02}', coordinates))
        finals.append([encode(v) for v in witness['finals']])
        print(f'committed auxiliary table {ti}', flush=True)
    protocol.initialize_aux(transcript, spec['air']['tables'], aux_roots, finals)
    assert protocol.global_balance(spec, finals, alpha, gamma)
    save('prover-input.json', {'roots': roots, 'aux_roots': aux_roots, 'finals': finals,
                             'statement_words': words})
    save('preparation-report.json', {
        'status': 'PASS', 'tables': 33, 'source_cells': report['total_cells'],
        'seconds': time.monotonic()-started, 'proof_emitted': False,
        'air_sha256': report['sha256']['air'], 'trace_directory': str(trace),
        'scope': 'Real source and auxiliary commitments with challenge ordering and global product check; constraint proof and PCS openings still required.',
        'security_bits_claimed': None})


if __name__ == '__main__':
    main()
