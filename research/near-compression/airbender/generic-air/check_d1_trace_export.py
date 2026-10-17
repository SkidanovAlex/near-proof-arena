#!/usr/bin/env python3
"""Check exported D1 geometry/encoding and sample canonical AIR residuals.

This reads witnesses. It is not a succinct verifier or full independent bus check.
"""
import argparse
import array
from collections import Counter
from functools import lru_cache
import hashlib
import json
import mmap
from pathlib import Path
import struct
import sys
from reference import P, schema, evaluate, public_messages, require


def digest(path):
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for chunk in iter(lambda: stream.read(1 << 20), b''):
            h.update(chunk)
    return h.hexdigest()


def check_samples(directory, air, report, public):
    payload = json.loads((directory/'samples.json').read_text())
    tables = payload['tables'] if isinstance(payload, dict) else payload
    require(len(tables) == len(air['tables']) == 33, 'sample table count')
    checked = cells = 0
    for ti, (table, sample_table, meta) in enumerate(zip(air['tables'], tables, report['tables'])):
        require(sample_table['index'] == meta['index'] == ti, 'sample order')
        n, width = sample_table['log_rows'], sample_table['width']
        require(n == meta['log_rows'] and 1 <= n <= table['maxLog'] and
                width == meta['width'] == table['width'], 'sample geometry')
        height = 1 << n
        expected_rows = sorted({0, 1, height//2, height-2, height-1})
        require([s['row'] for s in sample_table['samples']] == expected_rows, 'sample boundary coverage')
        available = {}
        for sample in sample_table['samples']:
            row = sample['row']
            for index, values in ((row, sample['current']), ((row+1) % height, sample['next'])):
                require(len(values) == width and all(type(v) is int and 0 <= v < P for v in values),
                        'canonical sampled cells')
                if index in available:
                    require(available[index] == values, 'overlapping sample consistency')
                available[index] = values
                cells += width

        class Rows:
            def __len__(self):
                return height

            def __getitem__(self, index):
                return available[index]

        witness = Rows()
        for row in expected_rows:
            for ci, expression in enumerate(table['constraints']):
                require(evaluate(expression, witness, row, public) == 0,
                        f'sample residual table{ti} row{row} constraint{ci}')
                checked += 1
            for interaction in table['interactions']:
                for bit in interaction['mult']:
                    require(evaluate(bit, witness, row, public) in (0, 1), 'sample bit Booleanity')
    return {'status': 'PASS', 'table_count': len(tables), 'sampled_cells_checked': cells,
            'sampled_constraint_residuals': checked,
            'samples_sha256': digest(directory/'samples.json'),
            'limitations': ['Independent boundary/interior sample checks, not a full trace check or proof.',
                            'Full constraints and exact bus balance are native exporter evidence only.']}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('directory', type=Path)
    parser.add_argument('air', type=Path)
    parser.add_argument('--full', action='store_true', help='check every dumped row and exact natural bus balance')
    args = parser.parse_args()
    directory = args.directory.resolve()
    air = json.loads(args.air.read_text())
    schema(air)
    report = json.loads((directory/'report.json').read_text())
    require(len(report['tables']) == len(air['tables']) == 33, 'D1 table count')
    public = list((directory/'prepared.bin').read_bytes())
    messages = public_messages(air, public)
    require(not args.full or report['trace_dumped'], 'full check requires binary trace dump')
    counts = Counter()
    if not report['trace_dumped']:
        result = check_samples(directory, air, report, public)
        result.update({'air_sha256': digest(args.air), 'prepared_sha256': digest(directory/'prepared.bin'),
                       'public_messages': len(messages)})
        (directory/'independent-check.json').write_text(json.dumps(result, indent=2)+'\n')
        print(json.dumps(result))
        return
    checked, cells, tables = 0, 0, []
    for ti, (table, meta) in enumerate(zip(air['tables'], report['tables'])):
        require(meta['index'] == ti, 'table order')
        path = directory/meta['file']
        require(path.parent == directory, 'table file location')
        file_digest = digest(path)
        with path.open('rb') as stream:
            header = stream.read(8)
            require(len(header) == 8, 'table header')
            n, width = struct.unpack('<II', header)
            require(1 <= n <= table['maxLog'] and width == table['width'], 'canonical AIR geometry')
            rows = 1 << n
            require(meta['log_rows'] == n and meta['rows'] == rows and meta['width'] == width,
                    'report/header geometry agreement')
            require(path.stat().st_size == 8+4*rows*width, 'exact trace file length')
            # Scan every coordinate for canonical representation; bounded memory.
            for chunk in iter(lambda: stream.read(1 << 20), b''):
                values = array.array('I')
                values.frombytes(chunk)
                if sys.byteorder != 'little':
                    values.byteswap()
                require(max(values, default=0) < P, 'noncanonical field cell')
            with mmap.mmap(stream.fileno(), 0, access=mmap.ACCESS_READ) as mapped:
                class Rows:
                    def __len__(self):
                        return rows

                    @lru_cache(maxsize=32)
                    def __getitem__(self, row):
                        return struct.unpack_from('<'+'I'*width, mapped, 8+4*row*width)

                witness = Rows()
                # Boundary/cyclic-next rows plus deterministic interior samples.
                indices = sorted({0, 1, rows//2, rows-2, rows-1,
                                  int(file_digest[:16], 16) % rows})
                if args.full:
                    indices = range(rows)
                for row in indices:
                    for ci, expression in enumerate(table['constraints']):
                        require(evaluate(expression, witness, row, public) == 0,
                                f'constraint residual table{ti} row{row} constraint{ci}')
                        checked += 1
                    for interaction in table['interactions']:
                        bits = [evaluate(bit, witness, row, public) for bit in interaction['mult']]
                        require(all(bit in (0, 1) for bit in bits), 'multiplicity Booleanity')
                        if args.full:
                            mult = sum(1 << k for k, bit in enumerate(bits) if bit == 1)
                            if mult:
                                message = tuple(evaluate(e, witness, row, public) for e in interaction['msg'])
                                counts[(interaction['bus'], message)] += mult * (1 if interaction['send'] else -1)
                tables.append({'index': ti, 'rows': rows, 'width': width,
                               'checked_rows': rows if args.full else indices, 'sha256': file_digest})
                cells += rows*width
    if args.full:
        for bus, send, message in messages:
            counts[(bus, tuple(message))] += 1 if send else -1
        require(all(count == 0 for count in counts.values()), 'exact natural bus balance')
    result = {'status': 'PASS', 'table_count': len(tables), 'canonical_cells_scanned': cells,
              'sampled_constraint_residuals': checked, 'public_messages': len(messages),
              'air_sha256': digest(args.air), 'prepared_sha256': digest(directory/'prepared.bin'),
              'tables': tables,
              'limitations': ['Full witness read; not a succinct proof.',
                             'All cell encodings checked, but only sampled rows independently constraint-checked.',
                             'Full constraint and exact bus checks remain the native exporter evidence.']}
    if args.full:
        result['full_constraint_residuals'] = result.pop('sampled_constraint_residuals')
        result['exact_bus_message_keys'] = len(counts)
        result['limitations'] = ['Full-witness diagnostic, not a succinct proof or formal implementation refinement.']
    target = 'independent-full-check.json' if args.full else 'independent-check.json'
    (directory/target).write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'tables'}))


if __name__ == '__main__':
    main()
