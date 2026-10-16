"""Canonical complete literal GKR diagnostic envelope; no trusted AIR JSON.

All public values, shapes, commitments, requested Wasm, method, prepaid gas and
proof bytes are carried. Verification also pins the caller's expected request.
This changes transport only, not the GKR/PCS transcript or security parameters.
"""
import argparse
import json
import struct
from pathlib import Path
import prepared_code_table_air as literal
from pq384_primitives import P, require
from verify_prepared_gkr_slice import verify as verify_slice

MAGIC = b'NPLG\x00\x01'
FIXED_MAGIC = b'NPLF\x00\x01'

def wire_magic(input_log):
    require(input_log is None or (type(input_log) is int and 1 <= input_log <= 25), 'trusted input log')
    return MAGIC if input_log is None else FIXED_MAGIC


def encode(proof, statement, request, *, input_log=None):
    verify_slice(proof, statement, request, input_log=input_log)
    spec = statement['spec']
    method = request['method'].encode('utf-8')
    wasm = bytes(request['wasm_bytes'])
    require(0 <= request['prepaid'] < 1 << 64, 'envelope gas range')
    require(len(spec['log_rows']) == len(statement['roots']) == 2, 'literal table count')
    out = bytearray(wire_magic(input_log))
    if input_log is not None: out.append(input_log)
    out.extend(struct.pack('<I', len(spec['public'])))
    out.extend(struct.pack('<'+'I'*len(spec['public']), *spec['public']))
    out.extend(bytes(spec['log_rows']))
    for key in ('source_packings', 'aux_packings'):
        out.extend(struct.pack('<II', *spec[key]))
    out.extend(bytes([spec['terminal_degree']]))
    out.extend(b''.join(bytes.fromhex(r) for r in statement['roots']))
    out.extend(struct.pack('<I', len(wasm)))
    out.extend(wasm)
    out.extend(struct.pack('<I', len(method)))
    out.extend(method)
    out.extend(struct.pack('<QQ', request['prepaid'], len(proof)))
    out.extend(proof)
    return bytes(out)


def decode(data, *, input_log=None):
    magic = wire_magic(input_log)
    require(type(data) is bytes, 'envelope bytes')
    offset = 0
    def read(n):
        nonlocal offset
        require(0 <= n <= len(data)-offset, 'envelope truncation')
        out = data[offset:offset+n]
        offset += n
        return out
    def number(fmt):
        return struct.unpack(fmt, read(struct.calcsize(fmt)))[0]
    require(read(len(magic)) == magic, 'envelope profile')
    if input_log is not None: require(number('<B') == input_log, 'envelope trusted cap mismatch')
    count = number('<I')
    instructions, remainder = divmod(count-literal.CODEPUB, literal.RECORD)
    require(instructions > 0 and remainder == 0, 'literal public shape')
    raw = read(4*count)  # Bounds checked before allocation/unpacking/AIR reconstruction.
    public = list(struct.unpack('<'+'I'*count, raw))
    require(all(x < P for x in public), 'noncanonical public field')
    log_rows = list(read(2))
    source_packings = list(struct.unpack('<II', read(8)))
    aux_packings = list(struct.unpack('<II', read(8)))
    terminal_degree = number('<B')
    roots = [read(48).hex() for _ in range(2)]
    wasm = list(read(number('<I')))
    method = read(number('<I')).decode('utf-8', errors='strict')
    prepaid = number('<Q')
    proof = read(number('<Q'))
    require(offset == len(data), 'envelope trailing bytes')
    statement = dict(spec=dict(air=literal.air(instructions), public=public, log_rows=log_rows,
                     source_packings=source_packings, aux_packings=aux_packings,
                     terminal_degree=terminal_degree), roots=roots)
    request = dict(wasm_bytes=wasm, method=method, prepaid=prepaid)
    return proof, statement, request


def verify(data, expected_request, *, input_log=None):
    proof, statement, request = decode(data, input_log=input_log)
    require(request == expected_request, 'envelope caller request mismatch')
    return verify_slice(proof, statement, expected_request, input_log=input_log)


if __name__ == '__main__':
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('envelope', type=Path)
    ap.add_argument('expected_request', type=Path)
    ap.add_argument("--input-log", type=int, help="trusted fixed-input cap, checked against envelope")
    args = ap.parse_args()
    print(json.dumps(verify(args.envelope.read_bytes(), json.loads(args.expected_request.read_text()), input_log=args.input_log)))
