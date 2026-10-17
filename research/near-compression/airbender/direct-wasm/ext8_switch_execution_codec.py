"""Separate experimental pooled-affine code-switch execution envelope. Trusted spec/roots/switch schedule required.
Uses full 32-byte extension scalars. Counts come only from the trusted spec
and reconstructed terminal circuit. No witness data or opening claims on wire.
"""
import struct
import verify_ext8_execution as v
import ext8_weighted_code_switch_codec as switch
MAGIC=b'NPEX8CS1'
MAX_BYTES=32*1024*1024
PROFILE='phase-pooled-affine-code-switch-v1'


def encode(reduction,opening,spec,roots,*,config,native=None):
    params=v.opening_parameters(reduction,spec,roots,terminal_profile="affine-v1",commitment_profile="phase-pooled-v1")
    switch.decode(opening,*params,config,native=native)
    out=bytearray(MAGIC)
    for root in roots+reduction['aux_roots']:out.extend(v.codec.p.hashread(root))
    for finals in reduction['finals']:out.extend(v.gkr.vector_bytes(finals))
    for table in reduction['local']:
        for coeff in table:out.extend(v.gkr.vector_bytes(coeff))
    for layer in reduction['gkr']['layers']:
        for coeff in layer['rounds']:out.extend(v.gkr.vector_bytes(coeff))
        out.extend(v.gkr.vector_bytes(layer['inputs']))
    out.extend(opening);v.require(len(out)<=MAX_BYTES,'execution size');return bytes(out)


def decode(wire,spec,roots,*,config,native=None):
    v.require(type(wire)is bytes and len(wire)<=MAX_BYTES,'execution size');offset=0
    def read(n):
        nonlocal offset
        v.require(0<=n<=len(wire)-offset,'truncated execution')
        result=wire[offset:offset+n];offset+=n;return result
    def scalar():return list(v.f.canonical(struct.unpack('<8I',read(32))))
    v.require(read(8)==MAGIC,'execution version')
    n=len(spec['air']['tables'])
    v.require(len(roots)==n,'source root count')
    v.require([read(48).hex() for _ in range(n)]==roots,'source root binding')
    ars=[read(48).hex() for _ in range(n)]
    finals=[[scalar() for _ in range(v.aux.layout(table)['finals'])] for table in spec['air']['tables']]
    local=[[[scalar() for _ in range(v.local.protocol.algebra.table_degree(table,spec['air']['numPub'])+2)] for _ in range(log)] for table,log in zip(spec['air']['tables'],spec['log_rows'])]
    reduction=dict(spec=spec,source_roots=roots,aux_roots=ars,finals=finals,local=local,gkr=None)
    prefix=v.reduction_prefix(reduction,spec,roots,terminal_profile="affine-v1",commitment_profile="phase-pooled-v1");layout=prefix[-1]
    layers=[]
    for i in range(len(layout['layers'])-1,-1,-1):
        prev=layout['input_size'] if i==0 else len(layout['layers'][i-1]);rounds=2*(prev.bit_length()-1)
        layers.append(dict(rounds=[[scalar() for _ in range(3)] for _ in range(rounds)],inputs=[scalar(),scalar()]))
    reduction['gkr']=dict(profile=v.gkr.PROFILE.decode(),layers=layers)
    opening=wire[offset:]
    params=v._opening_parameters(reduction,spec,roots,prefix,commitment_profile="phase-pooled-v1")
    switch.decode(opening,*params,config,native=native)
    return reduction,opening


if __name__=='__main__':
    import argparse,gzip,json
    from pathlib import Path
    from pq384_ext8_native import Kernel
    parser=argparse.ArgumentParser()
    for key in ('proof','statement','config'):parser.add_argument('--'+key,type=Path,required=True)
    parser.add_argument('--native-library',type=Path)
    args=parser.parse_args()
    def read(path):
        raw=path.read_bytes();return json.loads(gzip.decompress(raw) if path.suffix=='.gz' else raw)
    statement=read(args.statement);native=Kernel(args.native_library) if args.native_library else None
    decode(args.proof.read_bytes(),statement['spec'],statement['roots'],config=read(args.config),native=native)
    print('PASS full pooled-affine code-switch execution envelope; diagnostic security only.')
