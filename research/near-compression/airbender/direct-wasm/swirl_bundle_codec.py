"""Fixed-profile binary bundle and key/layout-directed GKR codec.

Native sections are decoded and checked by the pinned Rust diagnostic verifier.
This module provides transport validation, not a cryptographic security proof.
"""
import struct
import pq384_terminal_gkr as g
P=2013265921
MAGIC=b'NPBND001'
MAX_BUNDLE=64*1024*1024


def layer_rounds(layout):
    for layer in range(len(layout['layers'])-1,-1,-1):
        prev=layout['input_size'] if layer==0 else len(layout['layers'][layer-1])
        yield 2*(prev-1).bit_length()


def encode_gkr(layout,proof):
    if set(proof)!={'profile','layers'} or proof['profile']!=g.PROFILE.decode():raise ValueError('GKR profile')
    counts=list(layer_rounds(layout))
    if len(proof['layers'])!=len(counts):raise ValueError('GKR layer count')
    words=[]
    for part,count in zip(proof['layers'],counts):
        if set(part)!={'rounds','inputs'} or len(part['rounds'])!=count or len(part['inputs'])!=2:raise ValueError('GKR layer shape')
        for row in part['rounds']:
            if len(row)!=3:raise ValueError('GKR round shape')
        for value in [v for row in part['rounds'] for v in row]+part['inputs']:
            if len(value)!=4 or any(type(x)is not int or not 0<=x<P for x in value):raise ValueError('noncanonical Ext4')
            words.extend(value)
    return struct.pack('<'+'I'*len(words),*words)


def decode_gkr(layout,data):
    counts=list(layer_rounds(layout));expected=16*sum(3*n+2 for n in counts)
    if len(data)!=expected:raise ValueError('GKR byte length')
    words=struct.unpack('<'+'I'*(len(data)//4),data)
    if any(x>=P for x in words):raise ValueError('noncanonical Ext4')
    cursor=0
    def take():
        nonlocal cursor
        value=list(words[cursor:cursor+4]);cursor+=4;return value
    layers=[]
    for count in counts:layers.append(dict(rounds=[[take(),take(),take()] for _ in range(count)],inputs=[take(),take()]))
    assert cursor==len(words)
    return dict(profile=g.PROFILE.decode(),layers=layers)


def pack(sections):
    if len(sections)!=4 or any(not x for x in sections):raise ValueError('four nonempty sections required')
    if 24+sum(map(len,sections))>MAX_BUNDLE:raise ValueError('bundle cap')
    return MAGIC+struct.pack('<4I',*map(len,sections))+b''.join(sections)


def unpack(data):
    if not 24<=len(data)<=MAX_BUNDLE or data[:8]!=MAGIC:raise ValueError('bundle envelope')
    sizes=struct.unpack('<4I',data[8:24])
    if any(n==0 for n in sizes) or 24+sum(sizes)!=len(data):raise ValueError('bundle lengths/trailing bytes')
    offset=24;sections=[]
    for n in sizes:sections.append(data[offset:offset+n]);offset+=n
    return sections
