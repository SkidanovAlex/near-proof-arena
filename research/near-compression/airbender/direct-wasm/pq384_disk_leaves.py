"""Prover-only lane-at-a-time leaf transpose from existing coefficient files.

This does not prove coefficient correctness or eliminate upstream witness
materialization. Explicit memory is one lane FFT plus a bounded leaf tile.
"""
from array import array
from pathlib import Path
import struct,sys
from pq384_primitives import P,require
from pq384_native_fft import MAX_DOMAIN


def build_disk_leaves(coefficients_path,leaves_path,*,degree,lanes,native,tile_leaves=1024):
    require(type(degree)is int and degree>=1 and degree&(degree-1)==0 and 4*degree<=MAX_DOMAIN,'degree')
    require(type(lanes)is int and lanes>=1,'lanes')
    require(type(tile_leaves)is int and tile_leaves>=1,'tile size')
    half=2*degree;stride=lanes*8
    with Path(coefficients_path).open('rb') as coefficients:
        require(coefficients.seek(0,2)==degree*lanes*4,'coefficient file size');coefficients.seek(0)
        with Path(leaves_path).open('x+b') as leaves:
            leaves.truncate(half*stride)
            for lane in range(lanes):
                words=array('I');require(words.itemsize==4,'u32 array width')
                words.frombytes(coefficients.read(degree*4))
                if sys.byteorder!='little':words.byteswap()
                require(len(words)==degree and all(v<P for v in words),'canonical coefficients')
                ext=array('I',[0])*(4*degree)
                ext[::4]=words
                del words
                values=native.lde4_words(ext)
                del ext
                for start in range(0,half,tile_leaves):
                    count=min(tile_leaves,half-start)
                    leaves.seek(start*stride);tile=bytearray(leaves.read(count*stride))
                    require(len(tile)==count*stride,'leaf tile size')
                    for j in range(count):
                        i=start+j
                        struct.pack_into('<II',tile,j*stride+8*lane,values[4*i],values[4*(i+half)])
                    leaves.seek(start*stride);leaves.write(tile)
                del values
            leaves.flush()
