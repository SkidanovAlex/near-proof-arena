"""Optional untrusted native prover FFT. Explicit library path; no auto-build.

rustc --edition=2021 --crate-type cdylib -O pq384_native_fft.rs -o /tmp/libpq384_fft.so
Flat array('I') API avoids per-element Python objects at large heights.
"""
import ctypes
from array import array

P = 2013265921
MAX_DOMAIN = 1 << 22

class NativeFFT:
    def __init__(self, library):
        self.lib = ctypes.CDLL(str(library))
        self.lib.pq384_fft.argtypes = [ctypes.POINTER(ctypes.c_uint32), ctypes.c_size_t,
                                     ctypes.POINTER(ctypes.c_uint32), ctypes.c_size_t,
                                     ctypes.c_size_t]
        self.lib.pq384_fft.restype = ctypes.c_int

    def fft_words(self, words, *, lde4=False):
        if not isinstance(words, array) or words.typecode != 'I' or words.itemsize != 4:
            raise ValueError("expected native uint32 array('I')")
        if not len(words) or len(words) % 4:
            raise ValueError('Ext4 word count')
        n = len(words) // 4
        domain = n * (4 if lde4 else 1)
        if domain > MAX_DOMAIN or domain & (domain-1):
            raise ValueError('FFT domain')
        out = array('I', [0]) * (4*domain)
        src = (ctypes.c_uint32 * len(words)).from_buffer(words)
        dst = (ctypes.c_uint32 * len(out)).from_buffer(out)
        status = self.lib.pq384_fft(src, len(words), dst, len(out), domain)
        if status:
            raise ValueError(f'native FFT rejected input: status {status}')
        return out

    def lde4_words(self, words):
        return self.fft_words(words, lde4=True)

    def fft(self, coefficients, *, lde4=False):
        words = array('I')
        for c in coefficients:
            if len(c) != 4 or any(type(v) is not int or not 0 <= v < P for v in c):
                raise ValueError('canonical Ext4 coefficient')
            words.extend(c)
        out = self.fft_words(words, lde4=lde4)
        return [tuple(out[i:i+4]) for i in range(0,len(out),4)]

    @staticmethod
    def _buffer(words):
        if not isinstance(words,array) or words.typecode != 'I' or words.itemsize != 4:
            raise ValueError("expected native uint32 array('I')")
        return (ctypes.c_uint32 * len(words)).from_buffer(words)

    def fold_words(self, words, challenge):
        if len(words)==0 or len(words)%8 or len(words)>4*MAX_DOMAIN:
            raise ValueError('fold shape')
        if len(challenge)!=4 or any(type(v) is not int or not 0<=v<P for v in challenge):
            raise ValueError('canonical challenge')
        src=self._buffer(words)
        out=array('I',[0])*(len(words)//2);dst=self._buffer(out)
        fn=self.lib.pq384_affine_fold
        fn.argtypes=[ctypes.POINTER(ctypes.c_uint32),ctypes.c_size_t,
                     ctypes.POINTER(ctypes.c_uint32),ctypes.c_size_t]+[ctypes.c_uint32]*4
        fn.restype=ctypes.c_int
        status=fn(src,len(words),dst,len(out),*challenge)
        if status:raise ValueError(f'native fold rejected input: status {status}')
        return out

    def quadratic_words(self, words, weights):
        if len(words)!=len(weights) or not len(words) or len(words)%8 or len(words)>4*MAX_DOMAIN:
            raise ValueError('quadratic shape')
        src=self._buffer(words);w=self._buffer(weights)
        out=array('I',[0])*12;dst=self._buffer(out)
        fn=self.lib.pq384_quadratic_dot
        fn.argtypes=[ctypes.POINTER(ctypes.c_uint32)]*2+[ctypes.c_size_t,
                     ctypes.POINTER(ctypes.c_uint32),ctypes.c_size_t]
        fn.restype=ctypes.c_int
        status=fn(src,w,len(words),dst,12)
        if status:raise ValueError(f'native quadratic rejected input: status {status}')
        return [tuple(out[i:i+4]) for i in range(0,12,4)]
