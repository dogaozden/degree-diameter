"""Card c3 (squad round 6): fast orbit compatibility rows through compat6.so (same output as orbl.compat_packed)."""
import ctypes
import os

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
import orbl as L  # noqa: E402

_lib = ctypes.CDLL(os.path.join(HERE, 'libcompat6.so'))
_lib.compat_bits.restype = None
_lib.compat_bits.argtypes = [ctypes.c_int, ctypes.c_int, ctypes.c_void_p, ctypes.c_void_p, ctypes.c_void_p,
                             ctypes.c_void_p]


def compat_rows(lab, rep, good):
    K = int(good.size)
    ncomp = rep.size
    pos = np.full(ncomp, -1, np.int64)
    pos[good] = np.arange(K)
    pts = np.flatnonzero(pos[lab] >= 0)
    pl = pos[lab[pts]]
    o = np.argsort(pl, kind='stable')
    pts = pts[o]
    pl = pl[o]
    starts = np.searchsorted(pl, np.arange(K + 1)).astype(np.int64)
    starts[K] = pl.size
    PJs = np.ascontiguousarray(L.PJ[pts].astype(np.uint8))           # (npts, 7), values 0..10
    RT = np.ascontiguousarray(L.P[rep[good]].T.astype(np.uint8))     # (7, K)
    W = (K + 63) // 64
    out = np.zeros((K, W), np.uint64)
    _lib.compat_bits(K, W, starts.ctypes.data, PJs.ctypes.data, RT.ctypes.data, out.ctypes.data)
    return out
