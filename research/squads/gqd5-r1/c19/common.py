"""Shared helpers for card c19: whole-graph level graph (no hubs), bad-pair counting in C."""
import ctypes, os, sys
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d5gq')
import gqlib, repair
_lib = ctypes.CDLL(os.path.join(HERE, 'libbad.so'))
_lib.count_bad_bits.restype = ctypes.c_long
_lib.count_bad_bits.argtypes = [ctypes.c_int, ctypes.c_int, ctypes.c_void_p, ctypes.c_void_p, ctypes.c_int, ctypes.c_void_p]
_lib.count_bad.restype = ctypes.c_long
_lib.count_bad.argtypes = [ctypes.c_int, ctypes.c_int, ctypes.c_void_p, ctypes.c_void_p, ctypes.c_int, ctypes.c_void_p]

def count_bad(n, eu, ev, D=5, per=False):
    eu = np.ascontiguousarray(eu, dtype=np.int32); ev = np.ascontiguousarray(ev, dtype=np.int32)
    pv = np.zeros(n, dtype=np.int64) if per else None
    b = _lib.count_bad_bits(n, len(eu), eu.ctypes.data, ev.ctypes.data, D, pv.ctypes.data if per else None)
    return (b, pv) if per else b

class Graph:
    """all-H level graph over G with L = 2r+1 levels; transitions (j,k), k=1..r, M[(j,k)] = array over points -> line ids."""
    def __init__(self, G, r):
        self.G = G; self.r = r; self.L = 2 * r + 1
        self.np = G.np; self.nl = G.nl; self.per = G.np + G.nl
        self.n = self.L * self.per
        eu, ev = [], []
        for j in range(self.L):
            for l, pts in enumerate(G.lines):
                for p in pts:
                    eu.append(j * self.per + p); ev.append(j * self.per + G.np + l)
        self.inner_u = np.array(eu, dtype=np.int32); self.inner_v = np.array(ev, dtype=np.int32)
        self.trans = [(j, k) for j in range(self.L) for k in range(1, r + 1)]

    def edges(self, M, R):
        """M: dict (j,k) -> array (points -> line ids); R: dict (j,k) -> set of freed points"""
        us = [self.inner_u]; vs = [self.inner_v]
        for (j, k) in self.trans:
            Mt = np.asarray(M[(j, k)]); Rt = R.get((j, k), ())
            keep = np.ones(self.np, dtype=bool)
            if len(Rt): keep[list(Rt)] = False
            a = np.nonzero(keep)[0]
            us.append(j * self.per + a)
            vs.append(((j + k) % self.L) * self.per + self.np + Mt[a])
        return np.concatenate(us).astype(np.int32), np.concatenate(vs).astype(np.int32)

    def bad(self, M, R, D=5, per=False):
        eu, ev = self.edges(M, R)
        return count_bad(self.n, eu, ev, D, per)

def write_edges(path, n, eu, ev):
    with open(path, 'w') as f:
        f.write('%d\n' % n)
        f.write(''.join('%d %d\n' % (a, b) for a, b in zip(eu, ev)))
