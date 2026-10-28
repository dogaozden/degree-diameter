"""Card c6: q = 7 level graph, all levels type H, rotational tournament j -> j+1, j+2, j+3 (mod 7), no hubs."""
import ctypes, os, sys, numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d5gq')
import gqlib
_lib = ctypes.CDLL(os.path.join(HERE, 'bad7.so'))
_lib.allbad.restype = ctypes.c_long
_lib.allbad.argtypes = [ctypes.c_int, ctypes.c_int, ctypes.c_void_p, ctypes.c_void_p, ctypes.c_int, ctypes.c_void_p, ctypes.c_int]

L = 7; R_ = 3; D = 5

class Net:
    def __init__(self, G):
        self.G = G; self.np = G.np; self.nl = G.nl; self.per = G.np + G.nl
        self.n = L * self.per
        eu, ev = [], []
        for j in range(L):
            for l, pts in enumerate(G.lines):
                for p in pts:
                    eu.append(j * self.per + p); ev.append(j * self.per + G.np + l)
        self.iu = np.array(eu, np.int32); self.iv = np.array(ev, np.int32)
        self.arcs = [(j, (j + k) % L) for j in range(L) for k in range(1, R_ + 1)]

    def edges(self, M, R):
        """M: dict arc -> array over points (line index of target level); R: dict arc -> set of freed points."""
        us = [self.iu]; vs = [self.iv]
        for (j, j2) in self.arcs:
            Mt = M[(j, j2)]
            keep = np.ones(self.np, bool)
            Rt = R.get((j, j2))
            if Rt is not None and len(Rt): keep[list(Rt)] = False
            a = np.nonzero(keep)[0]
            us.append(j * self.per + a); vs.append(j2 * self.per + self.np + Mt[a])
        return np.concatenate(us).astype(np.int32), np.concatenate(vs).astype(np.int32)

    def bad_pairs(self, M, R, maxpairs=200000):
        eu, ev = self.edges(M, R)
        buf = np.zeros(2 * maxpairs, np.int32)
        tot = _lib.allbad(self.n, len(eu), eu.ctypes.data, ev.ctypes.data, D, buf.ctypes.data, maxpairs)
        k = min(tot, maxpairs)
        return tot, buf[:2 * k].reshape(-1, 2)

    def bad(self, M, R):
        eu, ev = self.edges(M, R)
        return _lib.allbad(self.n, len(eu), eu.ctypes.data, ev.ctypes.data, D, None, 0)

def write_edges(path, n, eu, ev):
    with open(path, 'w') as f:
        f.write('%d\n' % n)
        f.write(''.join('%d %d\n' % (a, b) for a, b in zip(eu.tolist(), ev.tolist())))
