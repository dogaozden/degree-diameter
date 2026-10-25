"""c1 helpers: flag data (distance arrays, membership sets), fast mismatch, GF(8) coordinates, Frobenius."""
import sys, os, struct
import numpy as np
TOOLS = '/home/user/degree-diameter/research/squads/d10D7-r3/tools'
sys.path.insert(0, TOOLS)
from hexkit import Hex, HEXDIR

H = Hex(8)
N = H.N
assert H.LP.shape[0] == N


def load_coords():
    with open(os.path.join(HEXDIR, 'hex_q8.bin'), 'rb') as f:
        qq, NN, LL = struct.unpack('3i', f.read(12))
        f.seek(12 + 4 * LL * (qq + 1))
        return np.frombuffer(f.read(NN * 7), dtype=np.uint8).reshape(NN, 7).copy()


def dist(x, isline):
    H._cache.clear()
    d = H.bfs(x, isline)
    H._cache.clear()
    return d


class FD:
    """flag (p, l): distances from p and from l (uint8, length 2N) and membership sets."""
    def __init__(self, p, l):
        self.p = int(p); self.l = int(l)
        dp = dist(self.p, False); dl = dist(self.l, True)
        self.dp = dp.astype(np.uint8); self.dl = dl.astype(np.uint8)
        self.Sp = (dp[:N] == 4) & (dl[:N] == 5)     # points u: d(p,u)=4, d(l,u)=5
        self.Sl = (dl[N:] == 4) & (dp[N:] == 5)     # lines L: d(l,L)=4, d(p,L)=5


def opp(f, g):
    """flags f, g pairwise opposite (same convention as hexkit.opposite)."""
    return bool(f.dp[g.p] == 6 and f.dl[N + g.l] == 6 and f.dp[N + g.l] == 5 and f.dl[g.p] == 5)


def mismatch(fds):
    """sum over membership vectors |#points(v) - #lines(v)| over nonfreed points/lines (same as hexkit.mismatch)."""
    K = len(fds)
    cp = np.zeros(N, np.int64); cl = np.zeros(N, np.int64)
    fp = np.zeros(N, bool); fl = np.zeros(N, bool)
    for k, f in enumerate(fds):
        cp |= f.Sp.astype(np.int64) << k
        cl |= f.Sl.astype(np.int64) << k
        fp[f.p] = True; fl[f.l] = True
    cntP = np.bincount(cp[~fp], minlength=1 << K)
    cntL = np.bincount(cl[~fl], minlength=1 << K)
    return int(np.abs(cntP - cntL).sum())


def atoms(fds):
    K = len(fds)
    cp = np.zeros(N, np.int64); cl = np.zeros(N, np.int64)
    fp = np.zeros(N, bool); fl = np.zeros(N, bool)
    for k, f in enumerate(fds):
        cp |= f.Sp.astype(np.int64) << k
        cl |= f.Sl.astype(np.int64) << k
        fp[f.p] = True; fl[f.l] = True
    cntP = np.bincount(cp[~fp], minlength=1 << K)
    cntL = np.bincount(cl[~fl], minlength=1 << K)
    return cntP, cntL


def cliques(adj, n, k):
    """all k-cliques of graph with python-int bitmask adjacency (increasing index order)."""
    out = []
    def rec(cur, cand, depth):
        if depth == k:
            out.append(tuple(cur)); return
        c = cand
        while c:
            v = (c & -c).bit_length() - 1
            c &= c - 1
            rec(cur + [v], c & adj[v], depth + 1)
    rec([], (1 << n) - 1, 0)
    return out


# GF(8): elements 0..7 encode a0 + 2 a1 + 4 a2 in basis 1, x, x^2 with x^3 = x + 1
def gf8_mul(a, b):
    r = 0
    for i in range(3):
        if (b >> i) & 1:
            r ^= a << i
    for i in (4, 3):
        if (r >> i) & 1:
            r ^= 0b1011 << (i - 3)   # x^3 + x + 1 (x^3 = x + 1)
    return r

SQ = np.array([gf8_mul(v, v) for v in range(8)], dtype=np.uint8)
