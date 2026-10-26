"""Card c6: bad-pair counts before annealing, two-level (levels 0,1 with arc (0,1) only) vs whole graph.
Also classifies whole-graph bad pairs by endpoint type (is an endpoint of a deleted edge involved?)."""
import sys, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/gqd5-r2/c6')
from common7 import *
import gqlib
G = gqlib.Q4(7); net = Net(G); NP, PER = G.np, G.np + G.nl
def two_level(Mt, Rt):
    """unordered pairs at distance > 5 in the subgraph of levels 0 and 1 with arc (0,1) only:
    (tot = all such pairs, cross = those with one end in level 0 and one in level 1)"""
    from common7 import _lib
    keep = np.ones(NP, bool); keep[list(Rt)] = False; a = np.nonzero(keep)[0]
    iu, iv = [], []
    for j in (0, 1):
        for l, pts in enumerate(G.lines):
            for p in pts: iu.append(j * PER + p); iv.append(j * PER + NP + l)
    iu = np.array(iu + a.tolist(), np.int32)
    iv = np.array(iv + (PER + NP + Mt[a]).tolist(), np.int32)
    n2 = 2 * PER
    tot = _lib.allbad(n2, len(iu), iu.ctypes.data, iv.ctypes.data, 5, None, 0)
    maxp = 200000
    pb = np.zeros(2 * maxp, np.int32)
    k = _lib.allbad(n2, len(iu), iu.ctypes.data, iv.ctypes.data, 5, pb.ctypes.data, maxp)
    pr = pb[:2 * min(k, maxp)].reshape(-1, 2)
    cross = int(((pr[:, 0] < PER) & (pr[:, 1] >= PER)).sum())
    return int(tot), cross
rows = []
for narcs, s in [(1, 16), (1, 32), (1, 64), (2, 16), (4, 16)]:
    FREE = {1: [(0, 1)], 2: [(0, 1), (2, 3)], 4: [(0, 1), (2, 3), (4, 5), (6, 0)]}[narcs]
    for seed in (1, 2, 3):
        rng = np.random.default_rng(seed)
        M = {a: rng.permutation(NP) for a in net.arcs}
        R = {a: set(rng.choice(NP, s, replace=False).tolist()) for a in FREE}
        whole, pairs = net.bad_pairs(M, R)
        whole = int(whole)
        ep = set()
        for a in FREE:
            for x in R[a]:
                ep.add(a[0] * PER + x); ep.add(a[1] * PER + NP + int(M[a][x]))
        endpt = sum(1 for x, v in pairs if (int(x) in ep or int(v) in ep))
        tl = two_level(M[(0, 1)], R[(0, 1)])
        print('arcs=%d s=%d seed=%d: whole(unordered)=%d  endpoint-involved=%d  two-level(all)=%d  two-level(cross 0-1)=%d'
              % (narcs, s, seed, whole, endpt, tl[0], tl[1]), flush=True)
