"""c4 (squad round 3): crossover helpers for pairwise-opposite point sets of H(11).

Points: index in research/d13D7/hex/hex_q11.bin, 7 coordinates (x0..x6).  B(x,y) = x0y4+x4y0+x1y5+x5y1+x2y6+x6y2-2x3y3 mod 11;
x, y opposite iff B != 0.  For a fixed y, B(x,y) = x . w(y) with w(y) = (y4, y5, y6, -2y3, y0, y1, y2) mod 11.

union_max(P, Q): the largest pairwise-opposite subset of P u Q, EXACT.  P and Q are pairwise opposite, so every conflict
joins P\\Q to Q\\P (points in P n Q have no conflicts).  The conflict graph is bipartite, so by Konig's theorem a maximum
independent set = |P u Q| - (maximum matching), and it is read off the alternating-path cover of a maximum matching.
Random tie-breaking gives different maximum sets (diversity).

fill(S): greedy extension of S by points opposite to all of S (min-conflict rule inside the candidate set), so the result
is maximal in the whole hexagon (LNS only frees points that are blocked, so the start must be maximal).
"""
import sys, random
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/d13D7/tools')
import hexlib

HEX = '/home/user/degree-diameter/research/d13D7/hex/hex_q11.bin'
_q, _lines, coord = hexlib.load(HEX)
coord = np.asarray(coord, dtype=np.int64)
N = coord.shape[0]

def wmat(idx):
    c = coord[np.asarray(idx, dtype=np.int64)]
    w = np.stack([c[:, 4], c[:, 5], c[:, 6], (-2 * c[:, 3]) % 11, c[:, 0], c[:, 1], c[:, 2]], axis=1)
    return w % 11

def read_set(path):
    out = []
    with open(path) as f:
        for line in f:
            s = line.strip()
            if not s or s.startswith('#'):
                continue
            out.append(int(s))
    return out

def write_set(path, S, tag=''):
    with open(path, 'w') as f:
        f.write('# %s: %d points, pairwise opposite\n' % (tag, len(S)))
        for x in S:
            f.write('%d\n' % x)

def conflicts_row(x):
    """boolean vector over all points: True where B(point, x) == 0 (includes x itself)."""
    w = wmat([x])[0]
    return (coord @ w) % 11 == 0

def union_max(P, Q, rng):
    P = sorted(set(P)); Q = sorted(set(Q))
    Ps, Qs = set(P), set(Q)
    common = sorted(Ps & Qs)
    L = sorted(Ps - Qs); R = sorted(Qs - Ps)
    nl, nr = len(L), len(R)
    if nl and nr:
        M = ((coord[L] @ wmat(R).T) % 11 == 0)          # M[i, j]: L[i] and R[j] conflict
    else:
        M = np.zeros((nl, nr), dtype=bool)
    adj = [list(np.nonzero(M[i])[0]) for i in range(nl)]
    for a in adj: rng.shuffle(a)
    matchL = [-1] * nl; matchR = [-1] * nr
    sys.setrecursionlimit(10000)
    def aug(u, seen):
        for v in adj[u]:
            if not seen[v]:
                seen[v] = True
                if matchR[v] == -1 or aug(matchR[v], seen):
                    matchL[u] = v; matchR[v] = u
                    return True
        return False
    order = list(range(nl)); rng.shuffle(order)
    for u in order:
        if matchL[u] == -1:
            aug(u, [False] * nr)
    nu = sum(1 for u in range(nl) if matchL[u] != -1)
    # Konig: alternating BFS from unmatched left vertices
    visL = [False] * nl; visR = [False] * nr
    stack = [u for u in range(nl) if matchL[u] == -1]
    for u in stack: visL[u] = True
    while stack:
        u = stack.pop()
        for v in adj[u]:
            if not visR[v]:
                visR[v] = True
                w = matchR[v]
                if w != -1 and not visL[w]:
                    visL[w] = True; stack.append(w)
    IL = [L[i] for i in range(nl) if visL[i]]
    IR = [R[j] for j in range(nr) if not visR[j]]
    S = common + IL + IR
    assert len(S) == len(common) + nl + nr - nu, 'Konig bookkeeping'
    return S

def fill(S, rng, conf=None):
    """greedy maximal extension of S (list of point indices, pairwise opposite)."""
    S = list(S)
    inS = np.zeros(N, dtype=bool); inS[S] = True
    if conf is None:
        conf = np.zeros(N, dtype=np.int32)
        for s in S:
            conf += conflicts_row(s)
    added = []
    while True:
        cand = np.nonzero((~inS) & (conf == 0))[0]
        if len(cand) == 0:
            break
        if len(cand) > 1:
            Mc = (coord[cand] @ wmat(cand).T) % 11 == 0      # conflicts inside the candidate set
            deg = Mc.sum(axis=1) - 1                          # minus self-conflict
            noise = np.array([rng.random() for _ in cand]) * 0.5
            x = int(cand[int(np.argmin(deg + noise))])
        else:
            x = int(cand[0])
        S.append(x); added.append(x); inS[x] = True
        conf += conflicts_row(x)
    return S, added

def opposite_to_all(points, S):
    """boolean array: point (index) has no conflict with any element of S (ignores itself)."""
    if len(S) == 0:
        return np.ones(len(points), dtype=bool)
    W = wmat(S)                                            # |S| x 7
    C = coord[np.asarray(points, dtype=np.int64)]          # |points| x 7
    G = (C @ W.T) % 11 == 0                                # conflicts
    return ~G.any(axis=1)
