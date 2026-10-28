"""c16 (squad gqd5-r1): explicit partial ovoids of W(q), q odd.

W(q): points of PG(3,q), x ~ y (collinear) iff w(x,y) = x0*y2 + x1*y3 - x2*y0 - x3*y1 = 0.
A partial ovoid is a set of pairwise non-collinear points; gqlib.is_partial_ovoid checks this.

Printed:
 1. FAMILY L (size q+1): {(0,1,0,0), (0,0,0,1)} u {(1,t,0,t^2) : t in F_q^*}.  Valid for every odd q (proof in family.md).
 2. Cone family: points (1,a,b,a^2) (a,b in F_q) on the cone x0*x3 = x1^2; tabu search for the largest
    pairwise non-collinear subset (heuristic, not proved optimal).
Each set is verified with gqlib.is_partial_ovoid on gqlib.W(q) (q <= 11), and with an independent numpy check
of w for every q.
"""
import sys, os, time
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d5gq')
import gqlib
from gqlib import GF, _norm, is_partial_ovoid


def w_form(F, x, y):
    a = F.add[F.mul[x[0]][y[2]]][F.mul[x[1]][y[3]]]
    b = F.add[F.mul[x[2]][y[0]]][F.mul[x[3]][y[1]]]
    return F.sub[a][b]


def numpy_check(F, pts):
    """independent check: all pairs of distinct listed points have w != 0 (pure field-table arithmetic)"""
    for i in range(len(pts)):
        for j in range(i + 1, len(pts)):
            if w_form(F, pts[i], pts[j]) == 0:
                return False
    return True


def family_L(q):
    F = GF(q)
    pts = [(0, 1, 0, 0), (0, 0, 0, 1)]
    for t in range(1, q):
        pts.append((1, t, 0, F.mul[t][t]))
    return [_norm(F, p) for p in pts]


def cone_candidates(q):
    F = GF(q)
    return [(1, a, b, F.mul[a][a]) for a in range(q) for b in range(q)]


def mis_tabu(adj, iters=8000, seed=0):
    """max independent set (pairwise non-collinear) by k-fixed min-conflict tabu search; adj = collinearity"""
    rng = np.random.default_rng(seed)
    n = adj.shape[0]
    adjI = adj.astype(np.int32)
    S = np.zeros(n, bool); conf = np.zeros(n, np.int32)
    for v in rng.permutation(n):
        if conf[v] == 0:
            S[v] = True; conf += adjI[v]
    best = np.nonzero(S)[0]
    tabu_in = np.zeros(n, np.int64); tabu_out = np.zeros(n, np.int64)
    it = 0
    while it < iters:
        cand_add = np.where(~S)[0]
        if len(cand_add) == 0:
            break
        v = cand_add[np.argmin(conf[cand_add] + rng.random(len(cand_add)) * 0.5)]
        S[v] = True; conf += adjI[v]
        while it < iters:
            it += 1
            Sidx = np.nonzero(S)[0]
            if int(conf[Sidx].sum()) == 0:
                if len(Sidx) > len(best):
                    best = Sidx.copy()
                break
            ok = tabu_out[Sidx] <= it
            score = np.where(ok, conf[Sidx] + rng.random(len(Sidx)) * 0.5, -1.0)
            u = Sidx[np.argmax(score)]
            cost = conf - adjI[u]
            okv = (~S) & (tabu_in <= it)
            if not okv.any():
                okv = ~S
            v = int(np.argmin(np.where(okv, cost + rng.random(n) * 0.5, 1e9)))
            S[u] = False; conf -= adjI[u]
            S[v] = True; conf += adjI[v]
            tabu_in[u] = it + 7 + rng.integers(0, 5)
            tabu_out[v] = it + 3 + rng.integers(0, 3)
    return best


def tabu_subset(F, cands, seeds=3, iters=20000):
    """best pairwise non-collinear subset of cands found by tabu search (heuristic)"""
    n = len(cands)
    adj = np.zeros((n, n), dtype=bool)
    for i in range(n):
        for j in range(n):
            if i != j and w_form(F, cands[i], cands[j]) == 0:
                adj[i, j] = True
    best = max((mis_tabu(adj, iters=iters, seed=s) for s in range(seeds)), key=len)
    return [cands[i] for i in best]


def gq_verify(q, pts):
    G = gqlib.W(q)
    idx = {tuple(c): i for i, c in enumerate(G.coords)}
    S = [idx[tuple(p)] for p in pts]
    return is_partial_ovoid(G, S)


if __name__ == '__main__':
    qs = [int(x) for x in sys.argv[1:]] or [3, 5, 7, 9, 11, 13]
    for q in qs:
        t0 = time.time()
        F = GF(q)
        L = family_L(q)
        ok_np = numpy_check(F, L) and len(set(L)) == len(L)
        line = 'q=%2d  family L size=%d  numpy-valid=%s' % (q, len(L), ok_np)
        if q <= 11:
            line += '  gqlib-valid=%s' % gq_verify(q, L)
        print(line, flush=True)
        cand = cone_candidates(q)
        C = tabu_subset(F, cand, seeds=2, iters=8000)
        okc = numpy_check(F, C)
        line2 = 'q=%2d  cone (1,a,b,a^2) tabu subset size=%d  numpy-valid=%s' % (q, len(C), okc)
        if q <= 11:
            line2 += '  gqlib-valid=%s' % gq_verify(q, C)
        print(line2, '  (%.1fs)' % (time.time() - t0), flush=True)
