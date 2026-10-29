import numpy as np

def tabu_indep(C, verts, s, iters, rng, init=None):
    """Find s vertices from verts with no conflicting pair (C: bool conflict matrix over verts). Returns list or None."""
    n = len(verts)
    if s > n: return None
    Cs = C
    inS = np.zeros(n, bool)
    if init is None:
        S = list(rng.choice(n, s, replace=False))
    else:
        S = list(init)
    inS[S] = True
    cnt = Cs[S].sum(0).astype(np.int32)
    tabu = np.zeros(n, np.int64)
    best = None
    for it in range(iters):
        Sarr = np.array(S)
        confl = cnt[Sarr]
        bad = Sarr[confl > 0]
        if len(bad) == 0:
            return [int(verts[i]) for i in S]
        u = bad[rng.integers(len(bad))]
        # pick v not in S, not tabu, minimizing cnt[v] - C[u,v]
        score = cnt.astype(np.float64) - Cs[u].astype(np.float64) + rng.random(n) * 0.5
        score[inS] = np.inf
        score[tabu > it] = np.inf
        v = int(np.argmin(score))
        # swap u -> v
        k = S.index(u)
        S[k] = v
        inS[u] = False; inS[v] = True
        cnt -= Cs[u].astype(np.int32); cnt += Cs[v].astype(np.int32)
        tabu[u] = it + 7 + rng.integers(10)
    return None

def max_indep(C, verts, s_start, iters, rng, log=None):
    """Increase s until tabu fails. Returns best set found."""
    best = None; s = s_start
    while True:
        r = tabu_indep(C, verts, s, iters, rng, init=None if best is None else [i for i in range(len(verts)) if False] or None)
        if r is None: break
        best = r; s += 1
        if log: log(s - 1)
    return best
