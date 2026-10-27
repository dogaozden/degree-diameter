import numpy as np, random
def greedy_ls(w, compat, iters=300, seed=1, tl_iters=None):
    """randomised greedy by weight*noise + (1,1)-swap local search on a boolean compat matrix. returns (weight, verts)"""
    rng = np.random.default_rng(seed)
    w = np.asarray(w, dtype=np.float64); K = len(w)
    nc = ~compat; np.fill_diagonal(nc, True)
    best = (-1, [])
    for it in range(iters):
        key = w * (0.6 + 0.8 * rng.random(K))
        order = np.argsort(-key)
        cand = np.ones(K, dtype=bool); S = []
        for v in order:
            if cand[v]:
                S.append(int(v)); cand &= compat[v]; cand[v] = False
        # swap local search: find v outside with exactly one conflict u in S and w[v] > w[u]
        improved = True; rounds = 0
        while improved and rounds < 200:
            improved = False; rounds += 1
            inS = np.zeros(K, dtype=bool); inS[S] = True
            conf = nc[:, S].sum(1)
            conf[inS] = 0
            for v in np.nonzero((~inS) & (conf == 1))[0]:
                # find conflicting member
                u = [x for x in S if nc[v, x]][0]
                if w[v] > w[u]:
                    S.remove(u); S.append(int(v)); improved = True
                    # greedily add anything free
                    cand = np.ones(K, dtype=bool)
                    for x in S: cand &= compat[x]
                    cand[S] = False
                    for x in np.nonzero(cand)[0]:
                        if all(compat[x, y] for y in S):
                            S.append(int(x))
                    break
        tw = float(w[S].sum())
        if tw > best[0]:
            best = (tw, list(S))
    return best
