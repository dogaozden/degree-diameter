"""orbset.py: full-candidate orbit-level greedy (min-degree set packing) for disjoint totally singular lines.

Setting as tsgreedy.py: T = <h> semiregular on points, M = N/|T| point orbits. A totally singular line L has the
orbit-set O(L) = {orbits of its q+1 points} (q+1 distinct orbits needed). If O(L) and O(L') are disjoint, the
T-images of L and L' are disjoint; a family R with pairwise disjoint orbit-sets gives |T||R| disjoint lines.
Candidates: every line through a representative point of each orbit (every orbit-set of a line occurs this way,
since a line through p is moved to a line through rep(orbit of p) by some g in T); one candidate per distinct
orbit-set. Selection: repeatedly take the candidate whose orbits have the smallest total degree (number of
remaining candidates through each orbit), with random tie-breaking; remove all candidates meeting it.
Writes OUT.i32 (expanded lines, int32 point ids) and OUT.R.i32 (representative lines).
Usage: timeout W nice -n 10 python3 orbset.py HEXBIN SEED RESTARTS OUT PPERM [PPERM ...]
"""
import sys, time
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/polylev/r2/e15')
from tsgreedy import Ctx, orbits


def candidates(C, orb, M):
    q, N, X = C.q, C.N, C.X
    lam = np.arange(1, q, dtype=np.int64)
    _, rep = np.unique(orb, return_index=True)          # rep[O] = a point of orbit O
    rows_orb, rows_ids = [], []
    t0 = time.time()
    for n, p in enumerate(rep):
        b = C.bform_all(X[p])
        xs = np.flatnonzero(b == 0)
        xs = xs[xs != p]
        Xs = X[xs]
        P = C.ADD[X[p][None, None, :], C.MUL[lam[None, :, None], Xs[:, None, :]]]
        pP = C.ids(P.reshape(-1, 7)).reshape(len(xs), q - 1)
        keep = xs < pP.min(axis=1)           # keep the line once, via its smallest non-p point
        L = np.concatenate([np.full((keep.sum(), 1), p), xs[keep][:, None], pP[keep]], axis=1)
        O = orb[L]
        ok = (np.diff(np.sort(O, axis=1), axis=1) != 0).all(axis=1)
        rows_orb.append(np.sort(O[ok], axis=1).astype(np.int32))
        rows_ids.append(L[ok].astype(np.int32))
    print(f'candidates enumerated from {len(rep)} reps in {time.time() - t0:.1f}s', flush=True)
    A = np.concatenate(rows_orb)
    I = np.concatenate(rows_ids)
    U, first = np.unique(A, axis=0, return_index=True)
    print(f'{len(A)} lines through reps with distinct orbits, {len(U)} distinct orbit-sets', flush=True)
    return U, I[first]


def mindeg(S, M, rng):
    K = len(S)
    alive = np.ones(K, dtype=bool)
    chosen = []
    while alive.any():
        A = S[alive]
        deg = np.bincount(A.ravel(), minlength=M).astype(np.float64)
        cost = deg[S].sum(axis=1) + rng.random(K) * 0.5
        cost[~alive] = np.inf
        j = int(np.argmin(cost))
        chosen.append(j)
        hit = np.isin(S, S[j]).any(axis=1)
        alive &= ~hit
    return chosen


def main():
    hexpath, seed, restarts, out = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
    perms = [np.fromfile(f, dtype=np.int32).astype(np.int64) for f in sys.argv[5:]]
    C = Ctx(hexpath)
    h = perms[0]
    for P in perms[1:]:
        h = h[P]
    orb, M, sizes = orbits(h)
    assert len(sizes) == 1
    m = sizes.pop()
    print(f'q={C.q} |T|={m} orbits={M} bound |R| <= {M // (C.q + 1)}', flush=True)
    S, I = candidates(C, orb, M)
    best = None
    for r in range(restarts):
        rng = np.random.default_rng(seed * 1000 + r)
        ch = mindeg(S, M, rng)
        if best is None or len(ch) > len(best):
            best = ch
            print(f'restart {r}: |R|={len(ch)} lines={len(ch) * m}', flush=True)
    R = I[best].astype(np.int64)
    R.astype(np.int32).tofile(out + '.R.i32')
    allL, cur = [], R.copy()
    for k in range(m):
        allL.append(cur)
        cur = h[cur]
    E = np.concatenate(allL, axis=0)
    E.astype(np.int32).tofile(out + '.i32')
    print(f'final |R|={len(R)}, lines={len(E)}, covered orbits {len(R) * (C.q + 1)}/{M}', flush=True)


if __name__ == '__main__':
    main()
