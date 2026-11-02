# w08: bi-coset (H-K double coset) graphs. Side A: left cosets Hx; side B: left cosets Ky (K=H here).
# Hx ~ Ky iff x y^-1 in H S K, S = union of H-K double cosets. Vertices 2|G|/|H|, degree = sum of |HsH|/|H|.
# Diameter = max(ecc(A0), ecc(B0)) (G acts transitively on each side by right multiplication).
import sys, itertools, time
sys.path.insert(0, '/home/user/degree-diameter/research/squads/beyond11b/tools')
import numpy as np
from groups import table

def run(spec, n, Delta, D, h_order=2, out=None, maxcand=10**9):
    T = table(spec).astype(np.int64)
    N = T.shape[0]
    assert N == n, (spec, N, n)
    inv = np.argmax(T == 0, axis=1)
    invs = [t for t in range(1, N) if T[t, t] == 0]
    # conjugacy classes of involutions
    seen = set(); reps = []
    for t in invs:
        if t in seen: continue
        cls = set(int(T[T[g, t], inv[g]]) for g in range(N))
        seen |= cls; reps.append(t)
    best = None; hits = []; cnt = 0; regular = 0
    print("  classes", len(reps), "m", N // 2, flush=True)
    for t in reps:
        H = [0, t]
        # left cosets of H: id per element
        cid = -np.ones(N, dtype=np.int64); R = []
        for x in range(N):
            if cid[x] < 0:
                for h in H:
                    cid[int(T[h, x])] = len(R)
                R.append(x)
        m = len(R)
        R = np.array(R)
        # double cosets H s H
        dc = -np.ones(N, dtype=np.int64); dcs = []
        for s in range(N):
            if dc[s] < 0:
                el = set(int(T[T[h1, s], h2]) for h1 in H for h2 in H)
                for e in el: dc[e] = len(dcs)
                dcs.append(sorted(el))
        contrib = [len(d) // 2 for d in dcs]
        # subsets of double cosets with contribution sum = Delta
        idx = [i for i in range(len(dcs)) if contrib[i] <= Delta]
        def subsets(start, rem, cur):
            if rem == 0:
                yield list(cur); return
            for j in range(start, len(idx)):
                i = idx[j]
                if contrib[i] <= rem:
                    cur.append(i)
                    yield from subsets(j + 1, rem - contrib[i], cur)
                    cur.pop()
        invR = inv[R]
        P = T[R[:, None], invR[None, :]]          # x_i * y_j^-1 for reps
        for sub in subsets(0, Delta, []):
            cnt += 1
            if cnt % 5000 == 0: print("  prog", cnt, "reg", regular, "best", best[0] if best else None, "reps", len(reps), flush=True)
            if cnt > maxcand: break
            inS = np.isin(dc, sub)
            M = inS[P]                             # m x m adjacency
            if not (M.sum(1) == Delta).all() or not (M.sum(0) == Delta).all():
                continue
            regular += 1
            # bitset adjacency
            pa = np.packbits(M, axis=1, bitorder='little'); pb = np.packbits(M.T, axis=1, bitorder='little')
            adjA = [int.from_bytes(r.tobytes(), 'little') for r in pa]
            adjB = [int.from_bytes(r.tobytes(), 'little') for r in pb]
            def ecc(start_side, s):
                full = (1 << m) - 1
                if start_side == 'A':
                    seenA = 1 << s; seenB = 0; frontA = 1 << s; d = 0
                    while d < LIM:
                        nb = 0; f = frontA
                        while f:
                            lb = f & -f; i = lb.bit_length() - 1; nb |= adjA[i]; f ^= lb
                        nb &= ~seenB
                        if nb == 0: break
                        d += 1; seenB |= nb
                        nf = 0; f = nb
                        while f:
                            lb = f & -f; j = lb.bit_length() - 1; nf |= adjB[j]; f ^= lb
                        nf &= ~seenA
                        if nf == 0: break
                        d += 1; seenA |= nf; frontA = nf
                    return d if (seenA == full and seenB == full) else 10**6
                else:
                    seenB = 1 << s; seenA = 0; frontB = 1 << s; d = 0
                    while d < LIM:
                        na = 0; f = frontB
                        while f:
                            lb = f & -f; j = lb.bit_length() - 1; na |= adjB[j]; f ^= lb
                        na &= ~seenA
                        if na == 0: break
                        d += 1; seenA |= na
                        nb = 0; f = na
                        while f:
                            lb = f & -f; i = lb.bit_length() - 1; nb |= adjA[i]; f ^= lb
                        nb &= ~seenB
                        if nb == 0: break
                        d += 1; seenB |= nb; frontB = nb
                    return d if (seenA == full and seenB == full) else 10**6
            LIM = D + 3
            ea = ecc('A', 0)
            if ea > LIM: continue
            diam = max(ea, ecc('B', 0))
            rec = (diam, spec, int(t), sub)
            if best is None or diam < best[0]: best = rec
            if diam <= D:
                hits.append(rec)
                if out:
                    # edge list: A vertices 0..m-1, B vertices m..2m-1
                    with open(out, 'a') as f:
                        f.write('%s\n' % rec)
    return best, hits, cnt, regular, len(reps)

if __name__ == '__main__':
    pass
