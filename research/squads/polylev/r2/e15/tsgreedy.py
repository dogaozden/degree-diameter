"""tsgreedy.py: orbit-structured greedy for pairwise disjoint totally singular lines of Q(6,q).

T = <h>, h = composition of the given point permutations (they commute; each must be semiregular on points).
A set R of totally singular lines is kept so that all |R|(q+1) points lie in pairwise distinct T-orbits. Then the
T-images of R are |T||R| pairwise disjoint totally singular lines (x in g(L) and x in h(L') forces g = h, L = L').
Candidate lines: through a random point p (in a free, non-dead T-orbit) and a point x of p^perp (x singular, so
{p, x} spans a totally singular line); the line is accepted when its q+1 points lie in distinct free orbits.
Writes OUT.i32: the expanded set, int32 (K x (q+1)) point ids of all |T||R| lines, and OUT.R.i32 (the reps).
Usage: timeout W nice -n 10 python3 tsgreedy.py HEXBIN SEED WALL_SECONDS OUT PPERM [PPERM ...]
"""
import sys, time, struct
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/polylev')
from hexlib import field

PAIRS = ((0, 4), (4, 0), (1, 5), (5, 1), (2, 6), (6, 2))


class Ctx:
    def __init__(self, path):
        with open(path, 'rb') as f:
            q, N, L = struct.unpack('3i', f.read(12))
            f.seek(12 + 4 * L * (q + 1))
            X = np.frombuffer(f.read(N * 7), dtype=np.uint8).reshape(N, 7).astype(np.int64)
        self.q, self.N, self.X = q, N, X
        _, _, self.ADD, self.MUL, self.NEG, self.INV = field(q)
        self.W = q ** np.arange(7, dtype=np.int64)
        codes = X @ self.W
        self.order = np.argsort(codes)
        self.scodes = codes[self.order]

    def normalize(self, V):
        first = np.argmax(V != 0, axis=1)
        lead = V[np.arange(len(V)), first]
        return self.MUL[self.INV[lead][:, None], V]

    def ids(self, V):
        c = self.normalize(V) @ self.W
        idx = np.searchsorted(self.scodes, c)
        idx = np.minimum(idx, self.N - 1)
        if not (self.scodes[idx] == c).all():
            raise ValueError('vector is not a point of Q(6,q)')
        return self.order[idx]

    def bform_all(self, x):
        """b(x, y) for all points y (x a 7-vector)."""
        A, M, Ng, Y = self.ADD, self.MUL, self.NEG, self.X
        s = np.zeros(self.N, dtype=np.int64)
        for i, j in PAIRS:
            s = A[s, M[x[i], Y[:, j]]]
        t = M[x[3], Y[:, 3]]
        return A[s, Ng[A[t, t]]]


def orbits(perm):
    N = len(perm)
    orb = -np.ones(N, dtype=np.int64)
    cnt, sizes = 0, set()
    for s in range(N):
        if orb[s] >= 0:
            continue
        x, k = s, 0
        while orb[x] < 0:
            orb[x] = cnt
            x = perm[x]
            k += 1
        sizes.add(k)
        cnt += 1
    return orb, cnt, sizes


def greedy(C, orb, M, rng, wall):
    q, N, X = C.q, C.N, C.X
    free = np.ones(M, dtype=bool)
    dead = np.zeros(M, dtype=bool)
    pfree = free[orb]
    lam = np.arange(1, q, dtype=np.int64)
    R, steps, fails = [], 0, 0
    t0 = time.time()
    while time.time() - t0 < wall:
        sel = np.flatnonzero(pfree & ~dead[orb])
        if len(sel) == 0:
            break
        p = int(rng.choice(sel))
        b = C.bform_all(X[p])
        xs = np.flatnonzero((b == 0) & pfree)
        xs = xs[xs != p]
        steps += 1
        if len(xs) == 0:
            dead[orb[p]] = True
            fails += 1
            continue
        Xs = X[xs]
        P = C.ADD[X[p][None, None, :], C.MUL[lam[None, :, None], Xs[:, None, :]]]
        pP = C.ids(P.reshape(-1, 7)).reshape(len(xs), q - 1)
        L = np.concatenate([np.full((len(xs), 1), p), xs[:, None], pP], axis=1)
        O = orb[L]
        ok = pfree[L].all(axis=1)
        ok &= (np.diff(np.sort(O, axis=1), axis=1) != 0).all(axis=1)
        good = np.flatnonzero(ok)
        if len(good) == 0:
            dead[orb[p]] = True
            fails += 1
            continue
        ids = L[good[rng.integers(len(good))]]
        R.append(ids)
        free[orb[ids]] = False
        pfree = free[orb]
    return np.array(R, dtype=np.int64).reshape(-1, q + 1), steps, fails


def main():
    hexpath, seed, wall, out = sys.argv[1], int(sys.argv[2]), float(sys.argv[3]), sys.argv[4]
    perms = [np.fromfile(f, dtype=np.int32).astype(np.int64) for f in sys.argv[5:]]
    C = Ctx(hexpath)
    h = perms[0]
    for P in perms[1:]:
        h = h[P]
    orb, M, sizes = orbits(h)
    assert len(sizes) == 1, f'group not semiregular on points: orbit sizes {sorted(sizes)}'
    m = sizes.pop()
    print(f'q={C.q} |T|={m} point orbits={M}  bound on |R| = {M // (C.q + 1)}', flush=True)
    rng = np.random.default_rng(seed)
    t0 = time.time()
    R, steps, fails = greedy(C, orb, M, rng, wall)
    print(f'greedy: |R|={len(R)} orbit reps, lines={len(R) * m}, covered orbits {len(R) * (C.q + 1)} of {M} '
          f'({100.0 * len(R) * (C.q + 1) / M:.1f}%), steps {steps}, dead {fails}, time {time.time() - t0:.1f}s',
          flush=True)
    R.astype(np.int32).tofile(out + '.R.i32')
    allL = []
    cur = R.copy()
    for k in range(m):
        allL.append(cur)
        cur = h[cur]
    E = np.concatenate(allL, axis=0)
    E.astype(np.int32).tofile(out + '.i32')
    print(f'wrote {len(E)} lines (|T|*|R|) to {out}.i32', flush=True)


if __name__ == '__main__':
    main()
