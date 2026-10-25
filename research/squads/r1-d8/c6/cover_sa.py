"""Simulated annealing: colour points with Z_M so that every closed collinearity nbhd X(x) sees all M colours."""
import math, random, sys
sys.path.insert(0, '/home/user/degree-diameter/research/squads/r1-d8/c6')
from c6lib import load, collinear_lists


def cover_labels(H, M, seed, iters, T0=0.6, T1=0.02, init=None, X=None):
    rng = random.Random(seed)
    N = H.N
    X = X or collinear_lists(H)
    t = list(init) if init is not None else [rng.randrange(M) for _ in range(N)]
    cnt = [[0] * M for _ in range(N)]
    for x in range(N):
        for p in X[x]:
            cnt[x][t[p]] += 1
    miss = sum(1 for x in range(N) for c in range(M) if cnt[x][c] == 0)
    best = miss; bestt = list(t)
    for it in range(iters):
        T = T0 * (T1 / T0) ** (it / iters)
        p = rng.randrange(N)
        old = t[p]
        new = rng.randrange(M - 1)
        if new >= old:
            new += 1
        d = 0
        for x in X[p]:
            cx = cnt[x]
            if cx[old] == 1:
                d += 1
            if cx[new] == 0:
                d -= 1
        if d <= 0 or rng.random() < math.exp(-d / T):
            for x in X[p]:
                cx = cnt[x]
                cx[old] -= 1
                cx[new] += 1
            t[p] = new
            miss += d
            if miss < best:
                best = miss; bestt = list(t)
                if best == 0:
                    break
    return best, bestt


if __name__ == '__main__':
    q = int(sys.argv[1]); Ms = [int(x) for x in sys.argv[2].split(',')]; iters = int(sys.argv[3])
    H = load(q); X = collinear_lists(H)
    for M in Ms:
        best, t = cover_labels(H, M, 1, iters, X=X)
        print(f'q={q} M={M} cover-missing after {iters} iters: {best}', flush=True)
        with open(f'/home/user/degree-diameter/research/squads/r1-d8/c6/cover_q{q}_M{M}.txt', 'w') as fh:
            fh.write(' '.join(map(str, t)) + '\n')
