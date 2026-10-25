# c2: iterated local search for pairwise-opposite sets of H(8) points: (1,2)-swaps + plateau (1,1)-swaps + perturbation.
import numpy as np, sys, time
from extend import load_P
P = load_P(); N = P.shape[0]
MTAB = np.zeros((8, 8), dtype=np.int64)
def hm(a, b):
    r = 0
    for i in range(3):
        if (b >> i) & 1: r ^= a << i
    for i in (4, 3):
        if (r >> i) & 1: r ^= 0b1011 << (i - 3)
    return r
for a in range(8):
    for b in range(8): MTAB[a, b] = hm(a, b)
def pair_row(x, Y):   # B(x, y) for y in Y (index array)
    a = P[x]; b = P[Y]
    return (MTAB[a[0], b[:, 4]] ^ MTAB[a[4], b[:, 0]] ^ MTAB[a[1], b[:, 5]] ^ MTAB[a[5], b[:, 1]] ^ MTAB[a[2], b[:, 6]] ^ MTAB[a[6], b[:, 2]])
ALL = np.arange(N)
def conf_row(x):  # True where v collinear-in-Q (B==0) with x, v != x
    r = pair_row(x, ALL) == 0; r[x] = False; return r
def pair_mat(Y):
    return np.stack([pair_row(y, Y) for y in Y]) if len(Y) else np.zeros((0, 0), dtype=np.int64)
def run(S0, seconds, seed):
    rng = np.random.default_rng(seed)
    inS = np.zeros(N, dtype=bool); inS[S0] = True
    cnt = np.zeros(N, dtype=np.int64)
    for x in S0: cnt += conf_row(x)
    best = list(S0); cur = list(S0)
    t0 = time.time(); it = 0
    def add(x):
        nonlocal cnt
        inS[x] = True; cur.append(x); cnt += conf_row(x)
    def remove(x):
        nonlocal cnt
        inS[x] = False; cur.remove(x); cnt -= conf_row(x)
    while time.time() - t0 < seconds:
        it += 1
        # 1) add free vertices
        free = np.nonzero((cnt == 0) & (~inS))[0]
        while len(free):
            x = int(rng.choice(free)); add(x)
            free = np.nonzero((cnt == 0) & (~inS))[0]
        if len(cur) > len(best):
            best = list(cur); print('  new best', len(best), 'it', it, flush=True)
            open('ils_best_ids.txt', 'w').write(' '.join(map(str, sorted(best))) + '\n')
        # 2) (1,2)-swaps: remove x, add two opposite 1-tight neighbours
        improved = False
        order = list(cur); rng.shuffle(order)
        for x in order:
            if not inS[x]: continue
            T = np.nonzero((cnt == 1) & (~inS) & conf_row(x))[0]
            if len(T) < 2: continue
            M = pair_mat(T) != 0
            ii, jj = np.nonzero(np.triu(M, 1))
            if len(ii):
                k = rng.integers(len(ii)); u, w = int(T[ii[k]]), int(T[jj[k]])
                remove(x); add(u); add(w); improved = True
                break
        if improved: continue
        # 3) plateau: swap a 1-tight vertex in, then continue; or perturb with a random 2-tight vertex
        cand = np.nonzero((cnt == 1) & (~inS))[0]
        if len(cand) and rng.random() < 0.7:
            v = int(rng.choice(cand))
            x = [y for y in cur if conf_row(y)[v]][0] if False else None
            cr = conf_row(v); xs = [y for y in cur if cr[y]]
            if len(xs) == 1:
                remove(xs[0]); add(v)
            continue
        c2 = np.nonzero((cnt <= 2) & (~inS))[0]
        v = int(rng.choice(c2)) if len(c2) else int(rng.integers(N))
        cr = conf_row(v)
        for y in [y for y in cur if cr[y]]: remove(y)
        add(v)
    return best
if __name__ == '__main__':
    S0 = [int(x) for x in open(sys.argv[1]).read().split()]
    secs = float(sys.argv[2]); seed = int(sys.argv[3])
    best = run(S0, secs, seed)
    print('final best', len(best))
    open(sys.argv[4], 'w').write(' '.join(map(str, sorted(best))) + '\n')
