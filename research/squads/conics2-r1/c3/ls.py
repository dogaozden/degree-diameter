import sys, time, math, random
import numpy as np
from common import *

D = q + 2
def miss_per_source(sig, R):
    """Return (total bad, per-source miss counts over 2N level-0 sources)."""
    sig = np.asarray(sig, np.int64); R = np.asarray(sorted(R), np.int64)
    free = np.zeros(N, bool); free[R] = True
    T = np.full((4 * N, D), -1, np.int64)
    T[:N, :q + 1] = PL + N; T[N:2 * N, :q + 1] = LP; T[2 * N:3 * N, :q + 1] = PL + 3 * N; T[3 * N:, :q + 1] = LP + 2 * N
    keep = np.nonzero(~free)[0]
    T[keep, q + 1] = 3 * N + sig[keep]
    sinv = np.empty(N, np.int64); sinv[sig] = np.arange(N)
    lk = 3 * N + np.arange(N); ok = ~free[sinv]
    T[lk[ok], q + 1] = sinv[ok]
    T[T < 0] = 4 * N
    permiss = np.zeros(2 * N, np.int64)
    srcs = np.arange(2 * N); chunk = 2048
    for c0 in range(0, 2 * N, chunk):
        S = srcs[c0:c0 + chunk]; k = len(S); W = (k + 63) // 64
        vis = np.zeros((4 * N + 1, W), np.uint64)
        vis[S, np.arange(k) // 64] |= np.left_shift(np.uint64(1), (np.arange(k) % 64).astype(np.uint64))
        for _ in range(7):
            nv = vis.copy()
            for t in range(D):
                nv[:4 * N] |= vis[T[:, t]]
            nv[4 * N] = 0
            vis = nv
        full = np.full(W, ~np.uint64(0), np.uint64)
        if k % 64:
            full[-1] = np.uint64((1 << (k % 64)) - 1)
        miss = vis[2 * N:4 * N] ^ full
        bits = np.unpackbits(np.ascontiguousarray(miss).view(np.uint8), axis=1, bitorder='little')
        permiss[c0:c0 + k] = bits.sum(axis=0)[:k]
    return int(permiss.sum()), permiss

def ball(v, r):
    """vertices of H(q) incidence graph within distance r of vertex v (v<N: point, v>=N: line index v-N)."""
    seen = {('p' if v < N else 'l', v if v < N else v - N)}
    frontier = [seen.__iter__ and ('p' if v < N else 'l', v if v < N else v - N)]
    out = set()
    for _ in range(r):
        nf = []
        for typ, i in frontier:
            nbrs = LP[i] if typ == 'p' else PL[i]
            ntyp = 'l' if typ == 'p' else 'p'
            for j in nbrs:
                key = (ntyp, int(j))
                if key not in seen:
                    seen.add(key); nf.append(key)
        frontier = nf
    return [j for typ, j in seen if typ == 'p']

BALL2 = None
def pts_near_point(p, r=4):
    global BALL2
    if BALL2 is None:
        BALL2 = {}
    key = (p, r)
    if key not in BALL2:
        BALL2[key] = [j for j in ball(p, r) if j != p]
    return BALL2[key]

if __name__ == '__main__':
    seed = int(sys.argv[1]); x = int(sys.argv[2]); budget = float(sys.argv[3]); out = sys.argv[4]
    T0 = float(sys.argv[5]) if len(sys.argv) > 5 else 3.0
    rng = random.Random(seed)
    sig, R0 = load_rec()
    R = list(R0) + [x]
    sig = sig.copy()
    bad, per = miss_per_source(sig, R)
    best = (bad, sig.copy()); t0 = time.time(); it = 0
    print('start', x, bad, flush=True)
    while time.time() - t0 < budget and best[0] > 0:
        it += 1
        # pick a bad source
        bs = np.nonzero(per)[0]
        s = int(rng.choice(list(bs)))
        if s < N:
            center = s
        else:
            center = int(LP[s - N][rng.randrange(q + 1)])  # a point on the bad line
        # choose a: point near center; b: point or point near sigma-line near sig(center)
        r = rng.random()
        if r < 0.5:
            a = rng.choice(pts_near_point(center, 4) + [center])
            b = rng.randrange(N)
        else:
            l = int(sig[center]) if rng.random() < 0.5 else int(sig[rng.choice(pts_near_point(center, 4) + [center])])
            # a line near sigma(center): line from ball
            near_lines = [j for j in ball(N + l, 3)] if False else None
            cand_lines = []
            # lines at incidence distance 2 or 4 from l on level-1 side
            pts_ = LP[l]
            p2 = int(pts_[rng.randrange(q + 1)])
            ll = int(PL[p2][rng.randrange(q + 1)])
            if ll == l:
                continue
            b = int(np.nonzero(sig == ll)[0][0])
            a = rng.choice(pts_near_point(center, 4) + [center])
        if a == b or (a in R and b in R):
            continue
        sig2 = sig.copy(); sig2[a], sig2[b] = sig2[b], sig2[a]
        bad2, per2 = miss_per_source(sig2, R)
        d = bad2 - bad
        T = T0 * (1 - (time.time() - t0) / budget) + 0.05
        if d <= 0 or rng.random() < math.exp(-d / T):
            sig, bad, per = sig2, bad2, per2
        if bad < best[0]:
            best = (bad, sig.copy())
            print(f'it {it} t={time.time()-t0:.0f}s new best {bad}', flush=True)
            save(best[1], R, out)
    print('done it', it, 'best', best[0], 'time', time.time() - t0, flush=True)
    save(best[1], R, out)
