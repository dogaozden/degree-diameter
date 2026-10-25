#!/usr/bin/env python3
"""Hermitian-type spreads S(n): the hexagon lines inside n^perp for a nonsingular point n (B(n,x) = 0).
A set T of lines is a dual ovoid (every line outside T meets exactly one line of T) iff every line outside T has exactly
one covered point, where the covered points are the points of T's lines; then T is pairwise opposite.
usage: spreads.py SEED NTRY    (prints counts and dual-ovoid checks; saves elliptic ones to scratchpad r6_c5/spreads/)"""
import numpy as np, sys, os, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from hexmod import Hex
SP = '/tmp/claude-0/-home-user-degree-diameter/0a251e0c-8f17-58ce-a4f2-34eda2ea0db1/scratchpad/'
q = 11
H = Hex(SP + 'hex_q11.bin'); N = H.N; lp = H.lp; NL = lp.shape[0]; XC = H.X


def wvec(n):
    """B(n, x) = w . x (mod q) with the hexmod form B(x,y) = x0y4+x4y0+x1y5+x5y1+x2y6+x6y2-2x3y3."""
    n = [int(v) % q for v in n]
    return np.array([n[4], n[5], n[6], (-2 * n[3]) % q, n[0], n[1], n[2]], dtype=np.int64)


def Qval(n):
    n = [int(v) % q for v in n]
    return (n[0] * n[4] + n[1] * n[5] + n[2] * n[6] - n[3] * n[3]) % q


def spread_of(n):
    """hexagon lines with all 12 points in n^perp, sorted."""
    Z = ((XC @ wvec(n)) % q == 0)
    return np.nonzero(Z[lp].all(axis=1))[0]


def dual_ovoid_check(T):
    """returns (disjoint, every outside line has exactly one covered point, min, max covered count outside)."""
    T = np.asarray(T)
    cover = -np.ones(N, dtype=np.int64)
    cover[lp[T].ravel()] = np.repeat(np.arange(len(T)), q + 1)
    disjoint = int((cover >= 0).sum()) == (q + 1) * len(T)
    cnt = (cover[lp] >= 0).sum(axis=1)
    inT = np.zeros(NL, bool); inT[T] = True
    c = cnt[~inT]
    return disjoint, bool((c == 1).all()), int(c.min()), int(c.max())


if __name__ == '__main__':
    seed = int(sys.argv[1]); ntry = int(sys.argv[2])
    rng = np.random.default_rng(seed)
    outdir = SP + 'r6_c5/spreads/'; os.makedirs(outdir, exist_ok=True)
    t0 = time.time(); stats = {}
    saved = 0
    for it in range(ntry):
        n = rng.integers(0, q, size=7)
        if Qval(n) == 0: continue
        T = spread_of(n)
        stats[len(T)] = stats.get(len(T), 0) + 1
        if len(T) == 1332 and saved < 40:
            dj, ok, mn, mx = dual_ovoid_check(T)
            print(f'n={n.tolist()} Q={Qval(n)} lines={len(T)} disjoint={dj} dual_ovoid={ok} cov_outside=[{mn},{mx}] '
                  f'[{time.time()-t0:.0f}s]', flush=True)
            if dj and ok:
                np.save(outdir + f'T_{seed}_{it}.npy', T)
                with open(outdir + f'T_{seed}_{it}.n', 'w') as g: g.write(' '.join(map(str, n.tolist())) + '\n')
                saved += 1
    print('line counts over random nonsingular n:', dict(sorted(stats.items())), f'[{time.time()-t0:.0f}s]')
