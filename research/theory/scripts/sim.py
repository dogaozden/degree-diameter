"""Monte Carlo test of THRESHOLD.md Theorems 3-4 at finite size: P(diam H(G,S) <= D) for uniform random Delta-subsets S,
against the prediction exp(-mu) with mu from groups_inv / data_check.mu_special.  Light: a few minutes in total.
Usage: python3 sim.py [trials]"""
import sys, math, itertools
import numpy as np
from groups_inv import sl2, psl2, cyc, prod
from model import mu_model, W

def sl2_elems(p):
    return [(a, b, c, d) for a in range(p) for b in range(p) for c in range(p) for d in range(p) if (a * d - b * c) % p == 1]

def matgroup(p, proj):
    E = sl2_elems(p)
    if proj:  # PSL: canonical representative of {x, -x}
        canon = lambda x: min(x, tuple((-t) % p for t in x))
        E = sorted(set(canon(x) for x in E))
    else:
        canon = lambda x: x
    idx = {x: i for i, x in enumerate(E)}
    A = np.array(E, dtype=np.int64); n = len(E)
    mul = np.empty((n, n), dtype=np.int32)
    key = {}
    for i, x in enumerate(E):
        a, b, c, d = x
        P = np.stack([(a * A[:, 0] + b * A[:, 2]) % p, (a * A[:, 1] + b * A[:, 3]) % p,
                      (c * A[:, 0] + d * A[:, 2]) % p, (c * A[:, 1] + d * A[:, 3]) % p], 1)
        mul[i] = [idx[canon(tuple(r))] for r in P.tolist()]
    return mul

def cyclic(m):
    r = np.arange(m); return ((r[:, None] + r[None, :]) % m).astype(np.int32)

def direct(m1, m2):
    n1, n2 = len(m1), len(m2)
    # element (i, j) -> i * n2 + j
    return (m1[:, None, :, None] * n2 + m2[None, :, None, :]).reshape(n1 * n2, n1 * n2).astype(np.int32)

def inverse(mul):
    e = int(np.where((mul == np.arange(len(mul))[None, :]).all(1))[0][0])
    return np.argmax(mul == e, axis=1), e

def covered(mul, inv, e, S, D):
    """True iff diam H(G,S) <= D (covering lemma, THRESHOLD.md Lemma 0.1)."""
    n = len(mul); k = D // 2
    def power_cover(F, start, r):          # F^r * start as a boolean mask (left multiplication)
        m = np.zeros(n, bool); m[start] = True
        for _ in range(r):
            cur = np.nonzero(m)[0]; m2 = m.copy()
            for f in F: m2[mul[f, cur]] = True
            m = m2
        return m
    if D % 2 == 0:
        P = np.unique(mul[S[:, None], inv[S][None, :]].ravel())        # u t^-1
        return power_cover(P, S, k - 1).all()
    Q = np.unique(mul[inv[S][:, None], S[None, :]].ravel())            # s^-1 t
    if not power_cover(Q, [e], k).all(): return False
    P = np.unique(mul[S[:, None], inv[S][None, :]].ravel())
    return power_cover(P, [e], k).all()

def run(name, mul, ginfo, D, deltas, trials, rng):
    inv, e = inverse(mul); n = len(mul); out = []
    for d in deltas:
        ok = sum(covered(mul, inv, e, rng.choice(n, d, replace=False), D) for _ in range(trials))
        mg = n * math.exp(-W(d, D) / n)
        ms, _ = mu_model(d, D, n, ginfo, coincid=False); mf, _ = mu_model(d, D, n, ginfo)
        pe = ok / trials; se = math.sqrt(max(pe * (1 - pe), 0.25 / trials) / trials)
        out.append((name, n, D, d, trials, pe, se, mg, ms, mf))
        print('%-18s D=%d Δ=%-3d P_emp=%.3f±%.3f | e^-mu: generic %.3f  +special %.3f  +coincid %.3f | mu %.2f %.2f %.2f' % (
            name, D, d, pe, se, math.exp(-mg), math.exp(-ms), math.exp(-mf), mg, ms, mf), flush=True)
    return out

if __name__ == '__main__':
    T = int(sys.argv[1]) if len(sys.argv) > 1 else 400
    rng = np.random.default_rng(20261023)
    SL11 = matgroup(11, False); PSL11 = matgroup(11, True); SL5 = matgroup(5, False)
    G1320 = [('SL(2,11)', SL11, sl2(11)),
             ('PSL(2,11) x Z2', direct(PSL11, cyclic(2)), prod(psl2(11), cyc(2))),
             ('SL(2,5) x Z11', direct(SL5, cyclic(11)), prod(sl2(5), cyc(11))),
             ('Z_1320 (abelian)', cyclic(1320), cyc(1320))]
    res = []
    print('--- D = 3 (words s^-1 t; Theorem 3 regime: Delta ~ sqrt(n ln n)) ---')
    for name, m, g in G1320[:3]:
        res += run(name, m, g, 3, [80, 90, 100, 110], T, rng)
    print('--- D = 4 ---')
    for name, m, g in G1320[:3]:
        res += run(name, m, g, 4, [17, 19, 21, 23], T, rng)
    print('--- D = 5 ---')
    for name, m, g in G1320:
        res += run(name, m, g, 5, [10, 11, 12, 13, 14], T, rng)
    print('--- D = 6 ---')
    for name, m, g in G1320[:3]:
        res += run(name, m, g, 6, [7, 8, 9], T, rng)
    import csv
    with open('sim_results.csv', 'w', newline='') as fh:
        wr = csv.writer(fh); wr.writerow(['group', 'n', 'D', 'Delta', 'trials', 'P_emp', 'se', 'mu_generic', 'mu_special', 'mu_full'])
        for r in res: wr.writerow([r[0], r[1], r[2], r[3], r[4], '%.4f' % r[5], '%.4f' % r[6], '%.3f' % r[7], '%.3f' % r[8], '%.3f' % r[9]])
