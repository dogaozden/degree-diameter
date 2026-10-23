"""Larger-n Monte Carlo (no multiplication table): G = SL(2,p) x Z_m or PSL(2,p) x Z_m, p prime, D = 3, 4, 5.
Checks that P(diam <= D) -> exp(-mu) as n grows (THRESHOLD.md Theorem 3 regime) and the special/coincidence terms.
Usage: python3 sim2.py [trials]"""
import sys, math, csv
import numpy as np
from groups_inv import sl2, psl2, cyc, prod
from model import mu_model, W

class Grp:
    def __init__(s, p, m, proj):
        s.p, s.m, s.proj = p, m, proj
        s.n = (p * (p * p - 1) // (2 if proj else 1)) * m
        s.info = prod(psl2(p) if proj else sl2(p), cyc(m)) if m > 1 else (psl2(p) if proj else sl2(p))
    def sample(s, k, rng):
        out = set()
        while len(out) < k:
            a, b, c = rng.integers(0, s.p, 3)
            if a == 0: continue
            # random element of SL(2,p): pick a != 0, b, c; d = (1 + b c)/a  (not uniform over all of SL; fix below)
            out.add(s.code(np.array([[a]]), np.array([[b]]), np.array([[c]]), np.array([[(1 + b * c) * pow(int(a), s.p - 2, s.p) % s.p]]),
                           np.array([[rng.integers(0, s.m)]]))[0, 0])
        return np.array(sorted(out))
    def sample_uniform(s, k, rng):
        out = set()
        while len(out) < k:
            a, b, c, d = rng.integers(0, s.p, 4)
            if (a * d - b * c) % s.p != 1: continue
            out.add(int(s.code(*(np.array([[x]]) for x in (a, b, c, d, rng.integers(0, s.m))))[0, 0]))
        return np.array(sorted(out), dtype=np.int64)
    def canon(s, a, b, c, d):
        if not s.proj: return a, b, c, d
        p = s.p; na, nb, nc, nd = (-a) % p, (-b) % p, (-c) % p, (-d) % p
        # lexicographic min of (a,b,c,d) and its negative
        flip = (na < a) | ((na == a) & ((nb < b) | ((nb == b) & ((nc < c) | ((nc == c) & (nd < d))))))
        return np.where(flip, na, a), np.where(flip, nb, b), np.where(flip, nc, c), np.where(flip, nd, d)
    def code(s, a, b, c, d, z):
        a, b, c, d = s.canon(a % s.p, b % s.p, c % s.p, d % s.p)
        return (((a * s.p + b) * s.p + c) * s.p + d) * s.m + (z % s.m)
    def dec(s, g):
        z = g % s.m; g = g // s.m; d = g % s.p; g //= s.p; c = g % s.p; g //= s.p; b = g % s.p; a = g // s.p
        return a, b, c, d, z
    def inv(s, g):
        a, b, c, d, z = s.dec(g); return s.code(d, -b, -c, a, -z)
    def mulset(s, X, Y):
        """all products x*y, x in X, y in Y (1-d code arrays) -> unique codes"""
        a, b, c, d, z = s.dec(X[:, None]); e, f, g, h, w = s.dec(Y[None, :])
        return np.unique(s.code(a * e + b * g, a * f + b * h, c * e + d * g, c * f + d * h, z + w).ravel())

def covered(G, S, D):
    Si = G.inv(S); k = D // 2
    if D % 2 == 0:
        P = G.mulset(S, Si); R = S
        for _ in range(k - 1): R = G.mulset(P, R)
        return len(R) == G.n
    for L, R0 in ((G.mulset(Si, S), None), (G.mulset(S, Si), None)):
        X = L
        for _ in range(k - 1): X = G.mulset(L, X)
        if len(X) != G.n: return False
    return True

if __name__ == '__main__':
    T = int(sys.argv[1]) if len(sys.argv) > 1 else 200
    rng = np.random.default_rng(7)
    def target_delta(G, D, mu):   # smallest Delta with generic mu <= target
        d = 3
        while G.n * math.exp(-W(d, D) / G.n) > mu: d += 1
        return d
    plan = []
    for p in (11, 17, 23, 31, 41):
        G = Grp(p, 1, False); d1 = target_delta(G, 3, 2.0); plan.append((G, 3, [d1 - 2, d1, d1 + 2, d1 + 4]))
    for p in (13, 23, 37):
        for proj in (False, True):
            G = Grp(p, 1, proj); d1 = target_delta(G, 5, 1.0); plan.append((G, 5, [d1 - 1, d1, d1 + 1]))
    for p in (17, 29):
        for proj in (False, True):
            G = Grp(p, 1, proj); d1 = target_delta(G, 4, 1.0); plan.append((G, 4, [d1 - 1, d1, d1 + 1]))
    for p, m in ((5, 37), (7, 13)):
        G = Grp(p, m, False); d1 = target_delta(G, 5, 1.0); plan.append((G, 5, [d1 - 1, d1, d1 + 1]))
    rows = []
    for G, D, deltas in plan:
        name = '%s(2,%d)%s' % ('PSL' if G.proj else 'SL', G.p, ' x Z%d' % G.m if G.m > 1 else '')
        for d in deltas:
            ok = sum(covered(G, G.sample_uniform(d, rng), D) for _ in range(T)); pe = ok / T
            se = math.sqrt(max(pe * (1 - pe), 0.25 / T) / T)
            mg = G.n * math.exp(-W(d, D) / G.n); ms, _ = mu_model(d, D, G.n, G.info, coincid=False); mf, _ = mu_model(d, D, G.n, G.info)
            rows.append((name, G.n, D, d, T, pe, se, mg, ms, mf))
            print('%-16s n=%-6d D=%d Δ=%-4d P_emp=%.3f±%.3f | e^-mu: generic %.3f +special %.3f +coincid %.3f | mu %.2f %.2f %.2f' % (
                name, G.n, D, d, pe, se, math.exp(-mg), math.exp(-ms), math.exp(-mf), mg, ms, mf), flush=True)
    with open('sim2_results.csv', 'w', newline='') as fh:
        wr = csv.writer(fh); wr.writerow(['group', 'n', 'D', 'Delta', 'trials', 'P_emp', 'se', 'mu_generic', 'mu_special', 'mu_full'])
        for r in rows: wr.writerow([r[0], r[1], r[2], r[3], r[4], '%.4f' % r[5], '%.4f' % r[6], '%.3f' % r[7], '%.3f' % r[8], '%.3f' % r[9]])
