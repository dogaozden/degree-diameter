"""Relaxed sets of W(q) as unions of orbits of a subgroup of Sp(4,q) (job d5-relax).

Random elements g of Sp(4,q) (products of symplectic transvections); for the cyclic group <g> (or <g, h>) the points
of W(q) split into orbits.  For a union T of orbits, the number of points of T collinear with a point x depends only on
the orbit of x, so "T is relaxed" is a condition on the orbit matrix N[i][j] = #points of orbit j collinear with a fixed
point of orbit i: sum_{j in I} N[i][j] <= 1 for every i in I.  The best union is found exactly by a MIP (HiGHS).

Point numbering = gqlib.W(q) (PG(3,q) points with first non-zero coordinate 1, in itertools.product order), so the
output sets can be used with the d5gq tools and the data/ files of export_w.py.
usage: python3 orbits.py q n_elements seed [gens=1|2] [out.json]"""
import sys, os, json, itertools, math, random, time
import numpy as np
import highspy
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'chartlift'))
from gf import GF


class WSp:
    def __init__(self, q):
        F = GF(q); self.q = q; self.F = F
        self.add = np.array(F.add); self.mul = np.array(F.mul); self.sub = np.array(F.sub)
        self.inv = np.array([0] + [F.inv[a] for a in range(1, q)])
        pts = [v for v in itertools.product(range(q), repeat=4) if any(v) and next(x for x in v if x) == 1]
        self.P = np.array(pts, dtype=np.int64); self.n = len(pts)
        self.code = np.full(q ** 4, -1, dtype=np.int64)
        self.code[self._enc(self.P)] = np.arange(self.n)
        self.C = self.form(self.P[:, None, :], self.P[None, :, :]) == 0
        np.fill_diagonal(self.C, False)

    def _enc(self, X):
        q = self.q
        return ((X[..., 0] * q + X[..., 1]) * q + X[..., 2]) * q + X[..., 3]

    def form(self, x, y):
        m, a = self.mul, self.add
        s = a[m[x[..., 0], y[..., 2]], m[x[..., 1], y[..., 3]]]
        t = a[m[x[..., 2], y[..., 0]], m[x[..., 3], y[..., 1]]]
        return self.sub[s, t]

    def index(self, X):
        """indices of the projective points of the rows of X (non-zero vectors)"""
        first = np.argmax(X != 0, axis=1); lead = X[np.arange(len(X)), first]
        Y = self.mul[self.inv[lead][:, None], X]
        return self.code[self._enc(Y)]

    def transvection(self, v, lam):
        """permutation of the points under x -> x + lam w(x, v) v"""
        c = self.mul[lam, self.form(self.P, v[None, :])]                 # (n,)
        X = self.add[self.P, self.mul[c[:, None], v[None, :]]]
        return self.index(X)

    def random_element(self, rng, k=12):
        perm = np.arange(self.n)
        for _ in range(k):
            v = self.P[rng.randrange(self.n)]; lam = rng.randrange(1, self.q)
            perm = self.transvection(v, lam)[perm]
        return perm


def orbits_of(gens, n):
    par = np.arange(n)
    def find(x):
        while par[x] != x:
            par[x] = par[par[x]]; x = par[x]
        return x
    for g in gens:
        for x in range(n):
            a, b = find(x), find(int(g[x]))
            if a != b: par[a] = b
    roots = np.array([find(x) for x in range(n)])
    labs = {r: i for i, r in enumerate(sorted(set(roots.tolist())))}
    lab = np.array([labs[r] for r in roots])
    return lab, len(labs)


def perm_order(g):
    seen = np.zeros(len(g), bool); o = 1
    for x in range(len(g)):
        if not seen[x]:
            c = 0; y = x
            while not seen[y]:
                seen[y] = True; y = int(g[y]); c += 1
            o = o * c // math.gcd(o, c)
    return o


def best_union(Wq, lab, k, timelimit=10):
    sizes = np.bincount(lab, minlength=k)
    rep = np.array([np.nonzero(lab == i)[0][0] for i in range(k)])
    N = np.zeros((k, k), dtype=np.int64)
    for i in range(k):
        N[i] = np.bincount(lab[Wq.C[rep[i]]], minlength=k)
    ok = [i for i in range(k) if N[i, i] <= 1]
    if not ok: return 0, []
    h = highspy.Highs(); h.setOptionValue('output_flag', False); h.setOptionValue('time_limit', timelimit)
    h.setOptionValue('threads', 1)
    m = len(ok); inf = highspy.kHighsInf
    for i in ok: h.addVar(0.0, 1.0)
    h.changeColsIntegrality(m, np.arange(m, dtype=np.int32), np.array([highspy.HighsVarType.kInteger] * m))
    h.changeColsCost(m, np.arange(m, dtype=np.int32), -sizes[ok].astype(float))
    for a, i in enumerate(ok):
        row = N[i, ok].astype(float); S = row.sum()
        if S <= 1: continue
        coef = row.copy(); coef[a] += S - 1          # sum_j N x_j + (S-1) x_i <= S
        idx = np.nonzero(coef)[0]
        h.addRow(-inf, S, len(idx), idx.astype(np.int32), coef[idx])
    h.run()
    sol = h.getSolution().col_value
    I = [ok[a] for a in range(m) if sol[a] > 0.5]
    T = sorted(np.nonzero(np.isin(lab, I))[0].tolist())
    return len(T), T


def check_relaxed(Wq, T):
    T = np.array(T); d = Wq.C[np.ix_(T, T)].sum(1)
    return bool((d <= 1).all()), int(d.sum() // 2)


def main():
    q = int(sys.argv[1]); ne = int(sys.argv[2]); seed = int(sys.argv[3])
    gens = int(sys.argv[4]) if len(sys.argv) > 4 else 1
    out = sys.argv[5] if len(sys.argv) > 5 else None
    rng = random.Random(seed); Wq = WSp(q); t0 = time.time()
    best = (0, None, None)
    seen_orders = {}
    for e in range(ne):
        G = [Wq.random_element(rng) for _ in range(gens)]
        if gens == 1:
            o = perm_order(G[0])
            # also use powers of g, which give the subgroups of <g>
            cand = [(o // d, Wq_pow(G[0], d)) for d in divisors(o) if d < o]
        else:
            cand = [(0, G)]
        for (oo, gg) in cand:
            gl = [gg] if gens == 1 else gg
            lab, k = orbits_of(gl, Wq.n)
            if k > int(os.environ.get("KMAX", "150")): continue
            s, T = best_union(Wq, lab, k)
            key = (oo, k)
            if s > seen_orders.get(key, -1): seen_orders[key] = s
            if s > best[0]:
                ok, pairs = check_relaxed(Wq, T); assert ok
                best = (s, T, (oo, k, pairs))
                print('elt %d: order %d, %d orbits -> relaxed union %d (%d pairs)  [%.0f s]' % (e, oo, k, s, pairs, time.time() - t0))
                sys.stdout.flush()
                if out: json.dump(dict(q=q, size=s, T=T, group_order=oo, orbits=k, pairs=pairs), open(out, 'w'))
    print('summary (group order, #orbits) -> best:', sorted(seen_orders.items(), key=lambda x: -x[1])[:15])
    print('best', best[0], best[2])


def divisors(o):
    return [d for d in range(1, o + 1) if o % d == 0]


def Wq_pow(g, d):
    r = np.arange(len(g)); b = g.copy()
    while d:
        if d & 1: r = b[r]
        b = b[b]; d >>= 1
    return r


if __name__ == '__main__':
    main()
