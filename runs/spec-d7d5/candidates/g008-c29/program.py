import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe baseline families.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# NEW (bold): Haar graphs over the non-abelian simple groups PSL(2, p).
#
# Vertices A_x = x and B_y = |G| + y. Connection set S = {s_1..s_d} subset of G:
#   A_x ~ B_{x*s_j}.  Each A_x and B_y has degree d (distinct s give distinct
#   neighbours). Left multiplication by h is an automorphism, so it suffices to
#   check BFS distances from A_e and B_e: every pair lies in one of the orbits.
# Metacyclic lifts (the older family) cannot produce these non-solvable groups.
# ----------------------------------------------------------------------------

class _PSL:
    """PSL(2, p) for prime p >= 5, elements as canonical 2x2 matrices, identity at index 0."""

    def __init__(self, p):
        self.p = p
        seen = set()
        for a, b, c, dd in itertools.product(range(p), repeat=4):
            if (a * dd - b * c) % p == 1:
                seen.add(self._canon((a, b, c, dd)))
        ident = self._canon((1, 0, 0, 1))
        rest = sorted(seen - {ident})
        self.elems = [ident] + rest
        self.index = {e: i for i, e in enumerate(self.elems)}
        self.g = len(self.elems)
        self._tab = {}
        self._inv = {}

    def _canon(self, t):
        p = self.p
        neg = tuple((-v) % p for v in t)
        return min(t, neg)

    def _mul(self, X, Y):
        p = self.p
        a, b, c, dd = X
        e, f, h, k = Y
        return self._canon(((a * e + b * h) % p, (a * f + b * k) % p,
                            (c * e + dd * h) % p, (c * f + dd * k) % p))

    def inv(self, i):
        if i not in self._inv:
            a, b, c, dd = self.elems[i]
            p = self.p
            self._inv[i] = self.index[self._canon((dd % p, (-b) % p, (-c) % p, a % p))]
        return self._inv[i]

    def table(self, i):
        """table[x] = index of x * elems[i]."""
        if i not in self._tab:
            Y = self.elems[i]
            self._tab[i] = np.array([self.index[self._mul(X, Y)] for X in self.elems],
                                    dtype=np.int64)
        return self._tab[i]


def _haar_cost(g, D, Rs, Ris):
    """Unreached (vertex, source) pairs from A_e and B_e within distance D (0 means valid)."""
    cost = 0
    for side in (0, 1):
        A = np.zeros(g, dtype=bool)
        B = np.zeros(g, dtype=bool)
        if side == 0:
            A[0] = True
        else:
            B[0] = True
        fA, fB = A.copy(), B.copy()
        for _ in range(D):
            nB = np.zeros(g, dtype=bool)
            if fA.any():
                xs = np.flatnonzero(fA)
                for R in Rs:
                    nB[R[xs]] = True
            nB &= ~B
            nA = np.zeros(g, dtype=bool)
            if fB.any():
                ys = np.flatnonzero(fB)
                for Ri in Ris:
                    nA[Ri[ys]] = True
            nA &= ~A
            B |= nB
            A |= nA
            fA, fB = nA, nB
            if not (fA.any() or fB.any()):
                break
        cost += 2 * g - int(A.sum()) - int(B.sum())
    return cost


def _haar_search(P, d, D, rng, deadline):
    """Simulated annealing over connection sets S of size d. Returns S or None."""
    g = P.g

    def cost_of(S):
        Rs = [P.table(s) for s in S]
        Ris = [P.table(P.inv(s)) for s in S]
        return _haar_cost(g, D, Rs, Ris)

    S = rng.sample(range(g), d)
    cost = cost_of(S)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    best_c = cost
    stale = 0
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        frac = (now - t0) / span
        temp = max(0.2, 2.0 * (1.0 - frac))
        if stale > 3000:
            S = rng.sample(range(g), d)
            cost = cost_of(S)
            best_c = cost
            stale = 0
            continue
        j = rng.randrange(d)
        e = rng.randrange(g)
        if e in S:
            stale += 1
            continue
        old = S[j]
        S[j] = e
        c2 = cost_of(S)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost = c2
        else:
            S[j] = old
        if cost < best_c:
            best_c = cost
            stale = 0
        else:
            stale += 1
    return list(S) if cost == 0 else None


def _haar_graph_from(P, S):
    """Edges of the Haar graph of PSL(2,p) with connection set S: A_x ~ B_{x*s}."""
    g = P.g
    edges = []
    for s in S:
        R = P.table(s).tolist()
        for x in range(g):
            edges.append((x, g + R[x]))
    return 2 * g, edges


# ----------------------------------------------------------------------------
# Parent family: bi-Cayley lifts over semidirect products Z_m x| Z_k2.
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_KS = (1, 2, 3, 4)


def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, -(-target // k2))
        if k2 == 1:
            r = 1
        elif k2 == 2 and rng.random() < 0.3:
            r = m - 1
            if math.gcd(r, m) != 1 or pow(r, 2, m) != 1 % m:
                r = None
                continue
        else:
            r = None
            for _ in range(60):
                c = rng.randrange(2, m) if m > 2 else 1
                if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                    r = c
                    break
            if r is None:
                continue
        return m, k2, r
    return None


def _semidirect_tables(m, k2, r):
    """Return (G, Ts, Invs) for Z_m x| Z_k2 (element a*k2+b, (a,b)(c,e) = (a+r^b c, b+e))."""
    G = m * k2
    x = np.arange(G, dtype=np.int64)
    a = x // k2
    b = x % k2
    powers = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    M = ((a[:, None] + powers[b[:, None]] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2
    Ts = np.ascontiguousarray(M.T)
    Invs = np.empty((G, G), dtype=np.int64)
    rows = np.arange(G)[:, None]
    Invs[rows, Ts] = np.broadcast_to(x[None, :], (G, G))
    return G, Ts, Invs


def _set_dart(nbr, k, G, Ts, Invs, l, i, j, s):
    nbr[l, i * G:(i + 1) * G] = (k + j) * G + Ts[s]
    nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Invs[s]


def _reach(k, G, D, nbr, d):
    N = nbr.shape[1]
    reach = np.zeros(N, dtype=np.int64)
    for b in range(2 * k):
        reach[b * G] = 1 << b
    for _ in range(D):
        new = reach.copy()
        for l in range(d):
            new |= reach[nbr[l]]
        if np.array_equal(new, reach):
            break
        reach = new
    return reach


def _unreached(k, N, reach):
    return 2 * k * N - int(_POP[reach].sum())


def _search(d, D, k, G, Ts, Invs, rng, deadline, iters):
    N = 2 * k * G
    full = (1 << (2 * k)) - 1
    layers = [rng.sample(range(k), k) for _ in range(d)]
    S = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    nbr = np.empty((d, N), dtype=np.int64)
    for l in range(d):
        for i in range(k):
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], S[l][i])

    def dupcount():
        keys = [(i, layers[l][i], S[l][i]) for l in range(d) for i in range(k)]
        return len(keys) - len(set(keys))

    reach = _reach(k, G, D, nbr, d)
    cost = _unreached(k, N, reach) + _PENALTY * dupcount()
    c0 = float(max(cost, 1))

    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        temp = max(0.5, 0.01 * c0 * (1.0 - t / iters))
        x = rng.random()

        if k >= 2 and x < 0.25:
            l = rng.randrange(d)
            i1, i2 = rng.sample(range(k), 2)
            layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
            _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
            _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            r2 = _reach(k, G, D, nbr, d)
            c2 = _unreached(k, N, r2) + _PENALTY * dupcount()
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost, reach = c2, r2
            else:
                layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
                _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
                _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            continue

        bad = np.flatnonzero(reach != full) if rng.random() < 0.4 else None
        if bad is not None and bad.size:
            u = int(bad[rng.randrange(bad.size)])
            block = u // G
            l = rng.randrange(d)
            if block < k:
                i = block
            else:
                i = layers[l].index(block - k)
        else:
            l = rng.randrange(d)
            i = rng.randrange(k)

        old = S[l][i]
        new = rng.randrange(G)
        if new == old:
            continue
        S[l][i] = new
        _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], new)
        r2 = _reach(k, G, D, nbr, d)
        c2 = _unreached(k, N, r2) + _PENALTY * dupcount()
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost, reach = c2, r2
        else:
            S[l][i] = old
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], old)

    if cost != 0:
        return None
    edges = set()
    for u in range(k * G):
        for v in nbr[:, u]:
            edges.add((u, int(v)))
    return N, sorted(edges)


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions (calibration-style cases return immediately).
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # BOLD NEW FAMILY: Haar graphs over PSL(2, p), tried first with ~70% of the budget.
    if D >= 3 and d >= 3:
        moore = 2 * sum((d - 1) ** i for i in range(D))
        lower = max(best_n + 1, 0.4 * moore)
        cands = []
        for p in (5, 7, 11, 13, 17, 19, 23):
            g = p * (p * p - 1) // 2
            if lower < 2 * g <= moore:
                cands.append(p)
        cands.sort(reverse=True)  # largest group first
        psl_deadline = start + 0.7 * budget
        for pos, p in enumerate(cands):
            now = time.monotonic()
            if now >= psl_deadline:
                break
            slice_end = now + (psl_deadline - now) / (len(cands) - pos)
            P = _PSL(p)
            S = _haar_search(P, d, D, rng, slice_end)
            if S is not None:
                n_e, e_list = _haar_graph_from(P, S)
                consider(n_e, e_list)
                break

    # Parent family: bandit over base sizes k with bi-Cayley lifts for the rest of the budget.
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while time.monotonic() < deadline:
        k = pick_k()
        base = best_n // (2 * k)
        target = max(2, base + 1 + rng.randrange(0, max(2, base // 8 + 1)))
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        G, Ts, Invs = _semidirect_tables(m, k2, r)
        if 2 * k * G <= best_n:
            continue
        trials[k] += 1
        res = _search(d, D, k, G, Ts, Invs, rng, deadline, 4000)
        if res is not None:
            wins[k] += 1
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
