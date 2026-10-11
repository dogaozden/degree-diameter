import itertools
import math
import random
import time

import numpy as np

import lib


def _moore(d, D):
    """Moore-type upper bound for bipartite graphs with max degree d and diameter D."""
    if D == 0 or d == 0:
        return 1
    if d == 1:
        return min(2, D + 1)
    if d == 2:
        return 2 * D
    return 2 * sum((d - 1) ** i for i in range(D))


# ----------------------------------------------------------------------------
# Exact / safe families (unchanged from the parent).
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
# NEW family: bipartite Haar-type lifts over PSL(2,p) / PGL(2,p).
#
# Vertices A_g = g, B_h = |G| + h. Connection set S (d distinct group elements):
# A_g ~ B_{g*s} for s in S. Left multiplication is an automorphism, so the
# graph is transitive on each side and the diameter condition only needs
# BFS from one A-vertex and one B-vertex. Search is simulated annealing over S.
# ----------------------------------------------------------------------------

def _mat_mul(x, y, p):
    a, b, c, d = x
    e, f, g, h = y
    return ((a * e + b * g) % p, (a * f + b * h) % p,
            (c * e + d * g) % p, (c * f + d * h) % p)


class _Group:
    """PSL(2,p) (special=True) or PGL(2,p) (special=False) as canonical 2x2 matrices mod p."""

    def __init__(self, p, special):
        self.p = p
        self.special = special
        elems = set()
        for t in itertools.product(range(p), repeat=4):
            det = (t[0] * t[3] - t[1] * t[2]) % p
            ok = (det == 1) if special else (det != 0)
            if ok:
                elems.add(self._canon(t))
        self.elems = sorted(elems)
        self.index = {t: i for i, t in enumerate(self.elems)}
        self.G = len(self.elems)
        self.cache = {}

    def _canon(self, t):
        if self.special:
            neg = tuple((-x) % self.p for x in t)
            return min(t, neg)
        for x in t:
            if x:
                inv = pow(x, self.p - 2, self.p)
                return tuple((y * inv) % self.p for y in t)
        return t

    def perm(self, s):
        """perm[g] = index of g * elems[s] (right multiplication), cached."""
        pr = self.cache.get(s)
        if pr is None:
            sm = self.elems[s]
            pr = np.array([self.index[self._canon(_mat_mul(x, sm, self.p))]
                           for x in self.elems], dtype=np.int64)
            self.cache[s] = pr
        return pr


def _group_candidates():
    out = []
    for p in (5, 7, 11, 13):
        out.append((p * (p * p - 1) // 2, p, True))   # PSL(2,p)
        out.append((p * (p * p - 1), p, False))       # PGL(2,p)
    return out


def _haar_cost(nbr, G, D):
    """Unreached (source, vertex) pairs from one A-vertex and one B-vertex."""
    N = nbr.shape[0]
    cost = 0
    for src in (0, G):
        vis = np.zeros(N, dtype=bool)
        vis[src] = True
        frontier = np.array([src], dtype=np.int64)
        for _ in range(D):
            nb = nbr[frontier].ravel()
            nb = nb[~vis[nb]]
            if nb.size == 0:
                break
            nb = np.unique(nb)
            vis[nb] = True
            frontier = nb
        cost += N - int(vis.sum())
    return cost


def _anneal_haar(H, d, D, rng, deadline, iters):
    """Annealing over d-element connection sets in H. Returns the set S or None."""
    G = H.G
    S = rng.sample(range(G), d)
    nbr = np.empty((2 * G, d), dtype=np.int64)
    arG = np.arange(G, dtype=np.int64)

    def setcol(j):
        pr = H.perm(S[j])
        nbr[:G, j] = G + pr
        iv = np.empty(G, dtype=np.int64)
        iv[pr] = arG
        nbr[G:, j] = iv

    for j in range(d):
        setcol(j)
    cost = _haar_cost(nbr, G, D)
    c0 = float(max(cost, 1))
    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        j = rng.randrange(d)
        new = rng.randrange(G)
        if new in S:
            continue
        old = S[j]
        S[j] = new
        setcol(j)
        c2 = _haar_cost(nbr, G, D)
        temp = max(0.3, 0.05 * c0 * (1.0 - t / iters))
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost = c2
        else:
            S[j] = old
            setcol(j)
    return S if cost == 0 else None


def _haar_edges(H, S):
    G = H.G
    edges = []
    for s in S:
        pr = H.perm(s)
        for g in range(G):
            edges.append((g, G + int(pr[g])))
    return edges


# ----------------------------------------------------------------------------
# Parent's bi-Cayley lift search over Z_m x| Z_k2 (kept as the second phase).
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_KS = (1, 2, 3, 4)
_SWAP_PROB = 0.3
_STRUCT_PROB = 0.5


def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, -(-target // k2))
        if k2 == 1:
            r = 1
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


def _structured_init(d, k, G, Ts, rng):
    x = rng.randrange(1, G)
    powers = [0]
    for _ in range(d):
        powers.append(int(Ts[x, powers[-1]]))
    ys = [rng.randrange(G) for _ in range(k)]
    layers = [[(i + l) % k for i in range(k)] for l in range(d)]
    S = [[int(Ts[ys[i], powers[l + 1]]) for i in range(k)] for l in range(d)]
    return layers, S


def _random_init(d, k, G, rng):
    layers = [rng.sample(range(k), k) for _ in range(d)]
    S = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    return layers, S


def _set_dart(nbr, k, G, Ts, Invs, l, i, j, s):
    nbr[l, i * G:(i + 1) * G] = (k + j) * G + Ts[s]
    nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Invs[s]


def _cost(k, G, D, nbr):
    d, N = nbr.shape
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
    return 2 * k * N - int(_POP[reach].sum())


def _search(d, D, k, G, Ts, Invs, rng, deadline, iters):
    N = 2 * k * G
    if rng.random() < _STRUCT_PROB:
        layers, S = _structured_init(d, k, G, Ts, rng)
    else:
        layers, S = _random_init(d, k, G, rng)
    nbr = np.empty((d, N), dtype=np.int64)
    for l in range(d):
        for i in range(k):
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], S[l][i])

    def dupcount():
        keys = [(i, layers[l][i], S[l][i]) for l in range(d) for i in range(k)]
        return len(keys) - len(set(keys))

    cost = _cost(k, G, D, nbr) + _PENALTY * dupcount()
    c0 = float(max(cost, 1))

    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        temp = max(0.5, 0.01 * c0 * (1.0 - t / iters))
        l = rng.randrange(d)

        if k > 1 and rng.random() < _SWAP_PROB:
            i1, i2 = rng.sample(range(k), 2)
            layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
            _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
            _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            c2 = _cost(k, G, D, nbr) + _PENALTY * dupcount()
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost = c2
            else:
                layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
                _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
                _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            continue

        i = rng.randrange(k)
        old = S[l][i]
        new = rng.randrange(G)
        if new == old:
            continue
        S[l][i] = new
        _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], new)
        c2 = _cost(k, G, D, nbr) + _PENALTY * dupcount()
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost = c2
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

    # Phase 1 (bold new family): Haar lifts over PSL/PGL(2,p), annealed connection sets.
    moore = _moore(d, D)
    phase1_end = start + 0.6 * budget
    cands = [c for c in _group_candidates()
             if c[0] >= d and 2 * c[0] <= moore]
    cands.sort(reverse=True)
    groups = {}
    while time.monotonic() < phase1_end:
        live = [c for c in cands if 2 * c[0] > best_n]
        if not live:
            break
        if rng.random() < 0.5:
            c = live[0]
        else:
            c = rng.choice(live)
        key = (c[1], c[2])
        if key not in groups:
            groups[key] = _Group(c[1], c[2])
        H = groups[key]
        S = _anneal_haar(H, d, D, rng, phase1_end, 30000)
        if S is not None:
            consider(2 * H.G, _haar_edges(H, S))

    # Phase 2: parent's bi-Cayley semidirect-product search for the remaining time.
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
