import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe baseline families (always checked with lib.is_valid before use).
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
# Bi-Cayley lifts over groups Z_m x| Z_k2 (includes direct products and dihedral).
#
# A-block i has vertices i*G + g, B-block j has vertices (k+j)*G + h.
# Layer l pairs A-block i with B-block layers[l][i] through voltage S[l][i]:
#     A_{i,g} ~ B_{p, g*s}.
# Left multiplication is a graph automorphism, so reachability from the identity
# representative of each block decides the diameter.
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_KS = (1, 2, 3, 4, 6)
_TENURE = 6
_CANDS = 6
_STALL = 300
_ITER = 1500
_GMAX = 3000


def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, -(-target // k2))
        if k2 == 1:
            return m, 1, 1
        u = rng.random()
        if u < 0.2:
            r = 1                          # direct product Z_m x Z_k2
        elif u < 0.4 and k2 == 2:
            r = m - 1                      # dihedral-type
        else:
            r = None
            for _ in range(60):
                c = rng.randrange(2, m) if m > 2 else 1
                if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                    r = c
                    break
            if r is None:
                continue
        if math.gcd(r, m) != 1 or pow(r, k2, m) != 1 % m:
            continue
        return m, k2, r
    return None


def _semidirect_tables(m, k2, r):
    """Return (G, Ts, Invs): Ts[s, g] = g*s and Invs[s, h] = h*s^-1 for Z_m x| Z_k2."""
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
    """Write layer l's neighbours for A-block i and B-block j with voltage s."""
    nbr[l, i * G:(i + 1) * G] = (k + j) * G + Ts[s]
    nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Invs[s]


def _reach(k, G, D, nbr, d):
    """Bitmask per vertex: bit b is set when block b's identity is within distance D."""
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
    """Number of unreached (representative, vertex) pairs."""
    return 2 * k * N - int(_POP[reach].sum())


class _Lift:
    """Mutable lift state: layers, voltages and the neighbour table."""

    def __init__(self, d, D, k, G, Ts, Invs, rng):
        self.d, self.D, self.k, self.G = d, D, k, G
        self.Ts, self.Invs = Ts, Invs
        self.N = 2 * k * G
        self.full = (1 << (2 * k)) - 1
        self.layers = [rng.sample(range(k), k) for _ in range(d)]
        self.S = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
        self.nbr = np.empty((d, self.N), dtype=np.int64)
        for l in range(d):
            for i in range(k):
                _set_dart(self.nbr, k, G, Ts, Invs, l, i, self.layers[l][i], self.S[l][i])

    def cost(self):
        reach = _reach(self.k, self.G, self.D, self.nbr, self.d)
        keys = [(i, self.layers[l][i], self.S[l][i]) for l in range(self.d) for i in range(self.k)]
        dup = len(keys) - len(set(keys))
        return _unreached(self.k, self.N, reach) + _PENALTY * dup, reach

    def set_s(self, l, i, s):
        self.S[l][i] = s
        _set_dart(self.nbr, self.k, self.G, self.Ts, self.Invs, l, i, self.layers[l][i], s)

    def swap(self, l, i1, i2):
        L = self.layers[l]
        L[i1], L[i2] = L[i2], L[i1]
        _set_dart(self.nbr, self.k, self.G, self.Ts, self.Invs, l, i1, L[i1], self.S[l][i1])
        _set_dart(self.nbr, self.k, self.G, self.Ts, self.Invs, l, i2, L[i2], self.S[l][i2])

    def edges(self):
        es = set()
        for u in range(self.k * self.G):
            for v in self.nbr[:, u]:
                es.add((u, int(v)))
        return self.N, sorted(es)


def _gen_move(st, rng, reach, full):
    """Propose a move. Voltage moves are biased towards defects when reach is given."""
    d, k, G = st.d, st.k, st.G
    if k >= 2 and rng.random() < 0.2:
        l = rng.randrange(d)
        i1, i2 = rng.sample(range(k), 2)
        return ("P", l, i1, i2)
    l = rng.randrange(d)
    i = rng.randrange(k)
    if reach is not None and rng.random() < 0.5:
        bad = np.flatnonzero(reach != full)
        if bad.size:
            u = int(bad[rng.randrange(bad.size)])
            block = u // G
            if block < k:
                i = block
            else:
                i = st.layers[l].index(block - k)
    new = rng.randrange(G)
    old = st.S[l][i]
    if new == old:
        return None
    return ("S", l, i, new, old)


def _apply(st, mv):
    if mv[0] == "S":
        st.set_s(mv[1], mv[2], mv[3])
    else:
        st.swap(mv[1], mv[2], mv[3])


def _revert(st, mv):
    if mv[0] == "S":
        st.set_s(mv[1], mv[2], mv[4])
    else:
        st.swap(mv[1], mv[2], mv[3])


def _search(d, D, k, G, Ts, Invs, rng, deadline, max_iter):
    """Tabu search with defect-guided moves and perturbation restarts. Returns (n, edges) or None."""
    st = _Lift(d, D, k, G, Ts, Invs, rng)
    full = st.full
    cur, reach = st.cost()
    run_best = cur
    last = 0
    it = 0
    tabu = {}
    while cur > 0 and it < max_iter and time.monotonic() < deadline:
        it += 1
        if it - last > _STALL:
            for _ in range(3):
                mv = _gen_move(st, rng, None, full)
                if mv is not None:
                    _apply(st, mv)
            cur, reach = st.cost()
            run_best = cur
            last = it
            tabu.clear()
            continue
        best_c = None
        for _ in range(_CANDS):
            mv = _gen_move(st, rng, reach, full)
            if mv is None:
                continue
            key = (mv[0], mv[1], mv[2])
            _apply(st, mv)
            c, r = st.cost()
            _revert(st, mv)
            if tabu.get(key, 0) > it and c >= run_best:
                continue
            if best_c is None or c < best_c[0]:
                best_c = (c, r, mv, key)
        if best_c is None:
            continue
        c, r, mv, key = best_c
        _apply(st, mv)
        cur, reach = c, r
        tabu[key] = it + _TENURE
        if cur < run_best:
            run_best = cur
            last = it
    if cur != 0:
        return None
    return st.edges()


# ----------------------------------------------------------------------------
# Bipartition colouring and redundancy-aware pair insertion.
# ----------------------------------------------------------------------------

def _two_color(n, edges):
    """Return a proper 2-colouring (list of 0/1), or None if the graph is not bipartite."""
    adj = lib.adjacency(n, edges)
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
                elif color[v] == color[u]:
                    return None
    return color


def _edge_slack(n, edges, R):
    """Per-edge redundancy: popcount of (ball_R(u) & ball_R(v))."""
    balls = lib._balls(n, edges, max(1, R))
    return [(balls[u] & balls[v]).bit_count() for u, v in edges]


def _extend_redundant(n, edges, d, D, rng, deadline, max_fails=60):
    """Grow the order by 2 per accepted pair insertion, preferring high-redundancy edges."""
    if d < 1 or not edges:
        return n, edges
    color = _two_color(n, edges)
    if color is None:
        return n, edges
    edges = list(edges)
    color = list(color)
    fails = 0
    while time.monotonic() < deadline and fails < max_fails:
        slack = _edge_slack(n, edges, D - 1)
        keys = [slack[t] * (0.8 + 0.4 * rng.random()) for t in range(len(edges))]
        order = sorted(range(len(edges)), key=lambda t: -keys[t])
        chosen = []
        used_a, used_b = set(), set()
        for t in order:
            if len(chosen) == d - 1:
                break
            u, v = edges[t]
            a, b = (u, v) if color[u] == 0 else (v, u)
            if a in used_a or b in used_b:
                continue
            chosen.append(t)
            used_a.add(a)
            used_b.add(b)
        if len(chosen) < d - 1:
            break
        x, y = n, n + 1
        cs = set(chosen)
        cand = [e for t, e in enumerate(edges) if t not in cs]
        for t in chosen:
            u, v = edges[t]
            a, b = (u, v) if color[u] == 0 else (v, u)
            cand.append((x, b))
            cand.append((y, a))
        cand.append((x, y))
        if lib.is_valid(n + 2, cand, d, D):
            edges = cand
            n += 2
            color.extend([0, 1])
            fails = 0
        else:
            fails += 1
    return n, edges


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.90 * time_limit, time_limit - 5.0))
    deadline = start + budget
    search_deadline = start + 0.80 * budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

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

    if D >= 4 and time.monotonic() < search_deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    try:
        trials = {k: 0 for k in _KS}
        wins = {k: 0 for k in _KS}

        def pick_k():
            if rng.random() < 0.2:
                return rng.choice(_KS)
            return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

        while time.monotonic() < search_deadline:
            k = pick_k()
            base = best_n // (2 * k)
            target = max(2, base + 1 + rng.randrange(0, max(2, base // 6 + 1)))
            g = _sample_group(target, rng)
            if g is None:
                continue
            m, k2, r = g
            if m * k2 > _GMAX:
                continue
            G, Ts, Invs = _semidirect_tables(m, k2, r)
            if 2 * k * G <= best_n:
                continue
            trials[k] += 1
            res = _search(d, D, k, G, Ts, Invs, rng, search_deadline, _ITER)
            if res is not None:
                wins[k] += 1
                consider(res[0], res[1])
    except Exception:
        pass

    try:
        n2, e2 = _extend_redundant(best_n, best[1], d, D, rng, deadline)
        if n2 > best_n:
            consider(n2, e2)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
