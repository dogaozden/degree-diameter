import itertools
import math
import random
import time
from math import gcd

import numpy as np

import lib

N_CAP = 6000            # hard cap on vertex count
ITERS = 1500            # annealing iterations per attempt
S_CHOICES = (1, 2, 3, 4, 5, 6)   # base vertices per side
K_CHOICES = (1, 2, 3, 4)         # group Z_m x| Z_k orders (k = 1 is cyclic)
MAX_GQ_Q = 9            # W(q) construction is O(P^2); keep q small for speed


# ----------------------------------------------------------------------------
# Base constructions
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q), q the largest prime power with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q)."""
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

    edges = [(p, P + j) for j, L in enumerate(lines) for p in L]
    return 2 * P, edges


def _best_gq(d):
    """W(q) incidence graph for the largest prime power q with q + 1 <= d (diameter 4)."""
    for q in range(d - 1, 1, -1):
        if q <= MAX_GQ_Q and lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Growth: spare-degree saturation and cover-based vertex extension.
# Both preserve bipartiteness and diameter <= D.
# ----------------------------------------------------------------------------

def _balls_radius(n, adj, r):
    ball = [1 << v for v in range(n)]
    for _ in range(r):
        new = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new.append(x)
        ball = new
    return ball


def _bipartition(n, adj):
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
    return color


def _extend_cover(n, edges, d, D, deadline):
    if D < 2:
        return n, edges
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)

    while time.monotonic() < deadline:
        ball = _balls_radius(n, adj, D - 1)
        full = (1 << n) - 1
        added = False
        for c in (0, 1):
            cands = [s for s in range(n) if color[s] == c and deg[s] < d]
            if not cands:
                continue
            covered = 0
            chosen = []
            pool = set(cands)
            while covered != full and len(chosen) < d and pool:
                best_s, best_g = None, 0
                for s in pool:
                    g = (ball[s] & ~covered).bit_count()
                    if g > best_g:
                        best_g, best_s = g, s
                if best_s is None:
                    break
                chosen.append(best_s)
                covered |= ball[best_s]
                pool.discard(best_s)
            if covered == full and chosen:
                v = n
                n += 1
                color.append(1 - c)
                adj.append([])
                deg.append(0)
                for s in chosen:
                    edges.append((s, v))
                    adj[s].append(v)
                    adj[v].append(s)
                    deg[s] += 1
                    deg[v] += 1
                added = True
                break
        if not added:
            break
    return n, edges


def _saturate_edges(n, edges, d, rng):
    edges = list(edges)
    adj = [[] for _ in range(n)]
    existing = set()
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
        existing.add((min(u, v), max(u, v)))
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    left = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in left for b in right
             if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return edges


def _grow(n, edges, d, D, deadline, rng):
    cur_n, cur_e = n, list(edges)
    for _ in range(8):
        if time.monotonic() >= deadline:
            break
        cur_e = _saturate_edges(cur_n, cur_e, d, rng)
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline)
        if n2 == cur_n:
            break
        cur_n, cur_e = n2, e2
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# Voltage lifts over Z_m or the semidirect products Z_m x| Z_k.
# Group element x = a*k + b, product (a,b)(c,d) = (a + r^b c, b + d), r^k = 1 mod m.
# Left multiplication is an automorphism of the lift, so one source per fibre
# (the identity) suffices for the distance check.
# ----------------------------------------------------------------------------

def _pick_r(kg, m):
    if m < 2:
        return None
    if kg == 1:
        return 1
    if kg in (2, 4):
        return m - 1          # (-1)^k = 1 for even k
    if kg == 3:
        for r in range(2, m):
            if gcd(r, m) == 1 and pow(r, 3, m) == 1:
                return r
        return None
    return None


class _Group:
    def __init__(self, m, kg, r):
        self.m, self.k, self.r = m, kg, r
        self.G = m * kg
        self.pw = np.array([pow(r, b, m) for b in range(kg)], dtype=np.int64)
        self.xs = np.arange(self.G, dtype=np.int64)
        self.a = self.xs // kg
        self.b = self.xs % kg

    def mul_all(self, g):
        """Vector of x * g over all group elements x."""
        c, dd = divmod(g, self.k)
        return ((self.a + self.pw[self.b] * c) % self.m) * self.k + (self.b + dd) % self.k

    def inv(self, g):
        a, b = divmod(g, self.k)
        nb = (-b) % self.k
        return ((-int(self.pw[nb]) * a) % self.m) * self.k + nb


def _neighbors(grp, P, Pinv, V, s, d):
    """Neighbour table of the lift. A-fibre i, element x joins B-fibre P[k,i] at x*g."""
    G = grp.G
    nbr = np.empty((2 * s * G, d), dtype=np.int64)
    for k in range(d):
        for i in range(s):
            j = int(P[k, i])
            nbr[i * G:(i + 1) * G, k] = s * G + j * G + grp.mul_all(int(V[k, i]))
        for j in range(s):
            i = int(Pinv[k, j])
            nbr[(s + j) * G:(s + j + 1) * G, k] = i * G + grp.mul_all(grp.inv(int(V[k, i])))
    return nbr


def _cost(nbr, sources, D, n):
    """Number of (source, vertex) pairs not within distance D. Zero iff valid."""
    S = len(sources)
    R = np.zeros((S, n), dtype=bool)
    R[np.arange(S), sources] = True
    for _ in range(D):
        M = R.copy()
        for k in range(nbr.shape[1]):
            M |= R[:, nbr[:, k]]
        if np.array_equal(M, R):
            break
        R = M
    return int(S * n - np.count_nonzero(R))


def _swap(P, Pinv, k, a, b):
    P[k, a], P[k, b] = P[k, b], P[k, a]
    Pinv[k, P[k, a]] = a
    Pinv[k, P[k, b]] = b


def _anneal(s, grp, d, D, rng, deadline):
    """Simulated annealing over permutations and voltages. Returns (P, V) or None."""
    G = grp.G
    n = 2 * s * G
    P = np.array([rng.sample(range(s), s) for _ in range(d)], dtype=np.int64)
    Pinv = np.zeros_like(P)
    for k in range(d):
        for i in range(s):
            Pinv[k, P[k, i]] = i
    V = np.array([[rng.randrange(G) for _ in range(s)] for _ in range(d)], dtype=np.int64)
    sources = [i * G for i in range(2 * s)]
    nbr = _neighbors(grp, P, Pinv, V, s, d)
    cur = _cost(nbr, sources, D, n)
    for it in range(ITERS):
        if cur == 0 or time.monotonic() > deadline:
            break
        temp = 2.0 * (1.0 - it / ITERS) + 0.05
        if s == 1 or rng.random() < 0.7:
            k, i = rng.randrange(d), rng.randrange(s)
            old = int(V[k, i])
            new_v = rng.randrange(G)
            if new_v == old:
                continue
            V[k, i] = new_v
            cand = _neighbors(grp, P, Pinv, V, s, d)
            c = _cost(cand, sources, D, n)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur, nbr = c, cand
            else:
                V[k, i] = old
        else:
            k = rng.randrange(d)
            a, b = rng.sample(range(s), 2)
            _swap(P, Pinv, k, a, b)
            cand = _neighbors(grp, P, Pinv, V, s, d)
            c = _cost(cand, sources, D, n)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur, nbr = c, cand
            else:
                _swap(P, Pinv, k, a, b)
    if cur == 0:
        return P.copy(), V.copy()
    return None


def _graph(grp, s, P, V, d):
    Pinv = np.zeros_like(P)
    for k in range(d):
        for i in range(s):
            Pinv[k, P[k, i]] = i
    nbr = _neighbors(grp, P, Pinv, V, s, d)
    G = grp.G
    edges = set()
    for x in range(s * G):
        for y in nbr[x].tolist():
            edges.add((x, y))
    return 2 * s * G, sorted(edges)


def _next_m(st, s, kg, cap):
    """Next group size to try for a (s, kg) key, from its bisection state."""
    mmax = cap // (2 * s * kg)
    if mmax < 2:
        return None
    lo, hi = st["lo"], st["hi"]
    if hi is None:
        if lo >= mmax:
            return None
        m = max(lo + 1, 2, (lo * 3) // 2 + 1)
        return min(m, mmax)
    if hi - lo <= 1:
        return None
    return (lo + hi) // 2


def _lift_search(d, D, rng, deadline, cap, consider):
    keys = [(s, kg) for s in S_CHOICES for kg in K_CHOICES]
    states = {key: {"lo": 0, "hi": None, "dead": False} for key in keys}
    while time.monotonic() < deadline:
        live = [key for key in keys if not states[key]["dead"]]
        if not live:
            break
        s, kg = rng.choice(live)
        st = states[(s, kg)]
        m = _next_m(st, s, kg, cap)
        if m is None:
            st["dead"] = True
            continue
        r = _pick_r(kg, m)
        if r is None:
            st["hi"] = m
            continue
        grp = _Group(m, kg, r)
        res = _anneal(s, grp, d, D, rng, deadline)
        if res is not None:
            st["lo"] = m
            n, e = _graph(grp, s, res[0], res[1], d)
            consider(n, e)
        else:
            st["hi"] = m


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = max(0.5, 0.8 * time_limit - 1.0)
    deadline = start + total
    rng = random.Random(seed)

    # Trivial cases.
    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D                     # even cycle C_{2D}: diameter D, bipartite
        return n, [(i, (i + 1) % n) for i in range(n)]

    best = [lib.haar_graph(d, range(d))]   # K_{d,d}, diameter 2
    if D == 2:
        return best[0]
    cap = min(N_CAP, lib._moore_bound(d, D))

    def consider(n, e):
        if n > best[0][0] and lib.is_valid(n, e, d, D):
            best[0] = (n, e)

    # Projective plane (diameter 3, valid for any D >= 3).
    pg = _best_pg(d)
    if pg is not None:
        consider(pg[0], pg[1])
        if D == 3 and lib.is_prime_power(d - 1):
            return best[0]            # exact Moore-type construction
        n2, e2 = _grow(pg[0], pg[1], d, D, start + 0.35 * total, rng)
        consider(n2, e2)

    # Generalized quadrangle W(q) (diameter 4, valid for D >= 4).
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            n2, e2 = _grow(gq[0], gq[1], d, D, start + 0.5 * total, rng)
            consider(n2, e2)

    # Voltage lifts over Z_m and Z_m x| Z_k for the remaining budget.
    _lift_search(d, D, rng, deadline, cap, consider)

    return best[0]
