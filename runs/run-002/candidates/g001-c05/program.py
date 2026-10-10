import itertools
import math
import random
import time

import numpy as np

import lib

N_CAP = 6000                  # hard cap on vertex count
ITERS = 6000                  # annealing iterations per attempt
S_LIST = (1, 2, 3, 4, 5, 6)   # number of base vertices per side (cyclic lifts)
DIHEDRAL_S = (1, 2, 3)        # base sizes tried with the semidirect group Z_m x| Z_2
GQ_Q_MAX = 9                  # largest q for which W(q) is built (pair loop is O(P^2))
RETRIES = 2                   # annealing attempts per candidate lift size
TIME_FRAC = 0.8               # fraction of time_limit used for search
POST_FRAC = 0.85              # fraction of time_limit after which nothing new starts
POST_EXTEND_SLICE = 1.5       # seconds given to greedy growth of the best lift


# ---------------------------------------------------------------- shared helpers

def _two_colour(n, edges):
    """Return a proper 2-colouring (0/1 per vertex) of a bipartite graph, component by component."""
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
    return color


def _greedy_cover(cand, sets, target, budget):
    """Pick at most `budget` candidates whose `sets` bitmasks jointly cover `target`.

    Returns the chosen list (possibly empty if target is already covered), or None.
    """
    cand = list(cand)
    covered = 0
    chosen = []
    while (target & ~covered) and len(chosen) < budget and cand:
        best_u, best_gain = -1, 0
        for u in cand:
            g = (sets[u] & target & ~covered).bit_count()
            if g > best_gain:
                best_u, best_gain = u, g
        if best_u < 0:
            break
        chosen.append(best_u)
        covered |= sets[best_u]
        cand.remove(best_u)
    if target & ~covered:
        return None
    return chosen


def _extend(n, edges, d, D, rng, deadline):
    """Greedily add new vertices, each attached to a set cover of the current graph.

    A new vertex x with neighbour set N is within distance D of every old vertex iff the
    radius-(D-1) balls of N cover all vertices. Old pairs only get closer, so the diameter
    bound is preserved.
    """
    edges = list(edges)
    if D < 2 or n == 0:
        return n, edges
    color = _two_colour(n, edges)
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1

    while time.monotonic() < deadline:
        full = (1 << n) - 1
        balls = lib._balls(n, edges, D - 1)
        grown = False
        order = [0, 1] if rng.random() < 0.5 else [1, 0]
        for c in order:
            cand = [u for u in range(n) if color[u] == 1 - c and deg[u] < d]
            rng.shuffle(cand)
            covered, chosen = 0, []
            while covered != full and len(chosen) < d and cand:
                best_u, best_gain = -1, 0
                for u in cand:
                    g = (balls[u] & ~covered).bit_count()
                    if g > best_gain:
                        best_u, best_gain = u, g
                if best_u < 0:
                    break
                chosen.append(best_u)
                covered |= balls[best_u]
                cand.remove(best_u)
            if covered == full and chosen:
                x = n
                n += 1
                color.append(c)
                deg.append(len(chosen))
                for u in chosen:
                    edges.append((u, x))
                    deg[u] += 1
                grown = True
                break
        if not grown:
            break
    return n, edges


def _pair_extend(n, edges, d, D, rng, deadline):
    """Add two adjacent new vertices x (side c) and y (side 1-c) at once.

    x gets neighbours N (old vertices on side 1-c) whose radius-(D-1) balls cover everything.
    y gets neighbours M (old vertices on side c) chosen so that
        balls_{D-1}(M) covers everything not already within D-2 of N,
    which is exactly the condition for y to reach each old vertex, either directly
    through M or through x and N (length 2 + dist(N, v)).
    Old-to-old distances only shrink, so the diameter bound is preserved.
    """
    edges = list(edges)
    if D < 3 or n == 0 or d < 2:
        return n, edges
    color = _two_colour(n, edges)
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1

    while time.monotonic() < deadline:
        full = (1 << n) - 1
        b1 = lib._balls(n, edges, D - 1)
        b2 = lib._balls(n, edges, D - 2)
        placed = False
        order = [0, 1] if rng.random() < 0.5 else [1, 0]
        for c in order:
            side_other = [u for u in range(n) if color[u] == 1 - c and deg[u] < d]
            side_c = [u for u in range(n) if color[u] == c and deg[u] < d]
            N = _greedy_cover(side_other, b1, full, d - 1)
            if not N:
                continue
            b2N = 0
            for u in N:
                b2N |= b2[u]
            M = _greedy_cover(side_c, b1, full & ~b2N, d - 1)
            if M is None:
                continue
            x, y = n, n + 1
            n += 2
            color.append(c)
            color.append(1 - c)
            deg.append(len(N) + 1)
            deg.append(len(M) + 1)
            for u in N:
                edges.append((u, x))
                deg[u] += 1
            for u in M:
                edges.append((u, y))
                deg[u] += 1
            edges.append((x, y))
            placed = True
            break
        if not placed:
            break
    return n, edges


def _grow(n, edges, d, D, rng, deadline):
    """Alternate single-vertex and paired greedy extension until neither adds anything."""
    prev = -1
    while n != prev and time.monotonic() < deadline:
        prev = n
        n, edges = _extend(n, edges, d, D, rng, deadline)
        n, edges = _pair_extend(n, edges, d, D, rng, deadline)
    return n, edges


def _augment(n, edges, d, seed):
    """Add edges between opposite colour classes using spare degree.

    Extra edges only shorten distances and keep the graph bipartite, so the diameter
    bound and bipartiteness are preserved.
    """
    rng = random.Random(seed + 7)
    color = _two_colour(n, edges)
    deg = [0] * n
    adj = [set() for _ in range(n)]
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
        adj[u].add(v)
        adj[v].add(u)
    side0 = [u for u in range(n) if color[u] == 0]
    side1 = [v for v in range(n) if color[v] == 1]
    new_edges = list(edges)
    for _ in range(3):
        us = [u for u in side0 if deg[u] < d]
        rng.shuffle(us)
        for u in us:
            if deg[u] >= d:
                continue
            cands = [v for v in side1 if deg[v] < d and v not in adj[u]]
            if not cands:
                continue
            v = rng.choice(cands)
            adj[u].add(v)
            adj[v].add(u)
            deg[u] += 1
            deg[v] += 1
            new_edges.append((u, v))
    return n, new_edges


def _finish(cands, d, D):
    """Return the largest candidate that passes lib.is_valid, else K_{d,d}."""
    for n, e in sorted(cands, key=lambda c: -c[0]):
        if lib.is_valid(n, e, d, D):
            return n, e
    return lib.haar_graph(d, range(d))


# ---------------------------------------------------------------- D = 3 : projective plane

def _pg_base(d):
    """Incidence graph of PG(2,q), q the largest prime power <= d-1."""
    q = d - 1
    while q >= 2 and not lib.is_prime_power(q):
        q -= 1
    if q < 2:
        return None
    return lib.projective_plane_incidence(q)


# ---------------------------------------------------------------- D >= 4 : generalized quadrangle

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q).

    Degree q + 1, diameter 4, order 2(q+1)(q^2+1).
    """
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
    """W(q) for the largest prime power q with q <= d-1 and q <= GQ_Q_MAX."""
    for q in range(min(d - 1, GQ_Q_MAX), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ---------------------------------------------------------------- Haar graphs (hill-climb)

def _search_haar(d, D, m, rng, deadline, iters):
    """Hill-climb a connection set S (|S| = d, containing 0) in Z_m so the Haar graph has diameter <= D."""
    others = list(range(1, m))
    if len(others) < d - 1:
        return None

    def cost(S):
        n, edges = lib.haar_graph(m, S)
        return lib.bad_pairs(n, edges, D)

    S = [0] + rng.sample(others, d - 1)
    c = cost(S)
    for _ in range(iters):
        if c == 0:
            return S
        if time.monotonic() >= deadline:
            break
        cand = [x for x in others if x not in S]
        if not cand:
            break
        i = rng.randrange(1, d)
        T = S[:]
        T[i] = rng.choice(cand)
        ct = cost(T)
        if ct <= c:
            S, c = T, ct
    return S if c == 0 else None


# ---------------------------------------------------------------- groups for lifts

class _Grp:
    """Semidirect product Z_m x|_r Z_k, element (a, b) coded as a*k+b.

    k = 1 gives the cyclic group Z_m. Right multiplication by a fixed element is
    vectorised, which is all the lift construction needs.
    """

    def __init__(self, m, k, r):
        self.m, self.k, self.r = m, k, r
        self.order = m * k
        self.pw = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
        x = np.arange(self.order, dtype=np.int64)
        self._a = x // k
        self._b = x % k
        self._inv = lib.semidirect_group(m, k, r)[2]

    def rmul(self, g):
        """Array over x of x * g."""
        c, e = divmod(g, self.k)
        A = (self._a + self.pw[self._b] * c) % self.m
        B = (self._b + e) % self.k
        return A * self.k + B

    def inv(self, g):
        """Inverse of g, as an int."""
        return self._inv(g)


def _make_group(m, k, rng):
    """Return a group Z_m x|_r Z_k, choosing r at random among valid choices (r^k = 1 mod m, gcd(r,m)=1).

    Falls back to the abelian r = 1 when no non-trivial r exists.
    """
    if k == 1:
        r = 1 % m
    else:
        cands = [r for r in range(2, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        r = rng.choice(cands) if cands else 1 % m
    return _Grp(m, k, r)


# ---------------------------------------------------------------- lifts (annealing)

def _neighbors(P, Pinv, V, s, G):
    """Neighbour table (n x d) of the G-lift of a d-regular bipartite base on s+s vertices."""
    d = P.shape[0]
    o = G.order
    nbr = np.empty((2 * s * o, d), dtype=np.int64)
    for k in range(d):
        for i in range(s):
            j = int(P[k, i])
            nbr[i * o:(i + 1) * o, k] = s * o + j * o + G.rmul(int(V[k, i]))
        for j in range(s):
            i = int(Pinv[k, j])
            nbr[(s + j) * o:(s + j + 1) * o, k] = i * o + G.rmul(G.inv(int(V[k, i])))
    return nbr


def _cost(nbr, sources, D):
    """Number of (source, vertex) pairs NOT within distance D. Zero iff the lift is valid."""
    n = nbr.shape[0]
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


def _anneal(s, G, d, D, rng, deadline):
    """Simulated annealing over permutations and voltages. Returns (P, V) with zero cost, or None."""
    o = G.order
    P = np.array([rng.sample(range(s), s) for _ in range(d)], dtype=np.int64)
    Pinv = np.zeros_like(P)
    for k in range(d):
        for i in range(s):
            Pinv[k, P[k, i]] = i
    V = np.array([[rng.randrange(o) for _ in range(s)] for _ in range(d)], dtype=np.int64)
    # Left multiplication is an automorphism, so one source per block suffices.
    sources = [i * o for i in range(2 * s)]
    nbr = _neighbors(P, Pinv, V, s, G)
    cur = _cost(nbr, sources, D)
    for it in range(ITERS):
        if cur == 0 or time.monotonic() > deadline:
            break
        temp = 2.0 * (1.0 - it / ITERS) + 0.05
        if s == 1 or rng.random() < 0.7:
            k, i = rng.randrange(d), rng.randrange(s)
            old = int(V[k, i])
            new_v = rng.randrange(o)
            if new_v == old:
                continue
            V[k, i] = new_v
            cand = _neighbors(P, Pinv, V, s, G)
            c = _cost(cand, sources, D)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur, nbr = c, cand
            else:
                V[k, i] = old
        else:
            k = rng.randrange(d)
            a, b = rng.sample(range(s), 2)
            _swap(P, Pinv, k, a, b)
            cand = _neighbors(P, Pinv, V, s, G)
            c = _cost(cand, sources, D)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur, nbr = c, cand
            else:
                _swap(P, Pinv, k, a, b)
    if cur == 0:
        return P.copy(), V.copy()
    return None


def _graph(s, G, P, V, d):
    """Materialise the G-lift as (n, edges), deduplicated."""
    Pinv = np.zeros_like(P)
    for k in range(d):
        for i in range(s):
            Pinv[k, P[k, i]] = i
    nbr = _neighbors(P, Pinv, V, s, G)
    edges = set()
    for x in range(s * G.order):
        for y in nbr[x].tolist():
            edges.add((x, y))
    return 2 * s * G.order, sorted(edges)


def _try_size(s, G, d, D, rng, deadline):
    """Attempt to anneal a valid lift over G, with a few independent restarts."""
    for _ in range(RETRIES):
        if time.monotonic() > deadline:
            break
        st = _anneal(s, G, d, D, rng, deadline)
        if st is not None:
            return st
    return None


def _search(s, k, d, D, rng, deadline, cap):
    """For fixed (s, k), find the largest m (doubling then bisection) whose lift over Z_m x| Z_k passes annealing."""
    best = None
    lo, hi = 0, None
    m = 1
    while time.monotonic() < deadline:
        if 2 * s * m * k > cap:
            hi = m
        else:
            G = _make_group(m, k, rng)
            st = _try_size(s, G, d, D, rng, deadline)
            if st is not None:
                lo = m
                best = (G, st[0], st[1])
            else:
                hi = m
        if hi is None:
            m = 2 * lo
        else:
            if hi - lo <= 1:
                break
            m = (lo + hi) // 2
    return best


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, TIME_FRAC * time_limit - 1.0)
    post_end = start + max(0.5, POST_FRAC * time_limit - 1.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if D == 2:
        return lib.haar_graph(d, range(d))  # K_{d,d} is extremal for D = 2

    cands = [lib.haar_graph(d, range(d))]   # K_{d,d}: diameter 2, always valid

    # D >= 3: projective plane (diameter 3), extended into spare degree.
    if d >= 3:
        base = _pg_base(d)
        if base is not None:
            if lib.is_prime_power(d - 1) and D == 3:   # Moore-extremal, nothing to improve
                return _finish(cands + [base], d, D)
            cands.append(base)
            aug = _augment(base[0], base[1], d, seed)
            for g in (base, aug):
                cands.append(_grow(g[0], g[1], d, D, rng, min(deadline, time.monotonic() + 0.7)))

    # D >= 4: generalized quadrangle W(q) (diameter 4 <= D), extended as well.
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            if D == 4 and d - 1 <= GQ_Q_MAX and lib.is_prime_power(d - 1):
                return _finish(cands + [gq], d, D)  # Moore-extremal for D = 4
            cands.append(gq)
            aug = _augment(gq[0], gq[1], d, seed)
            for g in (gq, aug):
                cands.append(_grow(g[0], g[1], d, D, rng, min(deadline, time.monotonic() + 0.7)))

    cap = min(N_CAP, lib._moore_bound(d, D))

    # Haar graphs with growing modulus (small slice of the remaining time).
    now = time.monotonic()
    haar_frac = 0.2 if D <= 4 else 0.1
    haar_end = now + haar_frac * max(0.0, deadline - now)
    haar_best, haar_m, haar_miss = None, d + 1, 0
    while time.monotonic() < haar_end and haar_miss < 4:
        S = _search_haar(d, D, haar_m, rng, haar_end, 120)
        if S is not None:
            haar_best = lib.haar_graph(haar_m, S)
            haar_miss = 0
        else:
            haar_miss += 1
        haar_m += 1
    if haar_best is not None:
        cands.append(haar_best)

    # Voltage-lift annealing: cyclic lifts for each s, plus dihedral-type lifts (k = 2).
    configs = [(s, 1) for s in S_LIST] + [(s, 2) for s in DIHEDRAL_S]
    lift_best = None
    for idx, (s, k) in enumerate(configs):
        now = time.monotonic()
        if now >= deadline:
            break
        slice_end = now + (deadline - now) / (len(configs) - idx)
        res = _search(s, k, d, D, rng, slice_end, cap)
        if res is not None:
            G, P, V = res
            g = _graph(s, G, P, V, d)
            cands.append(g)
            if lift_best is None or g[0] > lift_best[0]:
                lift_best = g

    # Post-process the largest lift: fill spare degree, then grow with single and paired vertices.
    if lift_best is not None and time.monotonic() < post_end:
        aug = _augment(lift_best[0], lift_best[1], d, seed)
        cands.append(aug)
        ext_end = min(post_end, time.monotonic() + POST_EXTEND_SLICE)
        cands.append(_grow(aug[0], aug[1], d, D, rng, ext_end))

    return _finish(cands, d, D)
