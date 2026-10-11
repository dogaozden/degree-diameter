import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact / safe families (fallbacks and calibration cases).
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
# Bi-Cayley (Haar-type) graphs over non-abelian groups Z_m x| Z_k.
#
# Vertices: A_g = g (g in G), B_x = G + x. Edge A_g ~ B_{g*s} for s in S, |S| = d.
# Left multiplication by h is an automorphism (A_g -> A_{hg}, B_x -> B_{hx}), so
# the graph is vertex-transitive on each side. Hence it has diameter <= D iff
# every vertex is within distance D of A_e and of B_e. This makes the check
# two BFS runs over 2|G| vertices, which is very cheap, so we can search many
# groups and connection sets quickly.
# ----------------------------------------------------------------------------

def _sample_group(T, rng):
    """Return (m, k, r) for the semidirect product Z_m x| Z_k with order m*k >= T, or None."""
    for _ in range(50):
        k = rng.randint(2, 12)
        m = -(-T // k)  # ceil
        if m < 3:
            continue
        rs = [r for r in range(2, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        if not rs:
            continue
        return m, k, rng.choice(rs)
    return None


def _semidirect_tables(m, k, r):
    """Return (G, Ts, Invs) for Z_m x| Z_k (element a*k+b, (a,b)(c,e) = (a+r^b c, b+e)).

    Ts[s, g] = g*s and Invs[s, h] = the g with g*s = h.
    """
    G = m * k
    x = np.arange(G, dtype=np.int64)
    a = x // k
    b = x % k
    powers = np.array([pow(r, t, m) for t in range(k)], dtype=np.int64)
    M = ((a[:, None] + powers[b[:, None]] * a[None, :]) % m) * k + (b[:, None] + b[None, :]) % k
    Ts = np.ascontiguousarray(M.T)  # Ts[s, g] = g*s
    Invs = np.empty((G, G), dtype=np.int64)
    rows = np.arange(G)[:, None]
    Invs[rows, Ts] = np.broadcast_to(x[None, :], (G, G))
    return G, Ts, Invs


def _nbr_from_set(S, G, Ts, Invs):
    """Adjacency array of shape (2G, d) for connection set S."""
    Sa = np.array(S, dtype=np.int64)
    A = G + Ts[Sa].T      # A_g -> B_{g*s_j}
    B = Invs[Sa].T        # B_x -> A_{x*s_j^{-1}}
    return np.vstack([A, B])


def _cost(nbr, G, D):
    """Number of (source, vertex) pairs unreached within D from A_e and from B_e. Zero iff valid."""
    N = 2 * G
    total = 0
    for src in (0, G):
        seen = np.zeros(N, dtype=bool)
        seen[src] = True
        fr = np.array([src], dtype=np.int64)
        for _ in range(D):
            nx = nbr[fr].ravel()
            nx = nx[~seen[nx]]
            if nx.size == 0:
                break
            nx = np.unique(nx)
            seen[nx] = True
            fr = nx
        total += N - int(seen.sum())
    return total


def _cayley_search(d, D, T, rng, deadline, iters):
    """Simulated annealing over connection sets in a random semidirect group of order about T.

    Returns (n, edges) with a valid graph, or None.
    """
    g = _sample_group(max(T, d + 1), rng)
    if g is None:
        return None
    m, k, r = g
    G, Ts, Invs = _semidirect_tables(m, k, r)
    if G < d + 1:
        return None

    S = rng.sample(range(G), d)
    nbr = _nbr_from_set(S, G, Ts, Invs)
    cost = _cost(nbr, G, D)

    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        temp = max(0.05, 1.5 * (1.0 - t / iters))
        j = rng.randrange(d)
        new = rng.randrange(G)
        if new in S:
            continue
        old = S[j]
        S[j] = new
        nbr2 = _nbr_from_set(S, G, Ts, Invs)
        c2 = _cost(nbr2, G, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            nbr, cost = nbr2, c2
        else:
            S[j] = old

    if cost != 0:
        return None
    A = nbr[:G]
    edges = [(gi, int(v)) for gi in range(G) for v in A[gi]]
    return 2 * G, edges


# ----------------------------------------------------------------------------
# Greedy pair insertion: grow the order by 2 while the result stays valid.
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


def _extend(n, edges, d, D, rng, deadline, max_fail=300):
    """Repeatedly add two vertices x (side A), y (side B) using removed edges, keeping validity."""
    if d < 1 or not edges:
        return n, edges
    color = _two_color(n, edges)
    if color is None:
        return n, edges
    edges = list(edges)
    color = list(color)
    fails = 0
    while time.monotonic() < deadline and fails < max_fail:
        order = list(range(len(edges)))
        rng.shuffle(order)
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
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget
    search_deadline = start + 0.78 * budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D  # even cycle: bipartite, degree 2, diameter D
        return n, [(i, (i + 1) % n) for i in range(n)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions.
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

    # Main search: bi-Cayley graphs over random semidirect products.
    # Target order just above the current best, with a small random spread.
    try:
        while time.monotonic() < search_deadline:
            half = best_n // 2
            spread = max(1, half // 20)
            T = half + 1 + rng.randrange(0, spread)
            attempt_deadline = min(search_deadline, time.monotonic() + 2.0)
            res = _cayley_search(d, D, T, rng, attempt_deadline, 2500)
            if res is not None:
                consider(res[0], res[1])
    except Exception:
        pass

    # Greedy pair insertion on the best graph found.
    try:
        n2, e2 = _extend(best_n, best[1], d, D, rng, deadline)
        if n2 > best_n:
            consider(n2, e2)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
