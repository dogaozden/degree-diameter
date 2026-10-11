import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe baseline families (always valid; used as fallbacks).
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
# NEW CONSTRUCTION: bipartite Haar graphs over finite groups.
#
# For a group G of order m and a connection set S = {s_1..s_d} (distinct),
# vertices A_g and B_h (g, h in G) with A_g ~ B_{g s} for s in S.
# This is d-regular and bipartite on 2m vertices. Left multiplication by G is
# an automorphism acting transitively on each side, so diameter <= D holds iff
# every vertex is within distance D of A_e and of B_e. We search S by simulated
# annealing, minimising the number of unreached (source, vertex) pairs for the
# two sources. Groups are semidirect products Z_m x| Z_k (r = 1 gives direct
# products, so abelian groups are included).
# ----------------------------------------------------------------------------

def _group(m, k, r):
    """Return (G, M, inv) for Z_m x|_r Z_k with element (a, b) coded as a*k + b; identity is 0."""
    G = m * k
    x = np.arange(G, dtype=np.int64)
    a = x // k
    b = x % k
    pw = np.array([pow(r, t, m) for t in range(k)], dtype=np.int64)
    M = ((a[:, None] + pw[b][:, None] * a[None, :]) % m) * k + (b[:, None] + b[None, :]) % k
    inv = np.empty(G, dtype=np.int64)
    rows, cols = np.nonzero(M == 0)
    inv[rows] = cols
    return G, M, inv


def _sample_group(target, rng):
    """Return (G, M, inv) for a group of order G >= target (roughly), or None."""
    for _ in range(200):
        k = rng.choice([1, 1, 2, 3, 4, 6, 7, 8, 9, 12, 14, 16])
        m = max(2, -(-(target + rng.randrange(0, 6)) // k))
        if k == 1:
            r = 1
        elif rng.random() < 0.4:
            r = 1
        else:
            r = None
            for _ in range(80):
                c = rng.randrange(2, m) if m > 2 else 1
                if math.gcd(c, m) == 1 and pow(c, k, m) == 1 % m:
                    r = c
                    break
            if r is None:
                continue
        return _group(m, k, r)
    return None


def _build_nbr(G, M, inv, S):
    """Neighbour table (2G x d): rows 0..G-1 are A-vertices, G..2G-1 are B-vertices."""
    A_nbr = G + M[:, S]
    B_nbr = M[:, inv[S]]
    return np.vstack([A_nbr, B_nbr])


def _cost(G, nbr, D):
    """Number of unreached (source, vertex) pairs for sources A_e and B_e within distance D."""
    N = nbr.shape[0]
    R = np.zeros((N, 2), dtype=bool)
    R[0, 0] = True
    R[G, 1] = True
    for _ in range(D):
        R2 = R | R[nbr].any(axis=1)
        if np.array_equal(R2, R):
            break
        R = R2
    return int(2 * N - R.sum())


def _anneal(d, D, G, M, inv, rng, deadline, iters):
    """Search a connection set S (containing the identity) with diameter <= D. Returns S or None."""
    if d < 2 or G < d:
        return None
    S = [0] + rng.sample(range(1, G), d - 1)
    S_arr = np.array(S, dtype=np.int64)
    inS = set(S)
    cost = _cost(G, _build_nbr(G, M, inv, S_arr), D)
    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        temp = 2.0 * (1.0 - t / iters) + 0.2
        j = rng.randrange(1, d)
        new = rng.randrange(1, G)
        if new in inS:
            continue
        old = S[j]
        S[j] = new
        S_arr[j] = new
        c2 = _cost(G, _build_nbr(G, M, inv, S_arr), D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost = c2
            inS.discard(old)
            inS.add(new)
        else:
            S[j] = old
            S_arr[j] = old
    if cost == 0:
        return S
    return None


def _haar_from_group(G, M, S):
    """Edge list of the Haar graph of the group with connection set S."""
    edges = [(g, G + int(M[g, s])) for g in range(G) for s in S]
    return 2 * G, edges


# ----------------------------------------------------------------------------
# Growth by edge-switch vertex insertion (adds 2 vertices, keeps degrees).
# ----------------------------------------------------------------------------

def _colours(n, edges):
    """Proper 2-colouring of a bipartite graph; returns a list of 0/1 per vertex."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    col = [-1] * n
    for s in range(n):
        if col[s] != -1:
            continue
        col[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for w in adj[u]:
                if col[w] == -1:
                    col[w] = 1 - col[u]
                    stack.append(w)
    return col


def _grow_step(n, edges, col, d, D, rng, deadline):
    """Try random edge-switch insertions until one keeps diameter <= D. Returns (n+2, edges, col) or None."""
    m = len(edges)
    need = d - 1
    while time.monotonic() < deadline:
        order = list(range(m))
        rng.shuffle(order)
        used_a, used_b, chosen = set(), set(), []
        for idx in order:
            u, v = edges[idx]
            if col[u] == 1:
                u, v = v, u
            if u in used_a or v in used_b:
                continue
            used_a.add(u)
            used_b.add(v)
            chosen.append((idx, u, v))
            if len(chosen) == need:
                break
        if len(chosen) < need:
            continue
        drop = {idx for idx, _, _ in chosen}
        new_edges = [edges[i] for i in range(m) if i not in drop]
        x, y = n, n + 1
        for _, a, b in chosen:
            new_edges.append((x, b))
            new_edges.append((a, y))
        new_edges.append((x, y))
        if lib.within_diameter(n + 2, new_edges, D):
            return n + 2, new_edges, col + [0, 1]
    return None


def _grow(d, D, n, edges, rng, deadline):
    """Repeatedly insert vertex pairs while the graph stays valid. Returns (n, edges)."""
    col = _colours(n, edges)
    while time.monotonic() < deadline:
        res = _grow_step(n, edges, col, d, D, rng, deadline)
        if res is None:
            break
        n, edges, col = res
    return n, edges


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

    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n
            return True
        return False

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() < start + 0.2 * budget:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Bold new search: Haar graphs over finite groups with annealed connection sets.
    if d >= 2 and D >= 2:
        search_end = start + 0.8 * budget
        target = max(d + 1, best_n // 2 + 1)
        while time.monotonic() < search_end:
            g = _sample_group(target, rng)
            if g is None:
                continue
            G, M, inv = g
            if 2 * G <= best_n:
                target = max(target, best_n // 2 + 1)
                continue
            S = _anneal(d, D, G, M, inv, rng, search_end, 3000)
            if S is not None:
                n_, e_ = _haar_from_group(G, M, S)
                if consider(n_, e_):
                    target = max(target, G + 1)

    # Growth phase: spend the remaining time inserting vertex pairs into the best graph.
    if d >= 3 and time.monotonic() < deadline:
        gn, ge = _grow(d, D, best[0], list(best[1]), rng, deadline)
        consider(gn, ge)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
