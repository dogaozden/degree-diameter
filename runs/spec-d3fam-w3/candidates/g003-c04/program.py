import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Utilities.
# ----------------------------------------------------------------------------

def _color(n, adj):
    """Two-colour a bipartite graph given as adjacency collections."""
    col = [-1] * n
    for s in range(n):
        if col[s] != -1:
            continue
        col[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if col[v] == -1:
                    col[v] = 1 - col[u]
                    stack.append(v)
    return col


def _bad_count(n, adj, D):
    """Ordered number of vertex pairs at distance > D (zero iff diameter <= D and connected)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(n - r.bit_count() for r in reach)


def _moore(d, D):
    """Moore-type upper bound on the order of a bipartite graph with max degree d and diameter D."""
    if D == 0 or d == 0:
        return 1
    if d == 1:
        return min(2, D + 1)
    if d == 2:
        return 2 * D
    return 2 * sum((d - 1) ** i for i in range(D))


# ----------------------------------------------------------------------------
# NEW construction for D = 3: Haar graphs H(m, S) with |S| = d.
#
# Vertices a_i, b_j (i, j in Z_m); a_i ~ b_{i+s} for s in S. Then
#   * a_0 and a_t are at distance <= 2  iff  t in S - S,
#   * a_0 and b_t are at distance <= 3  iff  t in S or t in S - S + S.
# So diameter <= 3 is a pure covering condition on Z_m, which we search
# directly by simulated annealing over the d-element set S (0 in S wlog).
# This is a different family from the projective-plane / Araujo-Pardo-Lopez
# base, and it can reach orders with no prime-power restriction on d-1.
# ----------------------------------------------------------------------------

def _haar_cost(arr, m):
    """Number of residues not covered by the two D=3 covering conditions (0 iff valid)."""
    diffs = (arr[:, None] - arr[None, :]) % m
    cov = np.zeros(m, dtype=bool)
    cov[diffs.ravel()] = True
    bad = m - int(cov.sum())
    tri = (diffs[:, :, None] + arr[None, None, :]) % m
    cov3 = np.zeros(m, dtype=bool)
    cov3[arr] = True
    cov3[tri.ravel()] = True
    bad += m - int(cov3.sum())
    return bad


def _anneal_haar(m, d, rng, end):
    """Find a size-d set S in Z_m (0 in S) with _haar_cost 0, or return None by the deadline."""
    S = [0] + rng.sample(range(1, m), d - 1)
    cur = _haar_cost(np.array(S, dtype=np.int64), m)
    it = 0
    while cur > 0:
        if time.monotonic() >= end:
            return None
        it += 1
        if it % 32 == 0 and time.monotonic() >= end:
            return None
        # Cyclic reheating keeps the search from freezing into one basin.
        T = 1.0 * (0.997 ** (it % 4000)) + 0.05
        i = rng.randrange(1, d)
        new = rng.randrange(1, m)
        if new in S:
            continue
        cand = S[:]
        cand[i] = new
        c = _haar_cost(np.array(cand, dtype=np.int64), m)
        if c <= cur or rng.random() < math.exp((cur - c) / T):
            S, cur = cand, c
    return S


def _haar_d3(d, deadline, rng):
    """Largest valid Haar graph H(m, S) with |S| = d found before the deadline, or None."""
    best = None
    m_cap = d * d - d + 1           # Moore-type limit for D = 3 (2m vertices)
    m = d + 1
    while m <= m_cap and time.monotonic() < deadline:
        remaining = deadline - time.monotonic()
        found = None
        for _ in range(2):          # two attempts per order m
            end = time.monotonic() + max(0.5, 0.3 * remaining)
            end = min(end, deadline)
            S = _anneal_haar(m, d, rng, end)
            if S is not None:
                found = S
                break
            if time.monotonic() >= deadline:
                break
        if found is None:
            break                   # harder for larger m; stop the ascent
        n, edges = lib.haar_graph(m, found)
        if lib.is_valid(n, edges, d, 3):
            best = (n, edges)
        m += 1
    return best


# ----------------------------------------------------------------------------
# Base constructions (parent pipeline, used for D = 3 and D = 4).
# ----------------------------------------------------------------------------

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


def _bases(d, D):
    """Candidate structured base graphs (already diameter <= D by construction)."""
    out = []
    if D == 3:
        q = d - 1
        if q >= 2 and lib.is_prime_power(q):
            out.append(lib.projective_plane_incidence(q))
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                out.append(lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass
    elif D == 4:
        for q in range(min(d - 1, 7), 1, -1):
            if lib.is_prime_power(q):
                out.append(_gq_w(q))
                break
    return out


# ----------------------------------------------------------------------------
# Degree-respecting saturation: adding edges never increases distances.
# ----------------------------------------------------------------------------

def _saturate(n, edges, d, rng):
    """Join deficient opposite-side vertices in random order while degrees stay <= d."""
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    col = _color(n, adj)
    deg = [len(s) for s in adj]
    left = [v for v in range(n) if col[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if col[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in left for b in right if b not in adj[a]]
    rng.shuffle(pairs)
    E = list(edges)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d and b not in adj[a]:
            adj[a].add(b)
            adj[b].add(a)
            deg[a] += 1
            deg[b] += 1
            E.append((a, b))
    return E


# ----------------------------------------------------------------------------
# Vertex augmentation: add a point P and a line L via degree-preserving
# 2-switches, annealing the number of pairs at distance > D to zero.
# ----------------------------------------------------------------------------

def _augment(n, edges, d, D, rng, deadline, iters):
    """Return (n+2, edges) with diameter <= D, or None if the anneal fails."""
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    col = _color(n, adj)

    P, L = n, n + 1
    adj.append(set())
    adj.append(set())
    N = n + 2

    oriented = [((u, v) if col[u] == 0 else (v, u)) for u, v in edges]
    rng.shuffle(oriented)
    used, pick = set(), []
    for idx, (a, b) in enumerate(oriented):
        if a not in used and b not in used:
            pick.append(idx)
            used.add(a)
            used.add(b)
            if len(pick) == d:
                break
    if len(pick) < d:
        return None

    picked = set(pick)
    E = [oriented[i] for i in range(len(oriented)) if i not in picked]
    for idx in pick:
        a, b = oriented[idx]
        adj[a].discard(b)
        adj[b].discard(a)
        adj[a].add(P)
        adj[P].add(a)
        adj[b].add(L)
        adj[L].add(b)
        E.append((a, P))
        E.append((L, b))

    M = len(E)
    cur = _bad_count(N, adj, D)
    for it in range(iters):
        if cur == 0:
            break
        if time.monotonic() >= deadline:
            return None
        T = 0.8 * (0.02 ** (it / iters))
        i = rng.randrange(M)
        j = rng.randrange(M)
        if i == j:
            continue
        a, b = E[i]
        c, e = E[j]
        if a == c or b == e or e in adj[a] or b in adj[c]:
            continue
        adj[a].discard(b)
        adj[b].discard(a)
        adj[c].discard(e)
        adj[e].discard(c)
        adj[a].add(e)
        adj[e].add(a)
        adj[c].add(b)
        adj[b].add(c)
        new = _bad_count(N, adj, D)
        if new <= cur or rng.random() < math.exp((cur - new) / T):
            cur = new
            E[i] = (a, e)
            E[j] = (c, b)
        else:
            adj[a].discard(e)
            adj[e].discard(a)
            adj[c].discard(b)
            adj[b].discard(c)
            adj[a].add(b)
            adj[b].add(a)
            adj[c].add(e)
            adj[e].add(c)
    if cur != 0:
        return None
    return N, E


# ----------------------------------------------------------------------------
# Haar graph random search (fallback for cases without a structured base).
# ----------------------------------------------------------------------------

def _haar_fallback(d, D, rng, deadline):
    best = lib.haar_graph(d, range(d))
    m, misses = d + 1, 0
    while time.monotonic() < deadline and misses < 10:
        found = None
        for _ in range(30):
            if time.monotonic() >= deadline:
                break
            S = [0] + rng.sample(range(1, m), d - 1)
            n, edges = lib.haar_graph(m, S)
            if lib.within_diameter(n, edges, D):
                found = (n, edges)
                break
        if found:
            best, misses = found, 0
        else:
            misses += 1
        m += 1
    return best


# ----------------------------------------------------------------------------
# Parent pipeline (structured base + saturation + augmentation).
# ----------------------------------------------------------------------------

def _structured(d, D, rng, deadline):
    cur = None
    for n_b, e_b in _bases(d, D):
        if lib.is_valid(n_b, e_b, d, D) and (cur is None or n_b > cur[0]):
            cur = (n_b, e_b)

    if cur is None:
        best = _haar_fallback(d, D, rng, deadline)
        if lib.is_valid(best[0], best[1], d, D):
            return best
        return lib.haar_graph(d, range(d))

    sat_edges = _saturate(cur[0], cur[1], d, rng)
    if lib.is_valid(cur[0], sat_edges, d, D):
        cur = (cur[0], sat_edges)

    mb = _moore(d, D)
    while time.monotonic() < deadline and cur[0] + 2 <= mb:
        res = _augment(cur[0], cur[1], d, D, rng, deadline, iters=2000)
        if res is None:
            continue
        if not lib.is_valid(res[0], res[1], d, D):
            break
        cur = res

    if not lib.is_valid(cur[0], cur[1], d, D):
        return lib.haar_graph(d, range(d))
    return cur


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = 0.85 * time_limit
    deadline = start + total
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    if D == 2:
        return lib.haar_graph(d, range(d))

    safe = lib.haar_graph(d, range(d))  # K_{d,d}: valid for D >= 2

    if D == 3:
        # Split the budget: the parent pipeline gets a share, the new Haar
        # search gets the rest. Either result is kept only if valid.
        cands = []
        parent_deadline = start + 0.4 * total
        try:
            p = _structured(d, D, rng, parent_deadline)
            if lib.is_valid(p[0], p[1], d, D):
                cands.append(p)
        except Exception:
            pass
        try:
            h = _haar_d3(d, deadline, rng)
            if h is not None and lib.is_valid(h[0], h[1], d, D):
                cands.append(h)
        except Exception:
            pass
        if not cands:
            return safe
        best = max(cands, key=lambda g: g[0])
        if lib.is_valid(best[0], best[1], d, D):
            return best
        return safe

    try:
        res = _structured(d, D, rng, deadline)
        if lib.is_valid(res[0], res[1], d, D):
            return res
    except Exception:
        pass
    return safe
