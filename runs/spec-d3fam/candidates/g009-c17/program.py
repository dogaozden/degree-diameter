import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Graph helpers.
# ----------------------------------------------------------------------------

def _adjsets(n, edges):
    """Adjacency as a list of sets."""
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    return adj


def _color(n, adj):
    """Two-colouring of a bipartite graph given by adjacency sets."""
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
    """Ordered number of vertex pairs at distance > D (0 means diameter <= D)."""
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
# Base constructions for diameter 3.
# ----------------------------------------------------------------------------

def _pg_base(d):
    """Incidence graph of PG(2, q), q the largest prime power with q + 1 <= d (capped for speed)."""
    for q in range(min(d - 1, 40), 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _ara_base(d):
    """Araujo-Pardo & Lopez graph for d = q + 2 with q a prime power (order 2(q^2+q+5))."""
    q = d - 2
    if 3 <= q <= 40 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# Edge saturation: join deficient opposite-side vertices (uses spare degree for free).
# ----------------------------------------------------------------------------

def _saturate(n, edges, d, rng):
    edges = list(edges)
    adj = _adjsets(n, edges)
    deg = [len(a) for a in adj]
    col = _color(n, adj)
    left = [v for v in range(n) if col[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if col[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in left for b in right if b not in adj[a]]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d and b not in adj[a]:
            adj[a].add(b)
            adj[b].add(a)
            deg[a] += 1
            deg[b] += 1
            edges.append((a, b))
    return n, edges


# ----------------------------------------------------------------------------
# Augmentation by two vertices (point P and line L) with degree-preserving 2-switches.
# ----------------------------------------------------------------------------

def _attempt(n, edges, d, D, rng, deadline, iters):
    """One randomized attempt to add P and L and anneal 2-switches to diameter <= D.

    Step 1: take a matching of d edges (a_i, b_i) with a_i on colour 0 and b_i on colour 1,
            replace each by (a_i, P) and (b_i, L). Old degrees are unchanged; P and L get degree d.
    Step 2: anneal 2-switches (a,b),(c,e) -> (a,e),(c,b). These keep degrees and bipartiteness.
    Returns (n+2, edges) if diameter <= D is reached, otherwise None.
    """
    adj = _adjsets(n, edges)
    col = _color(n, adj)
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
    P, L = n, n + 1                 # P has colour 1, L has colour 0
    N = n + 2
    adj.append(set())
    adj.append(set())
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

    cur = _bad_count(N, adj, D)
    M = len(E)
    for it in range(iters):
        if cur == 0:
            break
        if time.monotonic() >= deadline:
            return None
        T = 1.0 * (0.03 ** (it / iters))
        i = rng.randrange(M)
        j = rng.randrange(M)
        if i == j:
            continue
        a, b = E[i]
        c, e = E[j]
        if a == c or b == e or e in adj[a] or b in adj[c]:
            continue
        # 2-switch: (a,b),(c,e) -> (a,e),(c,b)
        adj[a].discard(b); adj[b].discard(a)
        adj[c].discard(e); adj[e].discard(c)
        adj[a].add(e); adj[e].add(a)
        adj[c].add(b); adj[b].add(c)
        new = _bad_count(N, adj, D)
        if new <= cur or rng.random() < math.exp((cur - new) / T):
            cur = new
            E[i] = (a, e)
            E[j] = (c, b)
        else:
            adj[a].discard(e); adj[e].discard(a)
            adj[c].discard(b); adj[b].discard(c)
            adj[a].add(b); adj[b].add(a)
            adj[c].add(e); adj[e].add(c)
    if cur != 0:
        return None
    return N, E


def _grow(n, edges, d, D, deadline, rng, mb):
    """Repeatedly add two vertices while the Moore bound and the deadline allow."""
    cur = (n, list(edges))
    while time.monotonic() < deadline and cur[0] + 2 <= mb:
        got = None
        while got is None and time.monotonic() < deadline:
            got = _attempt(cur[0], cur[1], d, D, rng, deadline, 1500)
        if got is None:
            break
        if not lib.is_valid(got[0], got[1], d, D):
            break
        cur = got
    return cur


# ----------------------------------------------------------------------------
# Fallback for other cases: random Haar graph hill-climb.
# ----------------------------------------------------------------------------

def _haar_search(d, D, rng, deadline, best):
    m, misses = d + 1, 0
    while time.monotonic() < deadline and misses < 10:
        found = None
        for _ in range(30):
            if time.monotonic() >= deadline:
                break
            if m - 1 < d - 1:
                break
            S = [0] + rng.sample(range(1, m), d - 1)
            n, edges = lib.haar_graph(m, S)
            if lib.within_diameter(n, edges, D):
                found = (n, edges)
                break
        if found and found[0] > best[0]:
            best = found
            misses = 0
        else:
            misses += 1
        m += 1
    return best


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 0:
        return 1, []
    if D == 0:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 2:
        return best

    if D == 3:
        bases = []
        for base in (_ara_base(d), _pg_base(d)):
            if base is not None and lib.is_valid(base[0], base[1], d, D):
                bases.append(base)
        for n0, e0 in bases:
            consider(n0, e0)
        if bases:
            n0, e0 = max(bases, key=lambda x: x[0])
            n1, e1 = _saturate(n0, e0, d, rng)
            consider(n1, e1)
            mb = _moore(d, D)
            n2, e2 = _grow(n1, e1, d, D, deadline, rng, mb)
            consider(n2, e2)
        if best[0] > 2 * d:
            return best

    best = _haar_search(d, D, rng, deadline, best)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
