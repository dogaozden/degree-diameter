import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Baseline families: projective plane incidence, Araujo-Pardo-Lopez for D = 3,
# and saturation with leftover degree (adds edges only, so validity is kept).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez record graph for d = q + 2 with q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


def _adj_from(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    return adj


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


def _saturate_edges(n, edges, d, rng):
    """Greedily add missing opposite-side edges between deficient vertices (only adds edges)."""
    edges = list(edges)
    adj = _adj_from(n, edges)
    existing = {(min(u, v), max(u, v)) for u, v in edges}
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    left = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in left for b in right if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return edges


# ----------------------------------------------------------------------------
# NEW: abelian Haar graphs over Z_a x Z_b (non-cyclic groups allowed), searched
# for diameter D with a cheap two-source cost.
#
# H(G, S): a-vertex x is joined to b-vertex x + s for every s in S, with |S| = d.
# Translations x -> x + g are automorphisms that act transitively on each side,
# so every distance check reduces to a BFS from a_0 and from b_0. The cost is
# the number of vertices not reached within D from those two sources (zero means
# diameter <= D). WLOG 0 is in S, because translating S only relabels b-vertices.
# The parent only searched cyclic Z_m and disabled this for D >= 5.
# ----------------------------------------------------------------------------

def _haar_cost(m, D, S_tr, S_ntr):
    """Uncovered-vertex count from a_0 and b_0. S_tr[i] is x -> x+s_i, S_ntr[i] is x -> x-s_i."""
    total = 0
    N = 2 * m
    for src in (0, m):
        seen = bytearray(N)
        seen[src] = 1
        frontier = [src]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < m:
                    for t in S_tr:
                        v = m + t[u]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    y = u - m
                    for t in S_ntr:
                        v = t[y]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            cnt += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - cnt
    return total


def _haar_search(d, D, a, b, rng, deadline, iters):
    """Hill-climb S (|S| = d, containing 0) in Z_a x Z_b; return S with zero cost or None."""
    m = a * b
    if m < d or d - 1 > m - 1:
        return None
    cache = {}

    def tr(s):
        t = cache.get(s)
        if t is None:
            si, sj = divmod(s, b)
            t = [((x // b + si) % a) * b + (x % b + sj) % b for x in range(m)]
            cache[s] = t
        return t

    def neg(s):
        si, sj = divmod(s, b)
        return ((-si) % a) * b + (-sj) % b

    def cost(S):
        return _haar_cost(m, D, [tr(s) for s in S], [tr(neg(s)) for s in S])

    S = [0] + rng.sample(range(1, m), d - 1)
    c = cost(S)
    T0 = 1.0
    it = 0
    while c > 0 and it < iters and time.monotonic() < deadline:
        it += 1
        i = rng.randrange(1, d)
        cand = rng.randrange(1, m)
        if cand in S:
            continue
        T = S[:]
        T[i] = cand
        ct = cost(T)
        if ct <= c or rng.random() < math.exp(-(ct - c) / T0):
            S, c = T, ct
    return S if c == 0 else None


def _haar_edges(m, S, b, a):
    """Edges of H(Z_a x Z_b, S): a-vertex x is id x, b-vertex y is id m + y."""
    edges = []
    for s in S:
        si, sj = divmod(s, b)
        for x in range(m):
            xi, xj = divmod(x, b)
            y = ((xi + si) % a) * b + (xj + sj) % b
            edges.append((x, m + y))
    return 2 * m, edges


def _haar_phase(d, D, moore, rng, deadline, state, consider):
    """Repeatedly search abelian Haar graphs just above the current best order."""
    while time.monotonic() < deadline and state["n"] < moore:
        m_lo = max(d, state["n"] // 2 + 1)
        m_hi = min(moore // 2, m_lo + 3)
        if m_hi < m_lo:
            break
        m = rng.randint(m_lo, m_hi)
        pairs = [(a, m // a) for a in range(1, m + 1) if m % a == 0]
        a, b = rng.choice(pairs)
        slice_end = min(deadline, time.monotonic() + 1.5)
        S = _haar_search(d, D, a, b, rng, slice_end, 300)
        if S is not None:
            n, e = _haar_edges(m, S, b, a)
            if consider(n, e):
                state["n"] = n


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))
    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e
            return True
        return False

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            n2 = pg[0]
            e2 = _saturate_edges(pg[0], pg[1], d, rng)
            consider(n2, e2)
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

    if best_n < moore:
        state = {"n": best_n}
        _haar_phase(d, D, moore, rng, deadline, state, consider)

    # Use leftover degree on the final graph (only adds edges, so validity is kept).
    if best_n < moore and time.monotonic() < deadline + 0.05 * time_limit:
        sat = _saturate_edges(best_n, best_e, d, rng)
        consider(best_n, sat)

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, best_e
