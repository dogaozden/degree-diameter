import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact constructions (kept as instant answers where they are optimal).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# New construction: single-block bi-Cayley graphs over small groups.
#
# Group G = Z_m x| Z_k (element a*k+b, (a,b)(c,e) = (a + r^b c, b + e)).
# Vertices A_g = g and B_h = G + h. Connection set S (|S| = d, distinct):
#     A_g ~ B_{g s} for s in S.
# Each B_h then has neighbours A_{h s^{-1}}, so the graph is bipartite and
# d-regular. Left multiplication is an automorphism that is transitive on each
# side, so diameter <= D holds iff eccentricity of A_e and of B_e are <= D.
# Both are checked with a vectorised bitmask BFS.
#
# S is found by simulated annealing on the number of unreached (source, vertex)
# pairs. The order is grown by galloping over G, and every success is checked
# with lib.is_valid before it is accepted. The fallback K_{d,d} is always kept.
# ----------------------------------------------------------------------------

def _groups(G):
    """Candidate groups of order G as (m, k, r), with the cyclic group always included."""
    out = [(G, 1, 1)]
    for k in range(2, G + 1):
        if G % k:
            continue
        m = G // k
        if m < 3:
            continue
        for r in range(2, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _table(m, k, r):
    """Return (G, RM, invs) with RM[s, g] = g*s and invs[s] = s^{-1}."""
    G = m * k
    x = np.arange(G, dtype=np.int64)
    a = x // k
    b = x % k
    P = np.array([pow(r, t, m) for t in range(k)], dtype=np.int64)
    RM = ((a[None, :] + P[b][None, :] * a[:, None]) % m) * k + (b[None, :] + b[:, None]) % k
    invs = np.argmax(RM == 0, axis=1)
    return G, RM, invs


def _cost(ADJ, G, D):
    """Number of (source, vertex) pairs left unreached within D steps from A_e and B_e."""
    N = 2 * G
    R = np.zeros((N, 2), dtype=bool)
    R[0, 0] = True
    R[G, 1] = True
    for _ in range(D):
        R = R | R[ADJ].any(axis=1)
    return 2 * N - int(R.sum())


def _anneal(d, D, G, RM, invs, rng, deadline):
    """Simulated annealing over the connection set. Returns the adjacency array, or None."""
    if G < d:
        return None
    S = rng.sample(range(G), d)
    ADJ = np.empty((2 * G, d), dtype=np.int64)

    def put(i, s):
        ADJ[:G, i] = G + RM[s]
        ADJ[G:, i] = RM[invs[s]]

    for i, s in enumerate(S):
        put(i, s)
    cost = _cost(ADJ, G, D)
    inS = set(S)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    T = 1.0
    it = 0
    while cost > 0:
        if (it & 31) == 0:
            now = time.monotonic()
            if now > deadline:
                return None
            T = 0.5 + 1.5 * max(0.0, 1.0 - (now - t0) / span)
        it += 1
        i = rng.randrange(d)
        new = rng.randrange(G)
        if new in inS:
            continue
        old = S[i]
        put(i, new)
        c2 = _cost(ADJ, G, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            S[i] = new
            inS.discard(old)
            inS.add(new)
            cost = c2
        else:
            put(i, old)
    return ADJ


def _edges(G, ADJ):
    """Edge list of the bi-Cayley graph: A_g = g, B_h = G + h."""
    return [(g, v) for g in range(G) for v in ADJ[g].tolist()]


# ----------------------------------------------------------------------------
# Greedy pair insertion (keeps degrees and bipartition, grows order by 2).
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


def _extend(n, edges, d, D, rng, deadline):
    """Repeatedly grow the order by 2 while the result stays valid."""
    if d < 1 or not edges:
        return n, edges
    color = _two_color(n, edges)
    if color is None:
        return n, edges
    edges = list(edges)
    color = list(color)
    while time.monotonic() < deadline:
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
    return n, edges


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for every D >= 2.
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
        if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(*lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass

    search_end = start + 0.8 * budget

    def attempt(G, slice_end):
        cands = _groups(G)
        while time.monotonic() < slice_end:
            m, k, r = rng.choice(cands)
            _, RM, invs = _table(m, k, r)
            ADJ = _anneal(d, D, G, RM, invs, rng, min(slice_end, time.monotonic() + 4.0))
            if ADJ is not None:
                return ADJ
        return None

    # Galloping search over the half-order G (order of the graph is 2G).
    try:
        lo = max(d, best_n // 2)
        step = max(1, lo // 8)
        fails = 0
        while time.monotonic() < search_end and fails < 3 and lo < 1500:
            G = lo + step
            slice_end = min(search_end, time.monotonic() + 6.0)
            ADJ = attempt(G, slice_end)
            if ADJ is not None:
                consider(2 * G, _edges(G, ADJ))
                lo = G
                step *= 2
                fails = 0
            else:
                if step == 1:
                    fails += 1
                else:
                    step = max(1, step // 2)
    except Exception:
        pass

    try:
        n2, e2 = _extend(best_n, best[1], d, D, rng, deadline)
        if n2 > best_n:
            consider(n2, e2)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
