import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe exact baselines.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d (diameter 3)."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Haar graphs over non-abelian groups (new family for D >= 5).
#
# G = Z_m x| Z_k2 with elements coded as a*k2 + b. The Haar graph of G with
# connection set S (|S| = d, distinct) has vertices A_g = g and B_h = G + h,
# with A_g ~ B_{g*s} for s in S. Every vertex has degree d. Left multiplication
# is an automorphism with two vertex orbits (A and B), so the diameter is at most
# D exactly when every vertex is within distance D of A_e and of B_e.
#
# The connection set is found by simulated annealing: each move replaces one
# element of S, and the cost is the number of vertices not reached within D steps
# from A_e and from B_e. Every accepted result is checked with lib.is_valid.
# ----------------------------------------------------------------------------

def _sample_group(target, rng):
    """Return (m, k2, r) with m * k2 >= target, or None."""
    for _ in range(300):
        k2 = rng.choice([1, 2, 2, 3, 3, 4, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24])
        m = max(2, -(-target // k2)) + rng.randrange(0, 3)
        if k2 == 1:
            if rng.random() < 0.8:  # prefer non-abelian groups
                continue
            return m, 1, 1
        r = None
        for _ in range(80):
            c = rng.randrange(1, m)
            if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                r = c
                break
        if r is None:
            continue
        return m, k2, r
    return None


def _semidirect_tables(m, k2, r):
    """Return (G, Ts, Invs): Ts[s, g] = g*s and Invs[s, h] = the g with g*s = h."""
    G = m * k2
    x = np.arange(G, dtype=np.int64)
    a = x // k2
    b = x % k2
    powers = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    M = ((a[:, None] + powers[b[:, None]] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2
    Ts = np.ascontiguousarray(M.T)  # Ts[s, g] = g*s
    Invs = np.empty((G, G), dtype=np.int64)
    rows = np.arange(G)[:, None]
    Invs[rows, Ts] = np.broadcast_to(x[None, :], (G, G))
    return G, Ts, Invs


def _unreached(nbr, N, src, D):
    """Number of vertices not within distance D of src, using frontier BFS over nbr (shape (d, N))."""
    seen = np.zeros(N, dtype=bool)
    seen[src] = True
    front = np.array([src], dtype=np.int64)
    for _ in range(D):
        nxt = np.unique(nbr[:, front])
        nxt = nxt[~seen[nxt]]
        if nxt.size == 0:
            break
        seen[nxt] = True
        front = nxt
    return N - int(seen.sum())


def _haar_search(d, D, G, Ts, Invs, rng, deadline, iters):
    """Anneal a connection set S (|S| = d) so the Haar graph of G has diameter <= D.

    Returns S on success, or None.
    """
    if G < d:
        return None
    N = 2 * G
    S = rng.sample(range(G), d)
    nbr = np.empty((d, N), dtype=np.int64)

    def fill(l, s):
        nbr[l, :G] = G + Ts[s]   # A_g ~ B_{g*s}
        nbr[l, G:] = Invs[s]     # B_h ~ A_{h*s^-1}

    for l, s in enumerate(S):
        fill(l, s)

    def cost():
        return _unreached(nbr, N, 0, D) + _unreached(nbr, N, G, D)

    cur = cost()
    T0 = 2.0
    for t in range(iters):
        if cur == 0:
            break
        if (t & 63) == 0 and time.monotonic() > deadline:
            break
        j = rng.randrange(d)
        new = rng.randrange(G)
        if new in S:
            continue
        old = S[j]
        S[j] = new
        fill(j, new)
        c2 = cost()
        temp = T0 * (1.0 - t / iters) + 0.05
        if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / temp):
            cur = c2
        else:
            S[j] = old
            fill(j, old)
    if cur != 0:
        return None
    return S


def _haar_edges(G, Ts, S):
    """Edge list of the Haar graph of G with connection set S; A_g = g, B_h = G + h."""
    edges = []
    for s in S:
        row = Ts[s]
        for g in range(G):
            edges.append((g, G + int(row[g])))
    return edges


# ----------------------------------------------------------------------------
# Greedy pair insertion (kept from the parent). Each accepted step grows the order by 2
# and keeps every degree at d and the bipartition intact; lib.is_valid gates each step.
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
# Driver.
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

    # Safe fallback: K_{d,d}, which has diameter 2.
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

    # Haar-graph annealing over non-abelian groups; each success raises the target order.
    while time.monotonic() < search_deadline:
        target = best_n // 2 + 1 + rng.randrange(0, 4)
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        G, Ts, Invs = _semidirect_tables(m, k2, r)
        if G < d or 2 * G <= best_n or G > 3000:
            continue
        run_deadline = min(search_deadline, time.monotonic() + 8.0)
        S = _haar_search(d, D, G, Ts, Invs, rng, run_deadline, 30000)
        if S is not None:
            consider(2 * G, _haar_edges(G, Ts, S))

    # Grow the best graph with checked pair insertions.
    try:
        n2, e2 = _extend(best_n, best[1], d, D, rng, deadline)
        if n2 > best_n:
            consider(n2, e2)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
