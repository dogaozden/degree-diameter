import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact fallbacks.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d (diameter 3)."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# New family: single-layer bi-Cayley graphs over Z_m x| Z_k.
#
# Vertices A_g = g and B_h = G + h for g, h in Z_G-group elements. Choose d distinct
# connection elements S = {s_1..s_d}; A_g ~ B_{g*s} for every s in S. Left multiplication
# is an automorphism, so the graph is vertex-transitive on each side and it has diameter
# <= D iff A_0 and B_0 reach every vertex within D steps. The search is simulated
# annealing over S with the cost = number of (start, vertex) pairs still unreached.
# Group orders grow by bisection between a feasible lower bound and an infeasible upper
# bound. Every returned graph is checked with lib.is_valid.
# ----------------------------------------------------------------------------

_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)


def _group_tables(m, k, r):
    """Return (G, Ts, Invs) for Z_m x| Z_k, element (a, b) coded as a*k + b, (a,b)(c,e)=(a+r^b c, b+e).

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


def _pick_group(G, rng):
    """Return (m, k, r) with m*k = G, preferring non-abelian choices, or None."""
    if G < 2:
        return None
    divs = [k for k in range(2, min(G, 48) + 1) if G % k == 0 and G // k >= 2]
    if divs and rng.random() < 0.85:
        k = rng.choice(divs)
    else:
        k = 1
    m = G // k
    if k == 1:
        return (m, 1, 1)
    for _ in range(200):
        c = rng.randrange(2, m) if m > 2 else 1
        if math.gcd(c, m) == 1 and pow(c, k, m) == 1 % m:
            return (m, k, c)
    return None


def _set_row(nbr, l, G, Ts, Invs, s):
    """Write layer l: A_g -> B_{g*s} and B_h -> A_{h*s^-1}."""
    nbr[l, :G] = G + Ts[s]
    nbr[l, G:] = Invs[s]


def _reach(G, D, nbr):
    """Bitmask per vertex: bit 0 = reached from A_0, bit 1 = reached from B_0, within D steps."""
    N = 2 * G
    reach = np.zeros(N, dtype=np.int64)
    reach[0] = 1
    reach[G] = 2
    for _ in range(D):
        new = reach.copy()
        for l in range(nbr.shape[0]):
            new |= reach[nbr[l]]
        if np.array_equal(new, reach):
            break
        reach = new
    return reach


def _cost(G, reach):
    """Number of unreached (start, vertex) pairs."""
    return 2 * (2 * G) - int(_POP[reach].sum())


def _sa(G, Ts, Invs, d, D, rng, iters, deadline):
    """Anneal a d-element connection set S in the group so that the graph has diameter <= D.

    Returns the list S on success or None.
    """
    if d > G:
        return None
    S = rng.sample(range(G), d)
    nbr = np.empty((d, 2 * G), dtype=np.int64)
    for l in range(d):
        _set_row(nbr, l, G, Ts, Invs, S[l])
    cost = _cost(G, _reach(G, D, nbr))
    for t in range(iters):
        if cost == 0:
            break
        if (t & 255) == 0 and time.monotonic() > deadline:
            break
        temp = 2.0 * (1.0 - t / iters) + 0.05
        l = rng.randrange(d)
        new = rng.randrange(G)
        if new in S:
            continue
        old = S[l]
        S[l] = new
        _set_row(nbr, l, G, Ts, Invs, new)
        c2 = _cost(G, _reach(G, D, nbr))
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost = c2
        else:
            S[l] = old
            _set_row(nbr, l, G, Ts, Invs, old)
    return S if cost == 0 else None


def _cayley_edges(G, Ts, S):
    """Edges (g, G + g*s) for s in S, g in the group. Distinct s give distinct edges."""
    edges = []
    for s in S:
        row = Ts[s]
        for g in range(G):
            edges.append((g, G + int(row[g])))
    return edges


def _cayley_phase(d, D, rng, deadline, G0):
    """Bisection over the group order G: find the largest G with a valid single-layer lift.

    Returns (n, edges) for the best graph found, or None.
    """
    best = None
    lo, hi = G0, None
    while time.monotonic() < deadline:
        if hi is None:
            G = lo + max(1, lo // 16)
        elif hi - lo <= 1:
            G = lo + 1
        else:
            G = (lo + hi) // 2
        ok = False
        for _ in range(6):
            if time.monotonic() > deadline:
                break
            grp = _pick_group(G, rng)
            if grp is None:
                continue
            m, k, r = grp
            Gg, Ts, Invs = _group_tables(m, k, r)
            S = _sa(Gg, Ts, Invs, d, D, rng, 3000, deadline)
            if S is not None:
                cand_n, cand_e = 2 * Gg, _cayley_edges(Gg, Ts, S)
                if lib.is_valid(cand_n, cand_e, d, D):
                    best = (cand_n, cand_e)
                    ok = True
                    break
        if ok:
            lo = G
        elif hi is None or G < hi:
            hi = G
    return best


# ----------------------------------------------------------------------------
# Greedy pair insertion (order +2 per accepted step, degree preserved).
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
    """Repeatedly remove d-1 edges with distinct endpoints and add two vertices x (colour 0), y (colour 1).

    Each step is accepted only if lib.is_valid still passes.
    """
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
    budget = max(1.0, min(0.88 * time_limit, time_limit - 8.0))
    deadline = start + budget
    search_deadline = start + 0.82 * budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
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

    # Main new construction: single-layer bi-Cayley search over groups.
    if D >= 3 and d >= 2:
        try:
            res = _cayley_phase(d, D, rng, search_deadline, max(d, best_n // 2))
            if res is not None:
                consider(res[0], res[1])
        except Exception:
            pass

    # Greedy pair insertion on the best graph found so far.
    try:
        n2, e2 = _extend(best_n, best[1], d, D, rng, deadline)
        if n2 > best_n:
            consider(n2, e2)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
