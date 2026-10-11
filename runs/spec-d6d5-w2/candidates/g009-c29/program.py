"""Bipartite degree/diameter search.

New routine (this version): regular bipartite growth by edge splitting.
Start from K_{d,d}, which is valid for D >= 2. To add a pair of vertices
(a, b), pick d disjoint edges (x_t, y_t), delete them, and add (a, y_t) and
(x_t, b). Every vertex keeps degree exactly d and the graph stays bipartite.
Double-edge swaps then anneal the number of ordered pairs farther than D
apart down to zero.
"""
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Algebraic baselines for D = 3.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez graph for d = q + 2, q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# Cost: number of ordered vertex pairs at distance > D (zero iff valid).
# Bitset balls, radius D.
# ----------------------------------------------------------------------------

def _bad(N, adj, D):
    full = (1 << N) - 1
    ball = [1 << v for v in range(N)]
    for _ in range(D):
        new = []
        for v in range(N):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new.append(x)
        ball = new
        if all(b == full for b in ball):
            break
    return sum(N - b.bit_count() for b in ball)


def _adj(k, E):
    """Adjacency lists for a graph with A = 0..k-1 and B = k..2k-1; E holds local (a, b) pairs."""
    adj = [[] for _ in range(2 * k)]
    for a, b in E:
        adj[a].append(k + b)
        adj[k + b].append(a)
    return adj


def _rewire(adj, k, rem, add):
    for a, b in rem:
        adj[a].remove(k + b)
        adj[k + b].remove(a)
    for a, b in add:
        adj[a].append(k + b)
        adj[k + b].append(a)


# ----------------------------------------------------------------------------
# Edge-splitting vertex insertion (keeps regularity d and bipartiteness).
# ----------------------------------------------------------------------------

def _insert_pair(k, E, d, rng):
    """Add one A-vertex k and one B-vertex k using d disjoint edges. Returns (k+1, E') or None."""
    idx = list(range(len(E)))
    rng.shuffle(idx)
    usedA, usedB, chosen = set(), set(), []
    for t in idx:
        a, b = E[t]
        if a in usedA or b in usedB:
            continue
        usedA.add(a)
        usedB.add(b)
        chosen.append(t)
        if len(chosen) == d:
            break
    if len(chosen) < d:
        return None
    chosen_set = set(chosen)
    newE = [E[t] for t in range(len(E)) if t not in chosen_set]
    for t in chosen:
        a, b = E[t]
        newE.append((k, b))  # new A-vertex to b
        newE.append((a, k))  # a to new B-vertex
    return k + 1, newE


# ----------------------------------------------------------------------------
# Annealing by double-edge swaps (preserves regularity and bipartiteness).
# ----------------------------------------------------------------------------

def _anneal(k, E, D, iters, deadline, rng):
    E = list(E)
    m = len(E)
    N = 2 * k
    adj = _adj(k, E)
    cost = _bad(N, adj, D)
    best_cost, best_E = cost, list(E)
    S = set(E)
    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        frac = 1.0 - it / iters
        T = 0.05 + 0.5 * frac + 0.01 * cost * frac
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        if (a1, b2) in S or (a2, b1) in S:
            continue
        rem = [(a1, b1), (a2, b2)]
        add = [(a1, b2), (a2, b1)]
        _rewire(adj, k, rem, add)
        nc = _bad(N, adj, D)
        delta = nc - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = nc
            E[i] = (a1, b2)
            E[j] = (a2, b1)
            S.discard((a1, b1))
            S.discard((a2, b2))
            S.add((a1, b2))
            S.add((a2, b1))
            if cost < best_cost:
                best_cost, best_E = cost, list(E)
        else:
            _rewire(adj, k, add, rem)
    return best_cost, best_E


# ----------------------------------------------------------------------------
# Growth driver: insert pairs, anneal to zero bad pairs, keep the last success.
# ----------------------------------------------------------------------------

def _grow(d, D, moore, deadline, rng):
    k = d
    E = [(a, b) for a in range(d) for b in range(d)]  # K_{d,d}, valid for D >= 2
    best_k, best_E = k, E
    step = max(1, k // 20)
    iters = 300
    while time.monotonic() < deadline and 2 * k < moore:
        step = min(step, moore // 2 - k)
        if step < 1:
            break
        ck, cE = k, E
        ok = True
        for _ in range(step):
            r = _insert_pair(ck, cE, d, rng)
            if r is None:
                ok = False
                break
            ck, cE = r
        if not ok:
            break
        c, bE = _anneal(ck, cE, D, iters, deadline, rng)
        if c == 0:
            k, E = ck, bE
            best_k, best_E = k, E
            step = min(step * 2, max(1, k // 10))
            iters = max(300, iters // 2)
        else:
            if step > 1:
                step = max(1, step // 2)
            else:
                iters = min(iters * 2, 20000)
    return best_k, best_E


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]

    # Fallback: K_{d,d} has diameter 2, valid for D >= 2.
    fallback = lib.haar_graph(d, range(d))
    cands = [fallback]

    moore = lib.moore_bound(d, D)
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            cands.append(pg)
        ar = _araujo(d)
        if ar is not None:
            cands.append(ar)

    if D >= 2:
        k, E = _grow(d, D, moore, deadline, rng)
        n = 2 * k
        edges = [(a, k + b) for a, b in E]
        cands.append((n, edges))

    # Largest candidate that passes the exact checker wins.
    cands.sort(key=lambda c: -c[0])
    for n, e in cands:
        if lib.is_valid(n, e, d, D):
            return n, e
    return fallback
