"""Bold variant for d6D5: non-Haar voltage lifts of small base graphs.

Base graph: k A-vertices and k B-vertices, each with exactly d darts (one per permutation
of a random d-tuple of perfect matchings between A and B).  A dart (i, j, g) joins
(x, A_i) to (x*g, B_j) for every group element x.  The lift has 2*k*|G| vertices and is
bipartite, with degree at most d.

Left multiplication by any h in G is an automorphism of the lift, and it acts regularly on
each fibre.  So the lift has diameter <= D iff the BFS ball of radius D around the single
representative (identity, base vertex b) covers the whole graph, for each of the 2k base
vertices.  The search hill-climbs on dart voltages with this cost (uncovered pairs), with
restarts.  Groups are cyclic Z_M or metacyclic Z_a x| Z_b, with several base sizes k.

Safe fallback: a valid order-330 Haar graph on a metacyclic group (660 vertices).  Every
returned graph is checked with lib.is_valid.
"""
import math
import time

import numpy as np

import lib

TARGET = (6, 5)


def _trivial(d, D):
    """Small always-valid graph for any (d, D) other than the target."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


def _sanitize(d, D, res):
    """Return res if it is valid, else a trivially valid graph."""
    try:
        if res is not None and lib.is_valid(res[0], res[1], d, D):
            return res
    except Exception:
        pass
    return (1, [])


def _fallback(d, D):
    """Valid Haar graph on Z_33 x| Z_10 (order 330, 660 vertices), or None."""
    try:
        M, mul, _ = lib.semidirect_group(33, 10, 26)
        T = [[mul(x, y) for y in range(M)] for x in range(M)]
        S = [0, 179, 116, 180, 47, 306]
        n = 2 * M
        edges = [(g, M + T[s][g]) for s in S for g in range(M)]
        if lib.is_valid(n, edges, d, D):
            return (n, edges)
    except Exception:
        pass
    return None


def _candidates(lo, hi):
    """(total vertices, k, M, semidirect params or None), sorted by vertex count."""
    out = []
    for k in range(2, 9):
        for M in range(-(-lo // (2 * k)), hi // (2 * k) + 1):
            n = 2 * k * M
            out.append((n, k, M, None))
            for a in range(3, M):
                if M % a:
                    continue
                b = M // a
                if b < 2:
                    continue
                rs = [r for r in range(2, a) if math.gcd(r, a) == 1 and pow(r, b, a) == 1]
                for r in rs[:2]:
                    out.append((n, k, M, (a, b, r)))
    out.sort(key=lambda t: (t[0], t[3] is not None))
    return out[:24]


def _group_table(M, params):
    """Multiplication table T[x][y] of the group (cyclic if params is None, else semidirect)."""
    if params is None:
        return [[(x + y) % M for y in range(M)] for x in range(M)]
    a, b, r = params
    order, mul, _ = lib.semidirect_group(a, b, r)
    assert order == M
    return [[mul(x, y) for y in range(M)] for x in range(M)]


def _adj(k, M, T, darts):
    """Adjacency lists of the lift of the base graph with the given darts."""
    n = 2 * k * M
    adj = [[] for _ in range(n)]
    for u, v, g in darts:
        ub, vb = u * M, v * M
        for x in range(M):
            a = ub + x
            b = vb + T[x][g]
            adj[a].append(b)
            adj[b].append(a)
    return adj


def _cost(k, M, adj, D):
    """Total number of (representative, vertex) pairs at distance > D; 0 iff the lift has diameter <= D."""
    n = len(adj)
    total = 0
    for b in range(2 * k):
        rep = b * M
        seen = bytearray(n)
        seen[rep] = 1
        frontier = [rep]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for w in adj[u]:
                    if not seen[w]:
                        seen[w] = 1
                        nxt.append(w)
            cnt += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += n - cnt
    return total


def _try_candidate(k, M, T, deadline, rng, d, D):
    """Hill-climb voltages (with restarts) until the lift has diameter <= D; return (n, edges) or None."""
    mul = lambda x, g: T[x][g]
    while time.monotonic() < deadline:
        darts = []
        for _ in range(d):
            perm = rng.permutation(k)
            for i in range(k):
                darts.append([i, k + int(perm[i]), int(rng.integers(M))])
        adj = _adj(k, M, T, darts)
        cur = _cost(k, M, adj, D)
        stuck = 0
        while time.monotonic() < deadline:
            if cur == 0:
                n, edges = lib.group_lift(2 * k, [tuple(x) for x in darts], M, mul)
                if lib.is_valid(n, edges, d, D):
                    return n, edges
                break
            t = int(rng.integers(len(darts)))
            old = darts[t][2]
            new = int(rng.integers(M))
            if new == old:
                continue
            darts[t][2] = new
            nadj = _adj(k, M, T, darts)
            c = _cost(k, M, nadj, D)
            if c <= cur or rng.random() < math.exp(-(c - cur) / 0.8):
                stuck = 0 if c < cur else stuck + 1
                cur, adj = c, nadj
            else:
                darts[t][2] = old
                stuck += 1
            if stuck > 1500:
                break
    return None


def _search_target(d, D, seed, time_limit, t0):
    deadline_all = t0 + 0.70 * time_limit
    best = _fallback(d, D)
    rng = np.random.default_rng(seed)
    cands = _candidates(662, 700)
    for idx, (n_tot, k, M, params) in enumerate(cands):
        now = time.monotonic()
        if now >= deadline_all:
            break
        if best is not None and n_tot <= best[0]:
            continue
        remaining = deadline_all - now
        share = remaining / (len(cands) - idx)
        try:
            T = _group_table(M, params)
            res = _try_candidate(k, M, T, now + share, rng, d, D)
        except Exception:
            res = None
        if res is not None and (best is None or res[0] > best[0]):
            best = res
    return best


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if (d, D) != TARGET:
        return _sanitize(d, D, _trivial(d, D))
    try:
        res = _search_target(d, D, seed, time_limit, t0)
    except Exception:
        res = None
    if res is None:
        res = _fallback(d, D)
    return _sanitize(d, D, res) if res is not None else _sanitize(d, D, _trivial(d, D))
