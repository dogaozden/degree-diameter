"""Bipartite (d, D) graph builder.

Families, in order of use:
  1. K_{d,d} fallback (valid for D >= 2).
  2. For D = 3: projective-plane incidence graph PG(2, q) and the Araujo-Pardo-Lopez graph.
  3. Non-abelian bi-Cayley (Haar-type) graphs over semidirect products Z_m x| Z_k.
     A graph on 2N vertices is A_g ~ B_{g*s} for s in S, |S| = d. It is bipartite and
     d-regular. Left multiplication is an automorphism, so the diameter is <= D iff BFS from
     A_e and from B_e reach everything within D steps. S is found by simulated annealing.
     N is raised one step at a time (a "ratchet") toward the Moore bound, using all groups
     of order N.
Every candidate passes lib.is_valid before it replaces the current best.
"""
import math
import random
import time

import lib


# ----------------------------------------------------------------- D = 3 families

def _pg_candidates(d):
    """PG(2, q) incidence (degree q+1 <= d) and Araujo-Pardo-Lopez (degree d) when they apply."""
    out = []
    for q in range(min(d - 1, 31), 1, -1):
        if lib.is_prime_power(q):
            out.append(lib.projective_plane_incidence(q))
            break
    if d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            out.append(lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass
    return out


# ------------------------------------------------- bi-Cayley over semidirect groups

def _group_options(N):
    """All (m, k, r) with m*k = N giving Z_m x| Z_k (r = 1 when k = 1, and m = 1 gives Z_N)."""
    opts = []
    for m in range(1, N + 1):
        if N % m:
            continue
        k = N // m
        if m == 1:
            opts.append((1, k, 0))
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1:
                opts.append((m, k, r))
    return opts


def _ctx(N, m, k, r):
    """Right-multiplication permutations (cached per element) and inverse table."""
    _, mul, inv = lib.semidirect_group(m, k, r)
    cache = {}

    def perm(s):
        p = cache.get(s)
        if p is None:
            p = [mul(g, s) for g in range(N)]
            cache[s] = p
        return p

    inv_t = [inv(x) for x in range(N)]
    return perm, inv_t


def _bad(src, adj, total, D):
    """Number of vertices NOT within distance D of src."""
    seen = bytearray(total)
    seen[src] = 1
    frontier = [src]
    cnt = 1
    for _ in range(D):
        nxt = []
        for u in frontier:
            for v in adj[u]:
                if not seen[v]:
                    seen[v] = 1
                    nxt.append(v)
        if not nxt:
            break
        cnt += len(nxt)
        frontier = nxt
    return total - cnt


def _eval(N, S, perm, inv_t, D):
    """Cost (unreached pairs from A_e and B_e) and adjacency for connection set S."""
    Ps = [perm(s) for s in S]
    Qs = [perm(inv_t[s]) for s in S]
    total = 2 * N
    adj = [None] * total
    for g in range(N):
        adj[g] = [N + p[g] for p in Ps]
    for h in range(N):
        adj[N + h] = [q[h] for q in Qs]
    return _bad(0, adj, total, D) + _bad(N, adj, total, D), adj


def _anneal(N, d, D, perm, inv_t, rng, deadline, iters):
    """Anneal a d-subset S of Z-group elements so the bi-Cayley graph has diameter <= D."""
    if N < d:
        return None
    S = rng.sample(range(N), d)
    cost, adj = _eval(N, S, perm, inv_t, D)
    T = 0.8
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(d)
        x = rng.randrange(N)
        if x in S:
            continue
        S2 = list(S)
        S2[i] = x
        c2, adj2 = _eval(N, S2, perm, inv_t, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            S, cost, adj = S2, c2, adj2
        T = max(0.05, T * 0.998)
    return S if cost == 0 else None


def _edges(N, S, perm):
    """Edges A_g -- B_{g*s} for s in S, with A_g = g and B_h = N + h."""
    E = []
    for s in S:
        p = perm(s)
        for g in range(N):
            E.append((g, N + p[g]))
    return E


# ------------------------------------------------------------------------ build

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 2.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
            return True
        return False

    if D == 2:
        return best if lib.is_valid(best[0], best[1], d, D) else (1, [])

    if D == 3:
        for n, e in _pg_candidates(d):
            consider(n, e)

    cap = lib.moore_bound(d, D) // 2   # bipartite Haar graph has 2N vertices
    bestN = best[0] // 2

    try:
        while time.monotonic() < deadline:
            target = bestN + 1
            if target > cap:
                break
            if target + 1 <= cap and rng.random() < 0.25:
                target += 1
            groups = _group_options(target)
            rng.shuffle(groups)
            for m, k, r in groups:
                if time.monotonic() >= deadline:
                    break
                try:
                    perm, inv_t = _ctx(target, m, k, r)
                except ValueError:
                    continue
                S = _anneal(target, d, D, perm, inv_t, rng, deadline, 1500)
                if S is None:
                    continue
                if consider(2 * target, _edges(target, S, perm)):
                    bestN = best[0] // 2
                    break
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best[0], best[1]
