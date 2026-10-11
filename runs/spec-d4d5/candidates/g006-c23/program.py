import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Safe fallbacks.
# ----------------------------------------------------------------------------

def _pg_fallback(d):
    """Incidence graph of PG(2, d-1) when d-1 is a prime power (diameter 3)."""
    q = d - 1
    if q >= 2 and lib.is_prime_power(q):
        return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Group sampling. Groups are semidirect products Z_m x| Z_k (lib.semidirect_group),
# which cover cyclic, direct-product and dihedral-type groups.
# ----------------------------------------------------------------------------

def _sample_groups(G, rng, count):
    """Return up to `count` random groups of order G as (mul_table, inv_list) pairs."""
    cands = []
    for k in range(1, min(G, 12) + 1):
        if G % k:
            continue
        m = G // k
        if m == 1:
            rs = [0]
        elif k == 1:
            rs = [1]
        else:
            rs = [r for r in range(1, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1]
            if len(rs) > 20:
                rs = rng.sample(rs, 20)
        for r in rs:
            cands.append((m, k, r))
    rng.shuffle(cands)
    out = []
    for m, k, r in cands[:count]:
        order, mul, inv_f = lib.semidirect_group(m, k, r)
        if order != G:
            continue
        T = [[mul(x, y) for y in range(G)] for x in range(G)]
        inv = [inv_f(x) for x in range(G)]
        out.append((T, inv))
    return out


# ----------------------------------------------------------------------------
# Shared BFS cost: number of (source, vertex) pairs not reached within depth D.
# ----------------------------------------------------------------------------

def _bfs_missing(N, adj, sources, D):
    total = 0
    for src in sources:
        seen = bytearray(N)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += N - count
    return total


# ----------------------------------------------------------------------------
# Phase 1: bi-Cayley graphs. Vertices A_g = g and B_h = G + h, with A_g adjacent to
# B_{g*s} for s in S (|S| = d). Left translations are automorphisms, so the diameter
# is at most D iff every vertex is within D of A_e and of B_e. This is a different
# family from the k-base voltage lifts, and the search is a hill-climb over S.
# ----------------------------------------------------------------------------

def _bc_adj(G, T, inv, S):
    adj = [None] * (2 * G)
    for g in range(G):
        Tg = T[g]
        adj[g] = [G + Tg[s] for s in S]
    for h in range(G):
        Th = T[h]
        adj[G + h] = [Th[inv[s]] for s in S]
    return adj


def _search_bc(d, D, G, T, inv, rng, iters, deadline):
    if G < d:
        return None
    S = rng.sample(range(G), d)
    c = _bfs_missing(2 * G, _bc_adj(G, T, inv, S), (0, G), D)
    for it in range(iters):
        if c == 0:
            return S
        if (it & 31) == 0 and time.monotonic() > deadline:
            break
        i = rng.randrange(d)
        x = rng.randrange(G)
        if x in S:
            continue
        S2 = S[:]
        S2[i] = x
        c2 = _bfs_missing(2 * G, _bc_adj(G, T, inv, S2), (0, G), D)
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / 0.7):
            S, c = S2, c2
    return S if c == 0 else None


def _phase_bicayley(d, D, G0, Gmax, rng, deadline, consider):
    G = G0
    while G <= Gmax and time.monotonic() < deadline:
        for T, inv in _sample_groups(G, rng, 3):
            if time.monotonic() >= deadline:
                break
            S = _search_bc(d, D, G, T, inv, rng, 500, deadline)
            if S is not None:
                adj = _bc_adj(G, T, inv, S)
                edges = [(g, v) for g in range(G) for v in adj[g]]
                consider(2 * G, edges)
                break
        G += 1


# ----------------------------------------------------------------------------
# Phase 2: annealed voltage lifts over small semidirect groups with k base
# vertices per side. Used as a fallback so the search never ends below what the
# parent's lift search reaches.
# ----------------------------------------------------------------------------

def _lift_adj(k, G, darts, perms):
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            a = i * G + g
            b = (k + j) * G + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    return N, adj


def _anneal_lift(d, D, k, G, T, rng, deadline, iters):
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [[T[g][s] for g in range(G)] for _, _, s in darts]
    sources = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]

    def cst():
        N, adj = _lift_adj(k, G, darts, perms)
        return _bfs_missing(N, adj, sources, D)

    cost = cst()
    for it in range(iters):
        if cost == 0:
            break
        if (it & 15) == 0 and time.monotonic() > deadline:
            break
        temp = 1.0 * (0.05 ** (it / iters))
        if k == 1 or rng.random() < 0.7:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_p = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = [T[g][new_s] for g in range(G)]
            c2 = cst()
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_p
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = cst()
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost != 0:
        return None
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _phase_lifts(d, D, rng, deadline, best, consider):
    while time.monotonic() < deadline:
        k = rng.choice([1, 2, 2, 3])
        G = max(2, best[0] // (2 * k) + 1 + rng.randrange(0, 4))
        for T, _inv in _sample_groups(G, rng, 2):
            if time.monotonic() >= deadline:
                return
            res = _anneal_lift(d, D, k, G, T, rng, deadline, 2000)
            if res is not None:
                consider(res[0], res[1])


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    hard = start + 0.8 * time_limit
    span = hard - start
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    fb_n, fb_e = lib.haar_graph(d, range(d))
    best = [fb_n, fb_e]

    def consider(n, e):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best[0], best[1] = n, e

    if D >= 3:
        pg = _pg_fallback(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Phase 1 (half the budget): bi-Cayley search, ascending in group order.
    p1 = start + 0.5 * span
    G0 = max(d, best[0] // 2 + 1, 2)
    _phase_bicayley(d, D, G0, G0 + 80, rng, p1, consider)

    # Phase 2 (rest): annealed voltage lifts.
    _phase_lifts(d, D, rng, hard, best, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        best = [fb_n, fb_e]
    return best[0], best[1]
