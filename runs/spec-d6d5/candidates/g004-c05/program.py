import math
import random
import time

import lib

_MAXG = 600  # cap on group order, keeps the multiplication table small


def _pg_fallback(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d (diameter 3)."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _group_options(G):
    """All (m, k, r) with Z_m x| Z_k of order G = m*k (k=1 gives the cyclic group)."""
    opts = []
    for k in range(1, G + 1):
        if G % k:
            continue
        m = G // k
        if m < 2:
            continue
        if k == 1:
            opts.append((m, 1, 1))
            continue
        for r in range(2, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                opts.append((m, k, r))
    return opts


def _pick(opts, rng):
    """Random group option, biased toward non-abelian semidirect products."""
    nonab = [o for o in opts if o[1] >= 2]
    if nonab and rng.random() < 0.85:
        return rng.choice(nonab)
    return rng.choice(opts)


class _Group:
    """Multiplication table of a finite group: R[s][g] = g*s, inv[s] = s^-1."""

    def __init__(self, m, k, r):
        G, mul, inv = lib.semidirect_group(m, k, r)
        self.G = G
        self.R = [[mul(g, s) for g in range(G)] for s in range(G)]
        self.inv = [inv(s) for s in range(G)]


# Bi-Cayley graph with one orbit per side: A-vertex g ~ B-vertex h iff g^-1 h in S.
# Left multiplication is an automorphism, so distances from the two identity
# vertices (one in A, one in B) determine the diameter exactly.

def _write_col(adj, G, Rs, Ri, i):
    """Write connection element s into slot i: A_g -> B_{g s}, B_h -> A_{h s^-1}."""
    for g in range(G):
        adj[g][i] = G + Rs[g]
    for h in range(G):
        adj[G + h][i] = Ri[h]


def _cost(adj, G, D):
    """Number of vertices not within distance D of A_e or B_e (zero iff diameter <= D)."""
    N = 2 * G
    total = 0
    for src in (0, G):
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


def _search(grp, d, D, rng, slice_end, iters):
    """Anneal a connection set S (|S| = d) in the group; returns S with diameter <= D or None."""
    G, R, inv = grp.G, grp.R, grp.inv
    N = 2 * G
    S = rng.sample(range(G), d)
    adj = [[0] * d for _ in range(N)]
    for i, s in enumerate(S):
        _write_col(adj, G, R[s], R[inv[s]], i)
    cur = _cost(adj, G, D)
    T = 2.0
    for _ in range(iters):
        if cur == 0 or time.monotonic() >= slice_end:
            break
        i = rng.randrange(d)
        x = rng.randrange(G)
        if x in S:
            continue
        old = S[i]
        S[i] = x
        _write_col(adj, G, R[x], R[inv[x]], i)
        new = _cost(adj, G, D)
        if new <= cur or rng.random() < math.exp((cur - new) / T):
            cur = new
        else:
            S[i] = old
            _write_col(adj, G, R[old], R[inv[old]], i)
        T = max(0.15, T * 0.997)
    if cur == 0:
        return list(S)
    return None


def _edges_of(grp, S):
    """Edge list of the bi-Cayley graph for connection set S."""
    G = grp.G
    E = []
    for s in S:
        Rs = grp.R[s]
        for g in range(G):
            E.append((g, G + Rs[g]))
    return 2 * G, E


def _bicayley(d, D, rng, deadline, floorG, startG, consider):
    """Search group orders G (graph order 2G), bisecting between known-feasible and failed values."""
    bestG = floorG - 1
    hiG = _MAXG + 1
    tryG = startG
    fails = 0
    while time.monotonic() < deadline and tryG <= _MAXG:
        now = time.monotonic()
        slice_end = min(deadline, now + max(1.5, 0.15 * (deadline - now)))
        opts = _group_options(tryG)
        if not opts:
            break
        hit = None
        while time.monotonic() < slice_end:
            m, k, r = _pick(opts, rng)
            grp = _Group(m, k, r)
            S = _search(grp, d, D, rng, slice_end, 1200)
            if S is not None:
                hit = (grp, S)
                break
        if hit is not None:
            n, e = _edges_of(hit[0], hit[1])
            consider(n, e)
            bestG = tryG
            fails = 0
        else:
            fails += 1
            if fails < 2:
                continue  # retry the same order with fresh random groups
            hiG = min(hiG, tryG)
            fails = 0
        if hiG - bestG > 1:
            tryG = (bestG + hiG) // 2
        else:
            tryG = bestG + 1


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2 or d == 1:
        return best
    if d == 2:
        n = 2 * D  # even cycle C_{2D}: diameter D, bipartite
        consider(n, [(i, (i + 1) % n) for i in range(n)])
        return best

    pg = _pg_fallback(d)
    if pg is not None:
        consider(pg[0], pg[1])

    moore = 2 * sum((d - 1) ** i for i in range(D))
    floorG = best_n // 2 + 1
    if best_n >= moore or floorG > _MAXG:
        return best

    startG = min(_MAXG, max(floorG, int(0.2 * moore)))
    _bicayley(d, D, rng, deadline, floorG, startG, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
