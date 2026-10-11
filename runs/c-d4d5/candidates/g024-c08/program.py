"""Bold variant: Haar graphs over finite groups instead of the earlier C lift search.

Construction: for a group G of order N, a connection set S of size d, and the bipartite graph
with parts A = G and B = G, joining A_g to B_{gs} for s in S. Left multiplication by h is an
automorphism (A_g -> A_{hg}, B_x -> B_{hx}), so G acts transitively on each side. A diameter
check therefore only needs BFS from A_e and B_e. This gives a valid d-regular graph on 2N vertices
with diameter <= D exactly when both BFS trees reach everything within D steps.

Search: for N increasing from the current best, sample groups Z_m x|_r Z_k with m*k = N, then
hill-climb S to drive the number of unreached (source, vertex) pairs to zero. Every accepted graph
is checked with lib.is_valid. Algebraic starts (projective planes, Araujo-Pardo-Lopez, W(q)) and
K_{d,d} remain as fallbacks, so every case returns a valid graph.
"""
import itertools
import math
import random
import time

import lib


def _gq_w(q):
    """Incidence graph of points and lines of W(q): degree q+1, diameter 4."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _largest_prime_power_le(x):
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def known_starts(d, D):
    """Algebraic candidates valid for diameter D (may be empty)."""
    out = []
    if D >= 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        out.append(lib.projective_plane_incidence(d - 1))
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        out.append(lib.araujo_lopez_graph(d - 2))
    if D >= 4:
        q = _largest_prime_power_le(min(d - 1, 9))
        if q is not None and q >= 2:
            out.append(_gq_w(q))
    return out


def _bfs_bad(n2, adj, D, sources):
    """Number of (source, vertex) pairs not reached within D steps, summed over the sources."""
    bad = 0
    for s in sources:
        dist = [-1] * n2
        dist[s] = 0
        frontier = [s]
        seen = 1
        for depth in range(D):
            nxt = []
            for v in frontier:
                for u in adj[v]:
                    if dist[u] < 0:
                        dist[u] = depth + 1
                        nxt.append(u)
            seen += len(nxt)
            frontier = nxt
            if not frontier:
                break
        bad += n2 - seen
    return bad


def _haar_bad(tab, invs, N, S, D):
    """Bad-pair count of the Haar graph over the group (tab = multiplication table)."""
    adj = [[N + tab[g][s] for s in S] for g in range(N)]
    adj += [[tab[h][invs[s]] for s in S] for h in range(N)]
    return _bfs_bad(2 * N, adj, D, [0, N])


def _groups(N, rng):
    """Semidirect groups Z_m x|_r Z_k of order N = m*k, shuffled."""
    out = []
    for m in range(1, N + 1):
        if N % m:
            continue
        k = N // m
        for r in range(1, max(m, 2)):
            if m > 1 and math.gcd(r, m) != 1:
                continue
            if pow(r, k, m) != 1 % m:
                continue
            out.append((m, k, r))
    rng.shuffle(out)
    return out


def _table(m, k, r):
    """Multiplication and inverse tables of the group Z_m x|_r Z_k."""
    N, mul, inv = lib.semidirect_group(m, k, r)
    tab = [[mul(x, y) for y in range(N)] for x in range(N)]
    invs = [inv(x) for x in range(N)]
    return tab, invs


def _climb(tab, invs, N, d, D, steps, rng, deadline):
    """Hill-climb a d-element connection set S until the Haar graph has diameter <= D."""
    S = rng.sample(range(N), d)
    bad = _haar_bad(tab, invs, N, S, D)
    for _ in range(steps):
        if bad == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(d)
        new = rng.randrange(N)
        if new in S:
            continue
        old = S[i]
        S[i] = new
        nb = _haar_bad(tab, invs, N, S, D)
        if nb <= bad or rng.random() < 0.05:
            bad = nb
        else:
            S[i] = old
    return list(S) if bad == 0 else None


def _find_haar(N, d, D, deadline, rng):
    """Try to find a valid Haar graph of order 2N; returns (tab, invs, S) or None."""
    if N < d:
        return None
    for (m, k, r) in _groups(N, rng)[:12]:
        if time.monotonic() > deadline:
            break
        try:
            tab, invs = _table(m, k, r)
        except ValueError:
            continue
        for _ in range(2):
            S = _climb(tab, invs, N, d, D, 200, rng, deadline)
            if S is not None:
                return tab, invs, S
    return None


def _haar_growth(d, D, start_n, best, deadline, rng):
    """Grow the best Haar-type graph by one group order at a time. Returns the best (n, edges)."""
    N = start_n // 2 + 1
    upper = lib.moore_bound(d, D) // 2
    while N <= upper and time.monotonic() < deadline:
        hit = _find_haar(N, d, D, deadline, rng)
        if hit is None:
            break
        tab, invs, S = hit
        edges = [(g, N + tab[g][s]) for g in range(N) for s in S]
        if lib.is_valid(2 * N, edges, d, D) and 2 * N > best[0]:
            best = (2 * N, edges)
        N += 1
    return best


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D
        return L, [(i, (i + 1) % L) for i in range(L)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}: always valid for D >= 2
    for cand in known_starts(d, D):
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D < 2 or best[0] >= lib.moore_bound(d, D):
        return best

    deadline = t0 + 0.85 * time_limit - 1.0
    if deadline - time.monotonic() < 1.0:
        return best

    rng = random.Random(seed * 7919 + 13 * d + D)
    try:
        cand = _haar_growth(d, D, best[0], best, deadline, rng)
        if cand[0] > best[0] and lib.is_valid(cand[0], cand[1], d, D):
            best = cand
    except Exception:
        pass
    return best
