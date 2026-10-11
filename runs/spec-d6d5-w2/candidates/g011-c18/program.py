import math
import random
import time

import lib


def _pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d (order 2(q^2+q+1))."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _groups_of_order(N, rng):
    """Candidate groups of order N as (m, k, r) triples for lib.semidirect_group(m, k, r), shuffled."""
    out = [(N, 1, 1)]  # cyclic
    for k in range(2, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        units = [r for r in range(1, m)
                 if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        for r in rng.sample(units, min(len(units), 3)):
            out.append((m, k, r))
    rng.shuffle(out)
    return out


def _table(m, k, r):
    """Full multiplication and inverse tables of the group Z_m x| Z_k."""
    N, mul, inv_f = lib.semidirect_group(m, k, r)
    tab = [[mul(x, y) for y in range(N)] for x in range(N)]
    inv = [inv_f(x) for x in range(N)]
    return N, tab, inv


def _cost(N, tab, inv, S, D):
    """Bi-Cayley graph on A = G, B = G with A_x ~ B_{x s}, s in S.

    Left multiplication is an automorphism that is transitive on each side, so
    checking the BFS balls of A_e and B_e (radius D) is exact.
    Returns the number of unreached (source, vertex) pairs; zero means valid.
    """
    sinv = [inv[s] for s in S]
    total = 0
    for src in (0, N):
        seen = bytearray(2 * N)
        seen[src] = 1
        frontier = [src]
        reached = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < N:
                    row = tab[u]
                    for s in S:
                        v = N + row[s]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    row = tab[u - N]
                    for si in sinv:
                        v = row[si]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            if not nxt:
                break
            reached += len(nxt)
            frontier = nxt
        total += 2 * N - reached
    return total


def _anneal(N, tab, inv, d, D, rng, deadline, iters):
    """Anneal a connection set S of size d containing the identity (WLOG) until the cost is zero."""
    S = [0] + rng.sample(range(1, N), d - 1)
    cost = _cost(N, tab, inv, S, D)
    T = 2.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(1, d)
        g = rng.randrange(1, N)
        if g in S:
            continue
        T2 = S[:]
        T2[i] = g
        c2 = _cost(N, tab, inv, T2, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / max(T, 1e-3)):
            S, cost = T2, c2
        T = max(0.05, T * 0.998)
    return S if cost == 0 else None


def _edges(N, tab, S):
    """Edge list of the bi-Cayley graph: A_x = x, B_y = N + y, edges x -- N + x*s."""
    E = []
    for x in range(N):
        row = tab[x]
        for s in S:
            E.append((x, N + row[s]))
    return 2 * N, E


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.2, 0.85 * time_limit - 0.5)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D  # even cycle C_{2D}: bipartite, degree 2, diameter D
        return n, [(i, (i + 1) % n) for i in range(n)]

    # Safe fallback: K_{d,d} has diameter 2 and is optimal for D = 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best
    best_n = best[0]

    pg = _pg(d)
    if pg is not None and lib.is_valid(pg[0], pg[1], d, D) and pg[0] > best_n:
        best = pg
        best_n = pg[0]
        if D == 3:
            # Projective plane incidence meets the Moore bound for D = 3.
            return best

    # Bi-Cayley search: one orbit per side over groups of order N, grown one step at a time.
    N = max(d, best_n // 2 + 1)
    while time.monotonic() < deadline:
        groups = _groups_of_order(N, rng)
        found = None
        for grp in groups:
            if time.monotonic() >= deadline:
                break
            _, tab, inv = _table(*grp)
            S = _anneal(N, tab, inv, d, D, rng, deadline, 1000)
            if S is not None:
                found = (tab, S)
                break
        if found is None:
            continue  # retry this order with fresh random starts while time remains
        tab, S = found
        n, e = _edges(N, tab, S)
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n
        N += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
