"""Multi-base voltage lifts with a 2*nb-source eccentricity cost.

Vertices are A_{i,x} and B_{j,y} for base indices i, j in 0..nb-1 and group elements
x, y in G, with |G| = N. Each dart (i, j, g) adds the edges A_{i,x} -- B_{j, x*g} for all x.
Left multiplication by G is an automorphism, so eccentricities need only be checked from
A_{i,e} and B_{j,e} for every base index: 2*nb BFS runs instead of 2*nb*N. Each A_i gets
degree d, each B_j gets degree d, and parallel darts in the same (i, j) class carry distinct
voltages, so the graph is simple and bipartite. Annealing moves one voltage at a time and
minimises the number of (source, vertex) pairs left beyond distance D. Nb = 2 gives
order 4N, which is the main target.
"""
import math
import random
import time

import lib

ITERS = 500
MAX_GROUPS = 8
T_HOT = 1.2
T_COLD = 0.1
BUDGET_START = 1.5
BUDGET_CAP = 8.0


def _groups(N):
    """Semidirect parameters (m, k, r) giving every group Z_m x|_r Z_k of order N."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _layout(nb, d, rng):
    """Base multigraph: one (i, j) entry per dart. Each base vertex has degree d on both sides."""
    if nb == 1:
        return [(0, 0)] * d
    p = rng.randint(1, d - 1)
    return [(0, 0)] * p + [(0, 1)] * (d - p) + [(1, 0)] * (d - p) + [(1, 1)] * p


def _cost(nb, N, D, mulT, invs, darts):
    """Sum over the 2*nb base sources of vertices NOT within distance D (0 means diameter <= D)."""
    BN = nb * N
    V = 2 * BN
    adjA = [[] for _ in range(nb)]
    adjB = [[] for _ in range(nb)]
    for i, j, g in darts:
        adjA[i].append((j, g))
        adjB[j].append((i, invs[g]))
    sources = [i * N for i in range(nb)] + [BN + j * N for j in range(nb)]
    total = 0
    for src in sources:
        seen = bytearray(V)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < BN:
                    i, x = divmod(u, N)
                    row = mulT[x]
                    for j, g in adjA[i]:
                        v = BN + j * N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    j, y = divmod(u - BN, N)
                    row = mulT[y]
                    for i, h in adjB[j]:
                        v = i * N + row[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            if not nxt:
                break
            frontier = nxt
        total += V - count
    return total


def _anneal(nb, N, D, mulT, invs, layout, rng, deadline):
    """Anneal voltages on the fixed base layout; return darts with cost 0, or None."""
    darts = []
    for i, j in layout:
        while True:
            g = rng.randrange(N)
            if not any(di == i and dj == j and dg == g for di, dj, dg in darts):
                break
        darts.append((i, j, g))
    cur = _cost(nb, N, D, mulT, invs, darts)
    for it in range(ITERS):
        if cur == 0:
            return darts
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / ITERS)
        s = rng.randrange(len(darts))
        i, j, _ = darts[s]
        g = rng.randrange(N)
        if any(di == i and dj == j and dg == g for di, dj, dg in darts):
            continue
        new = darts[:]
        new[s] = (i, j, g)
        v = _cost(nb, N, D, mulT, invs, new)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            darts, cur = new, v
    return darts if cur == 0 else None


def _attempt(nb, N, d, D, rng, deadline):
    """Try several groups of order N and one random base layout until a valid lift appears."""
    groups = _groups(N)
    rng.shuffle(groups)
    layout = _layout(nb, d, rng)
    for gm, gk, gr in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            return None
        _, mul, inv = lib.semidirect_group(gm, gk, gr)
        mulT = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        darts = _anneal(nb, N, D, mulT, invs, layout, rng, deadline)
        if darts is not None:
            return nb, N, mulT, darts
    return None


def _edges(nb, N, mulT, darts):
    BN = nb * N
    out = []
    for i, j, g in darts:
        for x in range(N):
            out.append((i * N + x, BN + j * N + mulT[x][g]))
    return out


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit - 1.0
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = (1, [])

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact record-matching case: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best

    if D >= 2:
        consider(*lib.haar_graph(d, range(d)))
    if D == 3 and d >= 5 and lib.is_prime_power(d - 2):
        try:
            consider(*lib.araujo_lopez_graph(d - 2))
        except ValueError:
            pass

    if d < 1 or D < 2:
        return best

    moore = lib._moore_bound(d, D)
    win = 6
    budget = BUDGET_START

    while time.monotonic() < deadline:
        best_n = best[0]
        nb = 2 if (d >= 2 and rng.random() < 0.8) else 1
        hi = moore // (2 * nb)
        lo = max(best_n // (2 * nb) + 1, d + 1)
        if lo > hi:
            if nb == 2:
                continue
            break
        N = rng.randint(lo, min(hi, lo + win - 1))
        now = time.monotonic()
        att_deadline = min(deadline, now + budget)
        res = _attempt(nb, N, d, D, rng, att_deadline)
        if res is None:
            win = min(win + 1, max(1, hi - lo + 1))
            budget = min(BUDGET_CAP, budget * 1.5)
            continue
        nb_r, N_r, mulT, darts = res
        consider(2 * nb_r * N_r, _edges(nb_r, N_r, mulT, darts))

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
