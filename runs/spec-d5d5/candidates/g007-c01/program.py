import math
import random
import time

import lib

ITERS = 800            # annealing steps per (group) try
T_HOT = 2.0            # initial annealing temperature (unreached-pair units)
T_COLD = 0.1           # final annealing temperature
MAX_GROUPS = 12        # groups tried per (b, N) attempt
WINDOW = 6             # candidate orders N tried above the current best, per b
MAX_CANDS = 10         # candidate (b, N) pairs considered per round
TIME_FRAC = 0.8        # fraction of time_limit used for search


# ----------------------------------------------------------------------------
# Fallback families.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Multi-orbit bipartite voltage lifts over semidirect products Z_m x| Z_k.
#
# Base graph: b "A" vertices and b "B" vertices. Each A_i has d darts; each B_j
# receives exactly d darts (so degrees stay <= d). A dart (i, j, g) joins
# A_{i,x} to B_{j, x*g} for all x in G. Left multiplication is an automorphism,
# so the diameter is decided by BFS from A_{i,e} and B_{j,e} only (2b sources).
# b = 1 is the bi-Cayley case.
# ----------------------------------------------------------------------------

def _groups(N):
    """Return semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _cost(b, N, D, T, darts, ginv):
    """Total number of (source, vertex) pairs not within distance D over the 2b sources."""
    BN = b * N
    adjA = [[] for _ in range(b)]
    adjB = [[] for _ in range(b)]
    for i, j, g in darts:
        adjA[i].append((j, g))
        adjB[j].append((i, ginv[g]))
    total = 0
    for src in range(2 * b):
        s = src * N if src < b else BN + (src - b) * N
        seen = bytearray(2 * BN)
        seen[s] = 1
        frontier = [s]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < BN:
                    i, x = divmod(u, N)
                    row = T[x]
                    for j, g in adjA[i]:
                        v = BN + j * N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    j, y = divmod(u - BN, N)
                    row = T[y]
                    for i, h in adjB[j]:
                        v = i * N + row[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += 2 * BN - count
    return total


def _try_voltages(b, N, d, D, T, ginv, rng, deadline):
    """Simulated annealing over the voltages for one group. Returns darts or None."""
    nd = b * d
    Bslots = [j for j in range(b) for _ in range(d)]
    rng.shuffle(Bslots)
    iA = [k // d for k in range(nd)]
    gs = [rng.randrange(N) for _ in range(nd)]

    def mk(vals):
        return [(iA[k], Bslots[k], vals[k]) for k in range(nd)]

    cur = _cost(b, N, D, T, mk(gs), ginv)
    for it in range(ITERS):
        if cur == 0:
            return mk(gs)
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / ITERS)
        k = rng.randrange(nd)
        c = rng.randrange(N)
        if c == gs[k]:
            continue
        old = gs[k]
        gs[k] = c
        v = _cost(b, N, D, T, mk(gs), ginv)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            gs[k] = old
    return mk(gs) if cur == 0 else None


def _attempt(b, N, d, D, rng, deadline):
    """Try groups of order N for base size b. Returns (darts, T) or None."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            return None
        _, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        ginv = [inv(g) for g in range(N)]
        darts = _try_voltages(b, N, d, D, T, ginv, rng, deadline)
        if darts is not None:
            return darts, T
    return None


def _edges(b, N, T, darts):
    """Expand the base darts into the simple edge list of the lift."""
    BN = b * N
    edges = set()
    for i, j, g in darts:
        for x in range(N):
            edges.add((i * N + x, BN + j * N + T[x][g]))
    return 2 * BN, sorted(edges)


def _candidates(d, best_n, moore, banned):
    """(b, N) pairs giving more than best_n vertices, smallest vertex count first."""
    out = []
    for b in (1, 2, 3, 4):
        Nmax = moore // (2 * b)
        Nlo = max(best_n // (2 * b) + 1, 2)
        for N in range(Nlo, min(Nmax, Nlo + WINDOW) + 1):
            if (b, N) not in banned:
                out.append((2 * b * N, b, N))
    out.sort()
    return [(b, N) for _, b, N in out[:MAX_CANDS]]


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + TIME_FRAC * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = (1, [])
    best_n = 1

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n
            return True
        return False

    # Calibration case: incidence graph of PG(2, d-1) meets the bound.
    if D == 3 and d >= 2 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best

    # Always-valid baseline: a single edge (diameter 1).
    consider(2, [(0, 1)])
    if D >= 2 and d >= 2:
        consider(*lib.haar_graph(d, range(d)))
    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if d < 2 or D < 2:
        return best

    moore = lib._moore_bound(d, D)
    banned = set()
    budget = 0.5
    while time.monotonic() < deadline:
        cands = _candidates(d, best_n, moore, banned)
        if not cands:
            break
        progressed = False
        for b, N in cands:
            now = time.monotonic()
            if now >= deadline:
                break
            att_deadline = min(deadline, now + budget)
            res = _attempt(b, N, d, D, rng, att_deadline)
            if res is None:
                continue
            darts, T = res
            n, e = _edges(b, N, T, darts)
            if consider(n, e):
                progressed = True
                break
            banned.add((b, N))
        if not progressed:
            budget *= 2

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
