import math
import random
import time

import lib

ITERS = 500           # annealing steps per (group, base pattern) try
T_HOT = 1.5           # initial temperature (unreached-pair units)
T_COLD = 0.15         # final temperature
MAX_GROUPS = 10       # metacyclic groups tried per order N within one attempt
BUDGET_START = 1.0    # seconds per order-N attempt in the first pass
BUDGET_CAP = 6.0      # cap on per-attempt seconds as passes fail
PHASE2_FRAC = 0.6     # share of the search time given to the 2-orbit phase


# ----------------------------------------------------------------------------
# Baseline families (cheap, validated before use).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Multi-orbit group lifts.
#
# Base bipartite graph: p "A-orbits" and p "B-orbits", each orbit a copy of a
# finite group G of order N. A dart (i, j, g) joins A_{i,x} to B_{j, x*g} for
# all x in G. Pattern C[i][j] = number of darts from A_i to B_j, with every row
# and column summing to d, so each lifted vertex has degree exactly d.
#
# Left multiplication by h in G maps A_{i,x} to A_{i,hx} and B_{j,y} to B_{j,hy},
# and it is an automorphism of the lift. So every vertex is equivalent to the
# identity vertex of its orbit. Diameter <= D therefore only needs BFS from the
# 2p sources A_{i,e} and B_{j,e}, not from all vertices.
#
# p = 1 is the single-orbit bi-Cayley graph. p = 2 uses four orbits (4N
# vertices) with a 2x2 base pattern, which lets smaller groups reach orders
# that a single orbit cannot.
# ----------------------------------------------------------------------------

def _groups(N):
    """Semidirect parameters (m, k, r) for Z_m x|_r Z_k of order N."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _patterns(d):
    """Connected 2x2 base patterns with all row and column sums equal to d."""
    return [[[k, d - k], [d - k, k]] for k in range(1, d)]


def _adjacency(p, pairs, vol, invs):
    """Per-orbit dart lists: outA[i] = [(j, g)], inB[j] = [(i, g^-1)]."""
    outA = [[] for _ in range(p)]
    inB = [[] for _ in range(p)]
    for s, (i, j) in enumerate(pairs):
        g = vol[s]
        outA[i].append((j, g))
        inB[j].append((i, invs[g]))
    return outA, inB


def _unreached(N, p, T, invs, pairs, vol, D):
    """Count (source, vertex) pairs at distance > D over the 2p orbit representatives."""
    outA, inB = _adjacency(p, pairs, vol, invs)
    Boff = p * N
    V = 2 * p * N
    total = 0
    sources = [i * N for i in range(p)] + [Boff + j * N for j in range(p)]
    for src in sources:
        seen = bytearray(V)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < Boff:
                    i, x = divmod(u, N)
                    row = T[x]
                    for j, g in outA[i]:
                        v = Boff + j * N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    j, y = divmod(u - Boff, N)
                    row = T[y]
                    for i, h in inB[j]:
                        v = i * N + row[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += V - count
    return total


def _anneal(N, p, T, invs, pairs, D, rng, iters, deadline):
    """Anneal dart voltages to zero unreached pairs. Darts sharing a pair must get distinct voltages."""
    L = len(pairs)
    same = [[t for t in range(L) if t != s and pairs[t] == pairs[s]] for s in range(L)]
    vol = [0] * L
    for pr in set(pairs):
        idxs = [s for s in range(L) if pairs[s] == pr]
        vals = rng.sample(range(N), len(idxs))
        for s, val in zip(idxs, vals):
            vol[s] = val
    cur = _unreached(N, p, T, invs, pairs, vol, D)
    for it in range(iters):
        if cur == 0:
            return vol
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        s = rng.randrange(L)
        c = rng.randrange(N)
        if any(vol[t] == c for t in same[s]):
            continue
        old = vol[s]
        vol[s] = c
        v = _unreached(N, p, T, invs, pairs, vol, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            vol[s] = old
    return vol if cur == 0 else None


def _edges(N, p, T, pairs, vol):
    """Edge list of the lift: A_{i,x} -- B_{j, x*g} for each dart (i, j, g)."""
    Boff = p * N
    edges = []
    for s, (i, j) in enumerate(pairs):
        g = vol[s]
        for x in range(N):
            edges.append((i * N + x, Boff + j * N + T[x][g]))
    return edges


def _attempt(p, N, d, D, patterns, rng, deadline):
    """Try groups of order N with random base patterns; return an edge list or None."""
    if N < d:
        return None
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            return None
        C = rng.choice(patterns)
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        pairs = [(i, j) for i in range(p) for j in range(p) for _ in range(C[i][j])]
        vol = _anneal(N, p, T, invs, pairs, D, rng, ITERS, deadline)
        if vol is not None:
            return _edges(N, p, T, pairs, vol)
    return None


def _run_phase(p, d, D, lo, hi, rng, deadline, consider):
    """Search N in [lo, hi] for p-orbit lifts; each success raises the floor for the next one."""
    if hi < lo or hi < d:
        return
    patterns = _patterns(d) if p == 2 else [[[d]]]
    bestN = lo - 1
    budget = BUDGET_START
    floor = max(lo, hi - 12)
    while time.monotonic() < deadline:
        cands = list(range(max(floor, bestN + 1), hi + 1))
        if not cands:
            break
        rng.shuffle(cands)
        success = False
        for N in cands:
            now = time.monotonic()
            if now >= deadline:
                break
            att_deadline = min(deadline, now + budget)
            edges = _attempt(p, N, d, D, patterns, rng, att_deadline)
            if edges is None:
                continue
            consider(2 * p * N, edges)
            bestN = N
            success = True
            break
        if not success:
            if budget < BUDGET_CAP:
                budget = min(BUDGET_CAP, budget * 1.5)
            elif floor > lo:
                floor -= 1


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit - 1.0
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = [(1, [])]

    def consider(n, e):
        if n > best[0][0] and lib.is_valid(n, e, d, D):
            best[0] = (n, e)

    # Record-matching case for D = 3: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best[0]

    if D >= 2:
        consider(*lib.haar_graph(d, range(d)))
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if d < 2 or D < 2:
        return best[0]

    moore = lib._moore_bound(d, D)
    try:
        # Phase A: two-orbit lifts (4N vertices). Window starts near moore/8,
        # which is the order-85 region for d=5, D=5.
        lo2 = max(best[0][0] // 4 + 1, moore // 8)
        hi2 = min(moore // 4, lo2 + 25)
        phase2_deadline = start + PHASE2_FRAC * (deadline - start)
        _run_phase(2, d, D, lo2, hi2, rng, phase2_deadline, consider)

        # Phase B: single-orbit bi-Cayley lifts (2N vertices), as in the parent.
        Nmax = moore // 2
        hi1 = min(Nmax, Nmax // 2 + 6)
        lo1 = max(best[0][0] // 2 + 1, hi1 - 12)
        _run_phase(1, d, D, lo1, hi1, rng, deadline, consider)
    except Exception:
        pass

    if not lib.is_valid(best[0][0], best[0][1], d, D):
        return 1, []
    return best[0]
