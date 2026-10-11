import math
import random
import time

import lib

ITERS = 600          # annealing steps per (group, base pattern) try
MAX_GROUPS = 12      # groups tried per attempt
LO_FRAC = 0.45       # search orders from this fraction of the Moore bound upward


# ----------------------------------------------------------------------------
# Lifts of small bipartite base multigraphs over semidirect products Z_m x| Z_k.
#
# Base: a A-vertices and a B-vertices, d darts out of each A-vertex and into
# each B-vertex (so base is d-regular). A dart (u, v, g) joins A(u, x) to
# B(v, x*g) for every group element x. Left multiplication by h is an
# automorphism, so eccentricities from A(u, e) and B(v, e) decide the diameter.
# Distinct voltages on parallel darts keep the lift simple.
# ----------------------------------------------------------------------------

def _groups(N):
    """Semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _random_pairs(a, d, rng):
    """Base multigraph: d random permutations of range(a); pair (u, v) per dart."""
    pairs = []
    for _ in range(d):
        perm = list(range(a))
        rng.shuffle(perm)
        for u in range(a):
            pairs.append((u, perm[u]))
    return pairs


def _build_adj(a, N, T, pairs, volts):
    """Adjacency lists of the lift. A(u, x) = u*N + x; B(v, y) = (a + v)*N + y."""
    n = 2 * a * N
    adj = [[] for _ in range(n)]
    for (u, v), g in zip(pairs, volts):
        pa = u * N
        pb = (a + v) * N
        for x in range(N):
            p = pa + x
            q = pb + T[x][g]
            adj[p].append(q)
            adj[q].append(p)
    return adj, n


def _unreached(a, N, adj, n, D):
    """Count (source, vertex) pairs not within distance D, over one source per base vertex."""
    sources = [u * N for u in range(a)] + [(a + v) * N for v in range(a)]
    total = 0
    for src in sources:
        seen = bytearray(n)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for p in frontier:
                for q in adj[p]:
                    if not seen[q]:
                        seen[q] = 1
                        nxt.append(q)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += n - count
    return total


def _anneal(a, N, T, pairs, same, d, D, rng, deadline):
    """Simulated annealing over dart voltages; returns voltages with zero unreached pairs, or None."""
    m = len(pairs)
    volts = [0] * m
    for j in range(m):
        used = {volts[k] for k in same[j] if k < j}
        choices = [g for g in range(N) if g not in used]
        volts[j] = rng.choice(choices)

    def score(vs):
        adj, n = _build_adj(a, N, T, pairs, vs)
        return _unreached(a, N, adj, n, D)

    cur = score(volts)
    for it in range(ITERS):
        if cur == 0:
            return volts
        if time.monotonic() > deadline:
            break
        temp = max(0.05, 2.0 * (1.0 - it / ITERS))
        j = rng.randrange(m)
        g = rng.randrange(N)
        if any(volts[k] == g for k in same[j]):
            continue
        old = volts[j]
        volts[j] = g
        new = score(volts)
        if new <= cur or rng.random() < math.exp(-(new - cur) / temp):
            cur = new
        else:
            volts[j] = old
    return volts if cur == 0 else None


def _attempt(a, N, d, D, rng, deadline):
    """Try groups of order N with random base patterns until one lift has diameter <= D."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            return None
        _, mul, _ = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        pairs = _random_pairs(a, d, rng)
        same = [[j2 for j2 in range(len(pairs)) if j2 != j and pairs[j2] == pairs[j]]
                for j in range(len(pairs))]
        volts = _anneal(a, N, T, pairs, same, d, D, rng, deadline)
        if volts is not None:
            return T, pairs, volts
    return None


def _lift_edges(a, N, T, pairs, volts):
    """Edge list and order of the lift for a successful voltage assignment."""
    edges = []
    for (u, v), g in zip(pairs, volts):
        for x in range(N):
            edges.append((u * N + x, (a + v) * N + T[x][g]))
    return 2 * a * N, edges


# ----------------------------------------------------------------------------
# Baseline families (fast fallbacks).
# ----------------------------------------------------------------------------

def _pg_fallback(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget_total = max(1.0, min(0.8 * time_limit, time_limit - 4.0))
    deadline = start + budget_total
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    # Exact record family for D = 3 when d - 1 is a prime power.
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(n, e, d, D):
            return n, e

    best = (1, [])

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    consider(2, [(0, 1)])
    if D >= 2:
        consider(*lib.haar_graph(d, range(d)))
    if D >= 3:
        pg = _pg_fallback(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if d >= 2 and D >= 2:
        moore = lib._moore_bound(d, D)
        lo = max(best[0] + 1, int(LO_FRAC * moore))
        cands = sorted(
            (2 * a * N, a, N)
            for a in range(1, 7)
            for N in range(max(d, 2), moore // (2 * a) + 1)
            if 2 * a * N >= lo and 2 * a * N <= moore
        )
        budget = 1.0
        while cands and time.monotonic() < deadline:
            failed = []
            for order, a, N in cands:
                if order <= best[0]:
                    continue
                now = time.monotonic()
                if now >= deadline:
                    break
                res = _attempt(a, N, d, D, rng, min(deadline, now + budget))
                if res is not None:
                    T, pairs, volts = res
                    n, e = _lift_edges(a, N, T, pairs, volts)
                    consider(n, e)
                else:
                    failed.append((order, a, N))
            cands = [c for c in failed if c[0] > best[0]]
            budget *= 1.5

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
