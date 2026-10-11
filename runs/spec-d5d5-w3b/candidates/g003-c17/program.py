import math
import random
import time

import lib

ITERS = 700            # annealing steps per (orbit matrix, group) try
T_HOT = 2.0
T_COLD = 0.1
MAX_GROUPS = 10        # groups tried per attempt
GROUP_MOVE_PROB = 0.3
A_CHOICES = (1, 2, 3, 4)   # number of vertex orbits per side


# ----------------------------------------------------------------------------
# Baseline families (cheap, verified by lib.is_valid before use).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Multi-orbit bi-Cayley lifts (voltage lifts over a group, a orbits per side).
#
# Vertices: A(i, x) and B(j, y) for orbits i, j in range(a) and x, y in G.
# Each "dart" (i, j, g) adds edges A(i, x) -- B(j, x*g) for all x in G.
# The dart multiset is circulant: orbit i on the A side is joined to orbit
# (i + s) mod a on the B side with multiplicity c[s], sum(c) = d. So every
# vertex has degree d. Within one (i, j) pair the group labels must be
# distinct, otherwise edges would repeat.
#
# Left multiplication is an automorphism, so the diameter is decided by BFS
# from the 2a sources A(i, e), B(j, e).
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


def _base_connected(a, c):
    """True if the a+a base graph with shift multiplicities c is connected."""
    parent = list(range(2 * a))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    for i in range(a):
        for s in range(a):
            if c[s]:
                parent[find(i)] = find(a + (i + s) % a)
    return len({find(x) for x in range(2 * a)}) == 1


def _random_composition(d, a, rng):
    """Random nonnegative c of length a with sum d whose base graph is connected."""
    for _ in range(200):
        c = [0] * a
        for _ in range(d):
            c[rng.randrange(a)] += 1
        if _base_connected(a, c):
            return c
    return None


def _dart_layout(a, c):
    """Return (darts, members): darts are (i, j) pairs; members[k] lists darts sharing (i, j)."""
    darts = []
    for i in range(a):
        for j in range(a):
            for _ in range(c[(j - i) % a]):
                darts.append((i, j))
    groups = {}
    for k, pr in enumerate(darts):
        groups.setdefault(pr, []).append(k)
    members = [groups[pr] for pr in darts]
    return darts, members


def _cost(N, a, D, T, darts, gs, invs):
    """Count (source, vertex) pairs not within distance D, over the 2a orbit sources."""
    outA = [[] for _ in range(a)]   # A orbit i -> (j, g)
    inB = [[] for _ in range(a)]    # B orbit j -> (i, g^-1)
    for (i, j), g in zip(darts, gs):
        outA[i].append((j, g))
        inB[j].append((i, invs[g]))
    aN = a * N
    V = 2 * aN
    total = 0
    sources = [i * N for i in range(a)] + [aN + j * N for j in range(a)]
    for src in sources:
        seen = bytearray(V)
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < aN:
                    i, x = divmod(u, N)
                    row = T[x]
                    for j, g in outA[i]:
                        v = aN + j * N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    j, y = divmod(u - aN, N)
                    row = T[y]
                    for i, gi in inB[j]:
                        v = i * N + row[gi]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += V - count
    return total


def _anneal(N, a, D, T, invs, darts, members, rng, deadline):
    """Anneal the dart group labels to zero unreached pairs; return labels or None."""
    gs = [0] * len(darts)
    seen_pairs = {}
    for k, pr in enumerate(darts):
        seen_pairs.setdefault(pr, []).append(k)
    for pr, idxs in seen_pairs.items():
        for k, g in zip(idxs, rng.sample(range(N), len(idxs))):
            gs[k] = g
    cur = _cost(N, a, D, T, darts, gs, invs)
    for it in range(ITERS):
        if cur == 0:
            return gs
        if time.monotonic() > deadline:
            return None
        temp = T_HOT * (T_COLD / T_HOT) ** (it / ITERS)
        k = rng.randrange(len(gs))
        used = {gs[t] for t in members[k] if t != k}
        if rng.random() < GROUP_MOVE_PROB:
            g = T[gs[rng.randrange(len(gs))]][gs[rng.randrange(len(gs))]]
        else:
            g = rng.randrange(N)
        if g in used:
            continue
        old = gs[k]
        gs[k] = g
        v = _cost(N, a, D, T, darts, gs, invs)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            gs[k] = old
    return gs if cur == 0 else None


def _attempt(a, N, d, D, rng, deadline):
    """Try random orbit patterns and groups of order N; return (T, darts, gs) or None."""
    c = _random_composition(d, a, rng)
    if c is None:
        return None
    darts, members = _dart_layout(a, c)
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            return None
        _, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        gs = _anneal(N, a, D, T, invs, darts, members, rng, deadline)
        if gs is not None:
            return T, darts, gs
    return None


def _edges_from(a, N, T, darts, gs):
    """Expand a multi-orbit lift to an edge list on 2aN vertices (A orbits first)."""
    aN = a * N
    edges = []
    for (i, j), g in zip(darts, gs):
        for x in range(N):
            edges.append((i * N + x, aN + j * N + T[x][g]))
    return edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, min(0.8 * time_limit, time_limit - 4.0))
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

    # Record-matching case: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best

    if D >= 2:
        consider(*lib.haar_graph(d, range(d)))
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if d < 2 or D < 2:
        return best

    moore = lib._moore_bound(d, D)
    budget = 2.0
    fails = 0

    while time.monotonic() < deadline:
        options = []
        for a in A_CHOICES:
            hi = moore // (2 * a)
            lo = max(d + 1, best_n // (2 * a) + 1)
            if lo <= hi:
                options.append((a, lo, hi))
        if not options:
            break
        a, lo, hi = rng.choice(options)
        # Prefer the lower part of the window: a feasible order there is what gains.
        N = rng.randint(lo, min(hi, lo + max(2, (hi - lo) // 3)))

        now = time.monotonic()
        att_deadline = min(deadline, now + budget)
        res = _attempt(a, N, d, D, rng, att_deadline)
        if res is None:
            fails += 1
            if fails % 4 == 0 and budget < 8.0:
                budget = min(8.0, budget * 1.3)
            continue
        T, darts, gs = res
        consider(2 * a * N, _edges_from(a, N, T, darts, gs))

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
