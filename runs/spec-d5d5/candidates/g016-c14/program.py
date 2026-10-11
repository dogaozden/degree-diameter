import itertools
import math
import random
import time

import lib

# Search parameters for the voltage-lift search.
ITERS = 1500          # annealing steps per (group, base, N) try
T_HOT = 2.0           # initial annealing temperature (unreached-pair units)
T_COLD = 0.1          # final annealing temperature
GROUPS_PER_ATTEMPT = 10
DUP_PENALTY = 50      # cost per duplicate lift edge (must reach zero)
SHARES = [(2, 0.35), (3, 0.30), (4, 0.20), (1, 0.15)]   # base-size phases
SEARCH_FRACTION = 0.8  # fraction of time_limit used for searching


# ----------------------------------------------------------------------------
# Baseline families (fast, always valid when they pass lib.is_valid).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
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


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Voltage lifts of small bipartite base graphs over groups of order N.
#
# Base: a vertices on side A, a on side B, and a d-regular bipartite multigraph
# given by d random permutations (dart (u, sigma(u)) for each permutation).
# Lift: A(u, x) -- B(v, x*g) for each dart (u, v, g) and every group element x.
#
# Left multiplication by h is an automorphism of the lift, so the lift has
# diameter <= D iff every source A(u, e) and B(v, e) reaches all 2aN vertices
# within D steps. That is only 2a BFS runs per evaluation.
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


def _unreached(V, adj, sources, D):
    """Count (source, vertex) pairs not within distance D over the given sources."""
    total = 0
    for s in sources:
        seen = bytearray(V)
        seen[s] = 1
        count = 1
        frontier = [s]
        for _ in range(D):
            nxt = []
            for u in frontier:
                for w in adj[u]:
                    if not seen[w]:
                        seen[w] = 1
                        nxt.append(w)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += V - count
    return total


def _cost(a, N, D, darts, volt, T):
    """Unreached-pair count for the lift, plus a penalty for duplicate lift edges."""
    V = 2 * a * N
    base_B = a * N
    adj = [[] for _ in range(V)]
    seen = set()
    dup = 0
    for (u, v), g in zip(darts, volt):
        key = (u, v, g)
        if key in seen:
            dup += 1
            continue
        seen.add(key)
        pu = u * N
        qv = base_B + v * N
        for x in range(N):
            p = pu + x
            q = qv + T[x][g]
            adj[p].append(q)
            adj[q].append(p)
    if dup:
        return DUP_PENALTY * dup
    sources = [u * N for u in range(a)] + [base_B + v * N for v in range(a)]
    return _unreached(V, adj, sources, D)


def _anneal(a, N, D, darts, T, rng, iters, deadline):
    """Simulated annealing over the dart voltages to zero the unreached-pair count."""
    G = len(darts)
    volt = [rng.randrange(N) for _ in range(G)]
    cur = _cost(a, N, D, darts, volt, T)
    for it in range(iters):
        if cur == 0:
            return volt
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        i = rng.randrange(G)
        old = volt[i]
        new = rng.randrange(N)
        if new == old:
            continue
        volt[i] = new
        c = _cost(a, N, D, darts, volt, T)
        if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
            cur = c
        else:
            volt[i] = old
    return volt if cur == 0 else None


def _attempt(a, N, d, D, rng, deadline):
    """Try groups of order N with a random base graph until voltages give diameter <= D."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        perms = [rng.sample(range(a), a) for _ in range(d)]
        darts = [(u, perms[i][u]) for i in range(d) for u in range(a)]
        volt = _anneal(a, N, D, darts, T, rng, ITERS, deadline)
        if volt is not None:
            return darts, volt, T
    return None


def _edges(a, N, darts, volt, T):
    """Explicit (n, edges) for a lift; A vertices are 0..aN-1, B vertices follow."""
    base_B = a * N
    out = []
    for (u, v), g in zip(darts, volt):
        for x in range(N):
            out.append((u * N + x, base_B + v * N + T[x][g]))
    return 2 * a * N, out


def _lift_search(a, d, D, rng, lo_n, deadline, offer):
    """Binary search on the group order N, for base size a, for lifts beating lo_n vertices."""
    cap = lib._moore_bound(d, D) // (2 * a)
    lo = max(d, lo_n // (2 * a))
    hi = cap
    while lo < hi:
        now = time.monotonic()
        if now >= deadline:
            break
        N = (lo + hi + 1) // 2
        att_dl = min(deadline, now + max(1.0, (deadline - now) / 4))
        res = _attempt(a, N, d, D, rng, att_dl)
        if res is None:
            hi = N - 1
        else:
            darts, volt, T = res
            n, e = _edges(a, N, darts, volt, T)
            offer(n, e)
            lo = N


def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = (1, [])
    best_n = 1

    def offer(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Record-matching case: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        offer(n, e)
        return best

    # Fast safe baselines.
    if D >= 2:
        offer(*lib.haar_graph(d, range(d)))
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            offer(pg[0], pg[1])
    if D >= 4 and time.monotonic() - start < SEARCH_FRACTION * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            offer(gq[0], gq[1])

    if d < 2 or D < 2:
        return best

    # Voltage-lift searches over several base sizes, each with a time share.
    total = SEARCH_FRACTION * time_limit
    cum = 0.0
    for a, share in SHARES:
        cum += share
        phase_end = start + total * cum
        if time.monotonic() >= phase_end:
            continue
        _lift_search(a, d, D, rng, best_n, phase_end, offer)

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
