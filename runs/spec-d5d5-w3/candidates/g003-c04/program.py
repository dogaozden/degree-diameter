import itertools
import math
import random
import time

import lib

ITERS = 400            # annealing steps per restart
RESTARTS = 2           # fresh random dart sets per group
GROUPS_PER_CAND = 6    # groups tried per (orbits, order) candidate within one attempt
ORBIT_COUNTS = (2, 3, 1, 4)   # base vertices per side tried; a=1 is the parent's bi-Cayley case
CAND_WINDOW = 10       # number of candidate sizes tried per pass, ascending from the current best
DUP_PENALTY = 20


# ----------------------------------------------------------------------------
# Baseline families (kept from the parent; each result is checked with lib.is_valid).
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
# New construction: multi-orbit bi-Cayley (voltage lift over a group).
#
# Base graph: a "A" vertices and a "B" vertices. Each base vertex i of side A and
# each base vertex j of side B lift to a copies of the group G of order M.
# A dart (i, j, g) gives edges A_{i,x} -- B_{j, x g} for all x in G.
# The base multigraph is d-regular: for each t in 0..d-1 pick a permutation
# sigma_t of range(a) and use darts (i, sigma_t(i), g_{t,i}). Every A vertex and
# every B vertex then has degree d.
#
# Symmetry-reduced diameter check: left multiplication by G is an automorphism
# that fixes each orbit, so eccentricities need only one source per orbit,
# i.e. A_{i,e} for i < a and B_{j,e} for j < a. This replaces the full all-pairs
# check during search, and the final lib.is_valid call verifies everything.
# a = 1 reduces to the parent's bi-Cayley search.
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


def _tables(m, k, r):
    """Return (M, T) with T[x][g] = x*g in the semidirect group; identity has index 0."""
    M, mul, _ = lib.semidirect_group(m, k, r)
    T = [[mul(x, g) for g in range(M)] for x in range(M)]
    return M, T


def _score(a, M, T, D, darts):
    """Unreached (source, vertex) pairs over orbit representatives, plus a duplicate penalty."""
    seen_darts = set()
    dups = 0
    for dart in darts:
        key = (dart[0], dart[1], dart[2])
        if key in seen_darts:
            dups += 1
        else:
            seen_darts.add(key)
    if dups:
        return DUP_PENALTY * dups

    n = 2 * a * M
    off = a * M
    adj = [[] for _ in range(n)]
    for i, j, g in darts:
        base = off + j * M
        for x in range(M):
            u = i * M + x
            v = base + T[x][g]
            adj[u].append(v)
            adj[v].append(u)

    sources = [i * M for i in range(a)] + [off + j * M for j in range(a)]
    total = 0
    for s in sources:
        seen = bytearray(n)
        seen[s] = 1
        frontier = [s]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            if not nxt:
                break
            cnt += len(nxt)
            frontier = nxt
        total += n - cnt
    return total


def _anneal(a, M, T, d, D, rng, iters, deadline):
    """Anneal the voltages of a d-regular base multigraph on a + a orbits."""
    darts = []
    for _ in range(d):
        perm = list(range(a))
        rng.shuffle(perm)
        for i in range(a):
            darts.append([i, perm[i], rng.randrange(M)])
    cur = _score(a, M, T, D, darts)
    for it in range(iters):
        if cur == 0:
            return darts
        if time.monotonic() > deadline:
            break
        temp = 2.0 * (1.0 - it / iters) + 0.1
        k = rng.randrange(len(darts))
        c = rng.randrange(M)
        old = darts[k][2]
        if c == old:
            continue
        darts[k][2] = c
        v = _score(a, M, T, D, darts)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            darts[k][2] = old
    return darts if cur == 0 else None


def _attempt(a, M, d, D, rng, deadline):
    """Try groups of order M with a base orbits per side; return (a, M, T, darts) or None."""
    groups = _groups(M)
    rng.shuffle(groups)
    for m, k, r in groups[:GROUPS_PER_CAND]:
        if time.monotonic() > deadline:
            return None
        Mo, T = _tables(m, k, r)
        for _ in range(RESTARTS):
            if time.monotonic() > deadline:
                return None
            darts = _anneal(a, Mo, T, d, D, rng, ITERS, deadline)
            if darts is not None:
                return a, Mo, T, darts
    return None


def _to_edges(a, M, T, darts):
    """Expand a found base multigraph into (n, edges)."""
    off = a * M
    edges = []
    for i, j, g in darts:
        for x in range(M):
            edges.append((i * M + x, off + j * M + T[x][g]))
    return 2 * a * M, edges


def _candidates(best_n, Mb, limit):
    """Candidate (a, M) pairs with total order 2*a*M above best_n, in ascending order."""
    out = []
    T0 = best_n + 1
    if T0 % 2:
        T0 += 1
    for T in range(T0, Mb + 1, 2):
        half = T // 2
        for a in ORBIT_COUNTS:
            if half % a == 0:
                M = half // a
                if M >= 2:
                    out.append((a, M))
        if len(out) >= limit:
            break
    return out[:limit]


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.0, min(0.85 * time_limit, time_limit - 3.0))
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
    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if d < 2 or D < 2:
        return best

    Mb = lib._moore_bound(d, D)   # total vertex bound
    budget = 2.0
    bad = set()

    while time.monotonic() < deadline:
        cl = [c for c in _candidates(best_n, Mb, CAND_WINDOW) if c not in bad]
        if not cl:
            break
        success = False
        for a, M in cl:
            now = time.monotonic()
            if now >= deadline:
                break
            res = _attempt(a, M, d, D, rng, min(deadline, now + budget))
            if res is None:
                continue
            before = best_n
            consider(*_to_edges(*res))
            if best_n > before:
                success = True
                break
            bad.add((a, M))
        if not success:
            budget *= 1.5

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
