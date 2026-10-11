import itertools
import math
import random
import time

import lib

MAX_GROUPS_PER_ATTEMPT = 12   # groups tried per order N within one attempt
ITERS = 1200                  # annealing steps per (group, connection set) try
MAX_N = 400                   # cap on bi-Cayley order (memory of the N x N table)


# ----------------------------------------------------------------------------
# Baseline families (fast, validated by lib.is_valid before use).
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
# Bi-Cayley search over semidirect products Z_m x| Z_k of order N.
#
# Vertices A_x and B_y (x, y in G). Edge A_x -- B_{x s} for s in S, |S| = d.
# Left multiplication is an automorphism, so eccentricities from A_0 and B_0
# decide the diameter. Identity is WLOG in S.
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


def _unreached(N, T, invs, S, D):
    """Count (source, vertex) pairs not within distance D, for sources A_0 and B_0."""
    Sinv = [invs[g] for g in S]
    total = 0
    for src in (0, N):
        seen = bytearray(2 * N)
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < N:
                    row = T[u]
                    for g in S:
                        v = N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    row = T[u - N]
                    for h in Sinv:
                        v = row[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += 2 * N - count
    return total


def _anneal(N, T, invs, d, D, rng, iters, deadline):
    """Annealing over S = {0, s_1, ..., s_{d-1}}. Returns the best (S, cost) seen."""
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _unreached(N, T, invs, S, D)
    best_S, best_c = S[:], cur
    for it in range(iters):
        if cur == 0:
            break
        if time.monotonic() > deadline:
            break
        temp = max(0.05, 2.0 * (1.0 - it / iters))
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _unreached(N, T, invs, S2, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            S, cur = S2, v
            if cur < best_c:
                best_S, best_c = S[:], cur
    return best_S, best_c


def _edges(N, T, S):
    """Edge list of the bi-Cayley graph: A_x -- B_{x s}."""
    return [(x, N + T[x][g]) for x in range(N) for g in S]


def _attempt(N, d, D, rng, deadline):
    """Try groups of order N. Returns ((T, S), None) on success, else (None, best near-miss)."""
    groups = _groups(N)
    rng.shuffle(groups)
    near = None  # (cost, T, S)
    for m, k, r in groups[:MAX_GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            break
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        S, c = _anneal(N, T, invs, d, D, rng, ITERS, deadline)
        if c == 0:
            return (T, S), None
        if near is None or c < near[0]:
            near = (c, T, S)
    return None, near


# ----------------------------------------------------------------------------
# NEW: exact-cost 2-switch repair of near-miss bi-Cayley graphs.
#
# A d-regular bipartite graph is changed by "2-switches": edges (a1,b1), (a2,b2)
# become (a1,b2), (a2,b1). Degrees and bipartiteness are preserved. The cost is
# the exact number of unordered vertex pairs at distance > D, computed with
# big-integer bitsets. Metropolis acceptance walks toward zero bad pairs. This
# can escape the group-restricted search space that the bi-Cayley annealing is
# stuck in.
# ----------------------------------------------------------------------------

def _bad_count(n, adj, D):
    """Number of unordered vertex pairs at distance > D (unreachable pairs included)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _repair(N, edges, D, rng, deadline):
    """2-switch annealing on a bipartite graph with parts [0,N) and [N,2N). Returns edges or None."""
    n = 2 * N
    E = [[a, b] for a, b in edges]
    present = set((a, b) for a, b in E)

    def adjacency():
        adj = [[] for _ in range(n)]
        for a, b in E:
            adj[a].append(b)
            adj[b].append(a)
        return adj

    cur = _bad_count(n, adjacency(), D)
    best_c = cur
    best_E = [e[:] for e in E]
    m = len(E)
    temp = 0.4
    while cur > 0 and time.monotonic() < deadline:
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        if (a1, b2) in present or (a2, b1) in present:
            continue
        E[i] = [a1, b2]
        E[j] = [a2, b1]
        new = _bad_count(n, adjacency(), D)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            present.discard((a1, b1))
            present.discard((a2, b2))
            present.add((a1, b2))
            present.add((a2, b1))
            cur = new
            if cur < best_c:
                best_c = cur
                best_E = [e[:] for e in E]
        else:
            E[i] = [a1, b1]
            E[j] = [a2, b2]
    if best_c != 0:
        return None
    return [(a, b) for a, b in best_E]


def _bicayley(d, D, rng, deadline, consider):
    """Search bi-Cayley graphs: first find any working order, then climb with search + repair."""
    Nmax = lib._moore_bound(d, D) // 2
    top = min(Nmax, Nmax // 2 + 3, MAX_N)
    if top <= d:
        return

    # Phase 1: descend from the top until some order succeeds.
    found = None
    budget = 0.3
    while found is None and time.monotonic() < deadline:
        for N in range(top, d, -1):
            now = time.monotonic()
            if now >= deadline:
                break
            res, _ = _attempt(N, d, D, rng, min(deadline, now + budget))
            if res is not None:
                consider(2 * N, _edges(N, res[0], res[1]))
                found = N
                break
        budget *= 2
    if found is None:
        return

    # Phase 2: ascend above the best order; each order gets group search, then repair.
    lo = found + 1
    budget = 0.3
    while lo <= top and time.monotonic() < deadline:
        N = lo
        while N <= top and time.monotonic() < deadline:
            att = min(deadline, time.monotonic() + budget)
            res, near = _attempt(N, d, D, rng, att)
            ok = False
            if res is not None:
                consider(2 * N, _edges(N, res[0], res[1]))
                ok = True
            elif near is not None and time.monotonic() < deadline:
                rep = _repair(N, _edges(N, near[1], near[2]), D, rng,
                              min(deadline, time.monotonic() + 2 * budget))
                if rep is not None:
                    consider(2 * N, rep)
                    ok = True
            if ok:
                lo = N + 1
                N = lo
            else:
                N += 1
        budget *= 2


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
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

    consider(*lib.haar_graph(d, range(d)))
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if d >= 2 and D >= 2 and time.monotonic() < deadline:
        _bicayley(d, D, rng, deadline, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
