import itertools
import math
import random
import time

import lib

MAX_GROUPS_PER_ATTEMPT = 12   # groups tried per (n0, N) within one attempt
ITERS = 800                   # annealing steps per attempt
N0_CHOICES = (1, 2, 3, 4, 5, 6)  # base vertices per side of the voltage lift


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
# Multi-orbit voltage lifts over semidirect groups.
#
# Base bipartite multigraph: A_0..A_{n0-1} and B_0..B_{n0-1}, d-regular, built as
# d permutations p_t of [n0]; dart (t, i) joins A_i to B_{p_t(i)} with voltage
# G[t][i] in G. Lift: vertex (base u, x) for x in G. Edge (A_i, x) -- (B_j, x*g).
# Distinct voltages on parallel darts keep the lift simple and d-regular.
# Left multiplication by G is an automorphism, so the diameter is the maximum
# over sources (base vertex, identity). This is a different family from the
# single-orbit bi-Cayley search: several orbits, a richer voltage space.
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


def _lift_nbrs(n0, N, d, perms, G, T):
    """Adjacency lists of the lift. Base vertices: A_i = i, B_j = n0 + j; fiber index x in 0..N-1."""
    V = 2 * n0 * N
    nbr = [[] for _ in range(V)]
    for t in range(d):
        pt = perms[t]
        for i in range(n0):
            ai = i * N
            bj = (n0 + pt[i]) * N
            g = G[t][i]
            for x in range(N):
                a = ai + x
                b = bj + T[x][g]
                nbr[a].append(b)
                nbr[b].append(a)
    return nbr


def _cost(n0, N, nbr, D):
    """Total number of (source, vertex) pairs not within distance D, sources = fiber identities."""
    V = len(nbr)
    total = 0
    for src in range(2 * n0):
        s = src * N
        seen = bytearray(V)
        seen[s] = 1
        frontier = [s]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in nbr[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += V - count
    return total


def _anneal(n0, N, d, D, perms, T, rng, deadline):
    """Simulated annealing over voltages so that the lift has diameter <= D."""
    G = [[0] * n0 for _ in range(d)]
    for i in range(n0):
        for t in range(d):
            j = perms[t][i]
            taken = {G[t2][i] for t2 in range(t) if perms[t2][i] == j}
            while True:
                c = rng.randrange(N)
                if c not in taken:
                    break
            G[t][i] = c

    cur = _cost(n0, N, _lift_nbrs(n0, N, d, perms, G, T), D)
    for it in range(ITERS):
        if cur == 0:
            return G
        if time.monotonic() > deadline:
            break
        t = rng.randrange(d)
        i = rng.randrange(n0)
        j = perms[t][i]
        c = rng.randrange(N)
        if any(G[t2][i] == c for t2 in range(d) if t2 != t and perms[t2][i] == j):
            continue
        old = G[t][i]
        G[t][i] = c
        v = _cost(n0, N, _lift_nbrs(n0, N, d, perms, G, T), D)
        temp = max(0.3, 2.0 * (1.0 - it / ITERS))
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            G[t][i] = old
    return G if cur == 0 else None


def _attempt(n0, N, d, D, rng, deadline):
    """Try groups of order N for an n0-orbit lift; return the lift adjacency lists or None."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        _, mul, _ = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        perms = [list(range(n0))] + [rng.sample(range(n0), n0) for _ in range(d - 1)]
        G = _anneal(n0, N, d, D, perms, T, rng, deadline)
        if G is not None:
            return _lift_nbrs(n0, N, d, perms, G, T)
    return None


def _edges_from(nbr):
    """Undirected edge list from adjacency lists."""
    return [(a, b) for a in range(len(nbr)) for b in nbr[a] if a < b]


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + min(0.8 * time_limit, time_limit - 6.0)
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

    # Main search: voltage lifts with several base orbits, ascending vertex count.
    if d >= 3 and D >= 2:
        moore = lib._moore_bound(d, D)
        V = max(best_n + 1, 2 * (d + 1))
        if V % 2:
            V += 1
        budget = 1.0
        while time.monotonic() < deadline and V <= moore:
            options = []
            for n0 in N0_CHOICES:
                if V % (2 * n0) == 0:
                    N = V // (2 * n0)
                    if N >= d + 1:
                        options.append((n0, N))
            if not options:
                V += 2
                continue
            rng.shuffle(options)

            found = None
            for n0, N in options:
                now = time.monotonic()
                if now >= deadline:
                    break
                nbr = _attempt(n0, N, d, D, rng, min(deadline, now + budget))
                if nbr is not None:
                    found = nbr
                    break

            if found is not None:
                consider(V, _edges_from(found))
                V = max(V, best_n) + 2
            else:
                budget *= 1.5

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
