import itertools
import math
import random
import time

import lib

ITERS = 800          # annealing steps per (group, base layout) try
MAX_GROUPS = 10      # groups tried per (k, N) attempt
BASE_SIZES = (1, 2, 3, 4)  # k = base vertices per side in the voltage lift


# ----------------------------------------------------------------------------
# Baseline families (fast, validated before use).
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
# Multi-base voltage lifts over Z_m x| Z_k.
#
# Base graph: k vertices A_0..A_{k-1} and k vertices B_0..B_{k-1}. Dart e = (i, t)
# joins A_i to B_{(i + c_t) mod k}, which makes the base d-regular on each side.
# Each dart carries a voltage s_e in G. Lift: A_i,g ~ B_j,(g * s_e) for every g.
# Left multiplication by G is an automorphism, and it is transitive on each fibre,
# so BFS from A_i,e and B_j,e (2k sources) decides the diameter.
# Distinct voltages within each base pair keep the lift simple.
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


def _layout(k, d, c):
    """Dart structure for base size k with per-slot offsets c (length d)."""
    E = k * d
    I = [e // d for e in range(E)]
    J = [(e // d + c[e % d]) % k for e in range(E)]
    incoming = [[e for e in range(E) if J[e] == j] for j in range(k)]
    same = [[e2 for e2 in range(E) if e2 != e and I[e2] == I[e] and J[e2] == J[e]]
            for e in range(E)]
    return I, J, incoming, same


def _cost(N, k, d, D, T, invs, I, J, incoming, V):
    """Total unreached (source, vertex) pairs over the 2k base sources."""
    off = k * N
    M = 2 * off
    adj = [None] * M
    for i in range(k):
        darts = range(i * d, i * d + d)
        for g in range(N):
            row = T[g]
            adj[i * N + g] = [off + J[e] * N + row[V[e]] for e in darts]
    for j in range(k):
        for h in range(N):
            row = T[h]
            adj[off + j * N + h] = [I[e] * N + row[invs[V[e]]] for e in incoming[j]]

    total = 0
    srcs = [i * N for i in range(k)] + [off + j * N for j in range(k)]
    for src in srcs:
        seen = bytearray(M)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += M - count
    return total


def _init_voltages(E, same, N, rng):
    V = [rng.randrange(N) for _ in range(E)]
    for e in range(E):
        while any(V[e] == V[e2] for e2 in same[e]):
            V[e] = rng.randrange(N)
    return V


def _anneal(N, k, d, D, T, invs, I, J, incoming, same, rng, deadline):
    """Simulated annealing over the dart voltages to zero the unreached count."""
    E = k * d
    V = _init_voltages(E, same, N, rng)
    cur = _cost(N, k, d, D, T, invs, I, J, incoming, V)
    scale = k  # temperatures grow with the number of sources (2k)
    t_hot = 1.5 * scale
    t_cold = 0.15 * scale
    for it in range(ITERS):
        if cur == 0:
            return V
        if time.monotonic() > deadline:
            break
        temp = t_hot * (t_cold / t_hot) ** (it / ITERS)
        e = rng.randrange(E)
        s = rng.randrange(N)
        if s == V[e] or any(V[e2] == s for e2 in same[e]):
            continue
        old = V[e]
        V[e] = s
        v = _cost(N, k, d, D, T, invs, I, J, incoming, V)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            V[e] = old
    return V if cur == 0 else None


def _attempt(k, N, d, D, rng, deadline):
    """Try groups of order N with base size k until a diameter-D lift is found."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, kk, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            return None
        _, mul, inv = lib.semidirect_group(m, kk, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        c = [rng.randrange(k) for _ in range(d)]
        I, J, incoming, same = _layout(k, d, c)
        V = _anneal(N, k, d, D, T, invs, I, J, incoming, same, rng, deadline)
        if V is not None:
            return T, V, I, J
    return None


def _lift_edges(k, N, d, T, V, I, J):
    off = k * N
    edges = []
    for e in range(k * d):
        i, j, s = I[e], J[e], V[e]
        for g in range(N):
            edges.append((i * N + g, off + j * N + T[g][s]))
    return 2 * off, edges


# ----------------------------------------------------------------------------
# Driver
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.2 * time_limit, min(0.8 * time_limit, time_limit - 3))
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

    if d < 3 or D < 2:
        return best

    moore = lib._moore_bound(d, D)

    # Candidate (k, N) pairs: total order 2kN must beat the current best.
    cands = []
    for k in BASE_SIZES:
        n_lo = best_n // (2 * k) + 1
        n_hi = moore // (2 * k)
        lo = max(n_lo, d)
        for N in range(lo, min(n_hi, n_lo + 6) + 1):
            cands.append((k, N))
    cands = [c for c in cands if 2 * c[0] * c[1] > best_n]
    cands.sort(key=lambda kn: 2 * kn[0] * kn[1])

    budget = 0.5
    while time.monotonic() < deadline and cands:
        progressed = False
        for (k, N) in list(cands):
            now = time.monotonic()
            if now >= deadline:
                break
            res = _attempt(k, N, d, D, rng, min(deadline, now + budget))
            if res is None:
                continue
            T, V, I, J = res
            n, e = _lift_edges(k, N, d, T, V, I, J)
            consider(n, e)
            cands = [c for c in cands if 2 * c[0] * c[1] > best_n and c != (k, N)]
            cands.sort(key=lambda kn: 2 * kn[0] * kn[1])
            progressed = True
            break
        if not progressed:
            budget *= 2

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
