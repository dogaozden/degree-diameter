import itertools
import math
import random
import time

import lib

KMAX = 4          # largest number of base vertices per side in a voltage lift
WINDOW = 40       # search window above the current best order
ITERS = 500       # annealing steps per (group, base) attempt
T_HOT = 1.2       # initial annealing temperature (unreached-pair units)
T_COLD = 0.1      # final annealing temperature
MARGIN_FRAC = 0.75


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
    """W(q) for the largest small prime power q with q + 1 <= d."""
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Groups of order N: semidirect products Z_m x|_r Z_k (identity is code 0).
# ----------------------------------------------------------------------------

def _groups(N):
    """Return semidirect parameters (m, k, r) with m*k = N."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


# ----------------------------------------------------------------------------
# Voltage lifts over a group G of order N with k base vertices per side.
#
# Vertices A_i,x = i*N + x and B_j,y = (k+j)*N + y.  Layer l (of d layers) is a
# permutation perms[l] matching A_i to B_{perms[l][i]} with group voltage
# volt[l][i]: A_i,x ~ B_{p(i)}, x*g.  The graph is d-regular, bipartite, and
# left multiplication by G acts as automorphisms.  Layer 0 has identity
# voltages WLOG, by relabelling the B side.  Diameter is decided by BFS from
# the 2k sources (u, identity).
# ----------------------------------------------------------------------------

def _lift_adj(k, N, T, d, perms, volt):
    adj = [[] for _ in range(2 * k * N)]
    for l in range(d):
        p = perms[l]
        vl = volt[l]
        for i in range(k):
            a = i * N
            b = (k + p[i]) * N
            g = vl[i]
            for x in range(N):
                y = T[x][g]
                adj[a + x].append(b + y)
                adj[b + y].append(a + x)
    return adj


def _cost(adj, V, srcs, D):
    """Total number of (source, vertex) pairs not within distance D."""
    total = 0
    for src in srcs:
        seen = bytearray(V)
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
        total += V - count
    return total


def _anneal(k, N, T, d, D, rng, iters, deadline):
    """Anneal over layer permutations and voltages to zero the unreached count."""
    V = 2 * k * N
    srcs = [i * N for i in range(k)] + [(k + j) * N for j in range(k)]
    perms = [list(range(k))] + [rng.sample(range(k), k) for _ in range(d - 1)]
    volt = [[0] * k] + [[rng.randrange(N) for _ in range(k)] for _ in range(d - 1)]
    cur = _cost(_lift_adj(k, N, T, d, perms, volt), V, srcs, D)
    for it in range(iters):
        if cur == 0:
            break
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        P2 = [row[:] for row in perms]
        V2 = [row[:] for row in volt]
        l = rng.randrange(1, d)
        if k > 1 and rng.random() < 0.05:
            P2[l] = rng.sample(range(k), k)
        else:
            V2[l][rng.randrange(k)] = rng.randrange(N)
        v = _cost(_lift_adj(k, N, T, d, P2, V2), V, srcs, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            perms, volt, cur = P2, V2, v
    return (perms, volt) if cur == 0 else None


def _attempt(k, N, d, D, rng, deadline):
    """Try every group of order N for base size k until one anneals to diameter <= D."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, kk, r in groups:
        if time.monotonic() > deadline:
            return None
        _, mul, _ = lib.semidirect_group(m, kk, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        res = _anneal(k, N, T, d, D, rng, ITERS, deadline)
        if res is not None:
            return T, res[0], res[1]
    return None


def _edges(k, N, T, d, perms, volt):
    """Expand a successful lift into (n, edges); A block comes before B block."""
    E = set()
    for l in range(d):
        p = perms[l]
        vl = volt[l]
        for i in range(k):
            a = i * N
            b = (k + p[i]) * N
            g = vl[i]
            for x in range(N):
                E.add((a + x, b + T[x][g]))
    return 2 * k * N, sorted(E)


def _candidates(best_n, M):
    """(total, k, N) with best_n < 2kN <= min(M, best_n + WINDOW), sorted by total."""
    out = []
    for k in range(1, KMAX + 1):
        lo = best_n // (2 * k) + 1
        hi = min(M, best_n + WINDOW) // (2 * k)
        for N in range(max(2, lo), hi + 1):
            out.append((2 * k * N, k, N))
    out.sort()
    return out


def _search(d, D, rng, deadline, best_n):
    """Ladder search: repeatedly try the smallest orders above the current best."""
    M = lib._moore_bound(d, D)
    best = None
    budget = 0.25
    while time.monotonic() < deadline:
        cands = _candidates(best_n, M)
        if not cands:
            break
        success = False
        for total, k, N in cands:
            now = time.monotonic()
            if now >= deadline:
                break
            res = _attempt(k, N, d, D, rng, min(deadline, now + budget))
            if res is None:
                continue
            T, perms, volt = res
            n, e = _edges(k, N, T, d, perms, volt)
            success = True
            if n > best_n and lib.is_valid(n, e, d, D):
                best = (n, e)
                best_n = n
            break
        if not success:
            budget *= 2
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, MARGIN_FRAC * time_limit)
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

    try:
        # Record-matching case: incidence graph of PG(2, d-1).
        if D == 3 and lib.is_prime_power(d - 1):
            consider(*lib.projective_plane_incidence(d - 1))
            return best

        if D >= 2:
            consider(*lib.haar_graph(d, range(d)))
        if D >= 3:
            pg = _best_pg(d)
            if pg is not None:
                consider(pg[0], pg[1])
            q = d - 2
            if q >= 3 and lib.is_prime_power(q):
                consider(*lib.araujo_lopez_graph(q))
        if D >= 4 and time.monotonic() < deadline:
            gq = _best_gq(d)
            if gq is not None:
                consider(gq[0], gq[1])

        if d >= 2 and D >= 2 and time.monotonic() < deadline:
            res = _search(d, D, rng, deadline, best_n)
            if res is not None:
                consider(res[0], res[1])
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
