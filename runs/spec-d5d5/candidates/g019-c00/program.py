import itertools
import math
import random
import time

import lib

ITERS = 3000          # annealing steps per attempt
MAX_GROUPS = 6        # groups tried per (t, N) attempt
TS = (1, 2, 2, 3, 4)  # number of base vertices per side to try (multi-orbit lifts)


# ----------------------------------------------------------------------------
# Baseline families (cheap, validated before use).
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
# NEW: multi-orbit voltage lifts over semidirect products.
#
# Base graph: t vertices A_0..A_{t-1} and t vertices B_0..B_{t-1}; each layer l
# is a bijection P_l: A-index -> B-index with a voltage V_l(f) in G. Lifted
# vertices are (fiber f, group element x); the edge A_{f,x} -- B_{P_l(f), x*V_l(f)}
# for every layer l. Each lifted vertex has degree d (before dedup), and left
# multiplication is an automorphism, so the diameter equals the maximum
# eccentricity over the 2t base vertices at the identity. Total order 2tN.
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


def _cost(P, Pinv, V, N, t, d, D, T, INV):
    """Total number of (source, vertex) pairs at distance > D, over the 2t base sources."""
    M = 2 * t * N
    total = 0
    for f0 in range(2 * t):
        s = f0 * N
        seen = bytearray(M)
        seen[s] = 1
        frontier = [s]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                f, x = divmod(u, N)
                row = T[x]
                if f < t:
                    for l in range(d):
                        v = (t + P[l][f]) * N + row[V[l][f]]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    j = f - t
                    for l in range(d):
                        i = Pinv[l][j]
                        v = i * N + row[INV[V[l][i]]]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += M - count
    return total


def _anneal(N, t, d, D, T, INV, rng, iters, deadline):
    """Anneal voltages and layer permutations until every base source reaches all within D."""
    P, Pinv = [], []
    for _ in range(d):
        perm = list(range(t))
        rng.shuffle(perm)
        inv = [0] * t
        for f, j in enumerate(perm):
            inv[j] = f
        P.append(perm)
        Pinv.append(inv)
    V = [[rng.randrange(N) for _ in range(t)] for _ in range(d)]
    cur = _cost(P, Pinv, V, N, t, d, D, T, INV)
    for it in range(iters):
        if cur == 0:
            break
        if time.monotonic() > deadline:
            return None
        temp = max(0.2, 2.0 * (1.0 - it / iters))
        if t == 1 or rng.random() < 0.6:
            l = rng.randrange(d)
            f = rng.randrange(t)
            old = V[l][f]
            new = rng.randrange(N)
            if new == old:
                continue
            V[l][f] = new
            c = _cost(P, Pinv, V, N, t, d, D, T, INV)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur = c
            else:
                V[l][f] = old
        else:
            l = rng.randrange(d)
            f1, f2 = rng.sample(range(t), 2)
            P[l][f1], P[l][f2] = P[l][f2], P[l][f1]
            Pinv[l][P[l][f1]] = f1
            Pinv[l][P[l][f2]] = f2
            c = _cost(P, Pinv, V, N, t, d, D, T, INV)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur = c
            else:
                P[l][f1], P[l][f2] = P[l][f2], P[l][f1]
                Pinv[l][P[l][f1]] = f1
                Pinv[l][P[l][f2]] = f2
    if cur == 0:
        return P, V
    return None


def _edges(N, t, d, T, P, V):
    """Edge list of the lift: A vertices are 0..tN-1, B vertices are tN..2tN-1."""
    E = set()
    for f in range(t):
        for x in range(N):
            a = f * N + x
            for l in range(d):
                b = (t + P[l][f]) * N + T[x][V[l][f]]
                E.add((a, b))
    return sorted(E)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    if time_limit >= 3:
        deadline = start + min(0.9 * time_limit, time_limit - 2.0)
    else:
        deadline = start + 0.6 * time_limit
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

    # D = 3 record family for d = q + 2 (Araujo-Pardo & Lopez).
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            n, e = lib.araujo_lopez_graph(d - 2)
            consider(n, e)
        except ValueError:
            pass

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

    moore = lib._moore_bound(d, D)
    feasible_ts = [t for t in (1, 2, 3, 4) if moore // (2 * t) >= 1]
    budget = 1.0
    fails = 0
    while time.monotonic() < deadline:
        ts = [t for t in feasible_ts if best_n // (2 * t) + 1 <= moore // (2 * t)]
        if not ts:
            break
        t = rng.choice([x for x in TS if x in ts] or ts)
        Nmin = best_n // (2 * t) + 1
        Nmax = moore // (2 * t)
        N = min(Nmax, Nmin + rng.randrange(0, 3))

        groups = _groups(N)
        rng.shuffle(groups)
        found = None
        for m, k, r in groups[:MAX_GROUPS]:
            if time.monotonic() >= deadline:
                break
            _, mul, inv = lib.semidirect_group(m, k, r)
            T = [[mul(x, g) for g in range(N)] for x in range(N)]
            INV = [inv(g) for g in range(N)]
            att_deadline = min(deadline, time.monotonic() + budget)
            res = _anneal(N, t, d, D, T, INV, rng, ITERS, att_deadline)
            if res is not None:
                found = (N, t, T, res)
                break

        if found is not None:
            N, t, T, (P, V) = found
            consider(2 * t * N, _edges(N, t, d, T, P, V))
            fails = 0
        else:
            fails += 1
            if fails % 4 == 0:
                budget = min(budget * 1.6, 0.3 * time_limit)

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
