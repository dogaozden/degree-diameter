import itertools
import math
import random
import time

import lib

MAX_GROUPS_PER_ATTEMPT = 12   # groups tried per (k, N) attempt
ITERS = 500                   # annealing steps per group
T_HOT = 2.0                   # initial temperature (unreached-pair units)
T_COLD = 0.2                  # final temperature
ATTEMPT_BUDGET = 4.0          # seconds per (k, N) attempt
SPAN = 40                     # search window above the current lower bound
MAX_K_DEGREE = 8              # use multi-vertex bases only for d up to this


# ----------------------------------------------------------------------------
# Safe baseline families (always checked with lib.is_valid before use).
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q."""
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Multi-vertex voltage lifts over semidirect groups.
#
# Base bipartite multigraph: k "A" vertices, k "B" vertices, with matrix M
# (row sums = column sums = d). Each base dart (i, j, g) gives edges
#     A_i,x -- B_j,(x*g)   for every x in G,
# so the lift has 2kN vertices and is bipartite with degree d.
#
# Left multiplication by h is an automorphism of the lift, so the diameter
# condition only needs balls around the 2k base vertices with identity labels.
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


def _base_connected(k, M):
    """True if the bipartite support graph of matrix M on 2k nodes is connected."""
    seen = {0}
    stack = [0]  # node 0 is A_0; nodes 0..k-1 are A, k..2k-1 are B
    while stack:
        u = stack.pop()
        if u < k:
            nbrs = [k + j for j in range(k) if M[u][j] > 0]
        else:
            j = u - k
            nbrs = [i for i in range(k) if M[i][j] > 0]
        for v in nbrs:
            if v not in seen:
                seen.add(v)
                stack.append(v)
    return len(seen) == 2 * k


def _base_matrices(k, d):
    """All k x k nonnegative integer matrices with row and column sums d and connected support."""
    if k == 1:
        return [((d,),)]
    comps = [c for c in itertools.product(range(d + 1), repeat=k) if sum(c) == d]
    out = []
    for rows in itertools.product(comps, repeat=k):
        if all(sum(rows[i][j] for i in range(k)) == d for j in range(k)):
            if _base_connected(k, rows):
                out.append(rows)
    return out


def _adj(pairs, volt, invs, k):
    """Per-base-vertex dart lists: adjA[i] = [(j, g)], adjB[j] = [(i, g^-1)]."""
    adjA = [[] for _ in range(k)]
    adjB = [[] for _ in range(k)]
    for t, (i, j) in enumerate(pairs):
        g = volt[t]
        adjA[i].append((j, g))
        adjB[j].append((i, invs[g]))
    return adjA, adjB


def _unreached(N, k, adjA, adjB, D, T):
    """Total (base source, vertex) pairs not within distance D, over all 2k base sources."""
    kN = k * N
    total_n = 2 * kN
    tot = 0
    for s in range(2 * k):
        src = s * N if s < k else kN + (s - k) * N
        seen = bytearray(total_n)
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < kN:
                    i, x = divmod(u, N)
                    row = T[x]
                    for j, g in adjA[i]:
                        v = kN + j * N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    j, y = divmod(u - kN, N)
                    row = T[y]
                    for i, h in adjB[j]:
                        v = i * N + row[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        tot += total_n - count
    return tot


def _anneal(N, k, D, pairs, T, invs, rng, deadline):
    """Anneal dart voltages to zero the number of unreached (source, vertex) pairs."""
    L = len(pairs)
    groups = {}
    for t, p in enumerate(pairs):
        groups.setdefault(p, []).append(t)
    volt = [0] * L
    for p, ts in groups.items():
        for t, v in zip(ts, rng.sample(range(N), len(ts))):
            volt[t] = v

    def cost(vs):
        adjA, adjB = _adj(pairs, vs, invs, k)
        return _unreached(N, k, adjA, adjB, D, T)

    cur = cost(volt)
    for it in range(ITERS):
        if cur == 0 or time.monotonic() > deadline:
            break
        t = rng.randrange(L)
        p = pairs[t]
        used = {volt[u] for u in groups[p] if u != t}
        c = rng.randrange(N)
        if c in used:
            continue
        temp = T_HOT * (T_COLD / T_HOT) ** (it / ITERS)
        old = volt[t]
        volt[t] = c
        v = cost(volt)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            volt[t] = old
    return volt if cur == 0 else None


def _attempt(N, k, d, D, bases, rng, deadline):
    """Try groups of order N with base size k; return (n, edges) for a valid lift, else None."""
    groups = _groups(N)
    rng.shuffle(groups)
    for (m, kk, r) in groups[:MAX_GROUPS_PER_ATTEMPT]:
        if time.monotonic() >= deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, kk, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        M = rng.choice(bases)
        pairs = [(i, j) for i in range(k) for j in range(k) for _ in range(M[i][j])]
        volt = _anneal(N, k, D, pairs, T, invs, rng, deadline)
        if volt is None:
            continue
        n = 2 * k * N
        edges = []
        for t, (i, j) in enumerate(pairs):
            g = volt[t]
            for x in range(N):
                edges.append((i * N + x, k * N + j * N + T[x][g]))
        if lib.is_valid(n, edges, d, D):
            return n, edges
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(2.0, 0.85 * time_limit - 2.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = [1, []]

    def consider(n, e):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best[0], best[1] = n, e

    # Record-matching case: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best[0], best[1]

    # Safe fallbacks.
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

    # Main search: multi-vertex base lifts, biased toward the smallest orders
    # that would beat the current best.
    if D >= 2 and d >= 2:
        try:
            Moore = lib._moore_bound(d, D)
            Ks = [1, 2, 3] if d <= MAX_K_DEGREE else [1]
            bases = {}
            for k in Ks:
                bl = _base_matrices(k, d)
                if bl:
                    bases[k] = bl
            ks = list(bases)
            while ks and time.monotonic() < deadline:
                k = rng.choice(ks)
                Nmax = Moore // (2 * k)
                lo = max(d, best[0] // (2 * k) + 1)
                if lo > Nmax:
                    ks.remove(k)
                    continue
                span = min(Nmax, lo + SPAN) - lo
                N = lo + int(span * rng.random() ** 2)
                att_deadline = min(deadline, time.monotonic() + ATTEMPT_BUDGET)
                res = _attempt(N, k, d, D, bases[k], rng, att_deadline)
                if res is not None:
                    consider(*res)
        except Exception:
            pass  # keep whatever valid graph we already have

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best[0], best[1]
