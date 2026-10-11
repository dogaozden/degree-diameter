import itertools
import math
import random
import time

import lib

MAX_GROUPS_PER_ATTEMPT = 12   # groups tried per (N, k) within one attempt
ITERS = 2000                  # annealing steps per (group, base pattern) try
T_HOT = 1.5                   # initial annealing temperature (unreached-pair units)
T_COLD = 0.15                 # final annealing temperature
KMAX = 4                      # largest base-side size k tried


# ----------------------------------------------------------------------------
# Baseline families (always checked with lib.is_valid before use).
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
# New idea: multi-orbit group lifts with a RANDOM REGULAR BASE MULTIGRAPH.
#
# Base graph: k vertices A_0..A_{k-1} and k vertices B_0..B_{k-1}. Its edges form
# a d-regular bipartite multigraph, built as the sum of d random permutation
# matrices (so every base vertex has degree exactly d). Each base dart (a, b)
# carries a group element g (distinct among parallel darts), and the lift on a
# group G of order N has vertices (s, x), s in 0..2k-1, x in G, with
#     (a, x) -- (k+b, x*g)   for every dart (a, b, g).
# Left multiplication by h is an automorphism, so the diameter is at most D iff
# every base vertex, at the identity fiber element, reaches all 2kN vertices
# within D steps. The lift has 2kN vertices, is bipartite and d-regular.
#
# The annealing moves individual voltages (group elements) and minimises the
# number of unreached (source, vertex) pairs.
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


def _pattern(k, d, rng):
    """Random d-regular bipartite multigraph on k+k base vertices, as a list of (a, b) darts."""
    counts = [[0] * k for _ in range(k)]
    for _ in range(d):
        p = list(range(k))
        rng.shuffle(p)
        for a in range(k):
            counts[a][p[a]] += 1
    pairs = []
    for a in range(k):
        for b in range(k):
            pairs.extend([(a, b)] * counts[a][b])
    return pairs


def _unreached(N, k, T, invs, darts, D):
    """Count (source, vertex) pairs not within distance D, over all 2k base sources at identity."""
    nb = 2 * k
    adj = [[] for _ in range(nb)]
    for a, b, g in darts:
        adj[a].append((k + b, g))            # (A_a, x) -> (B_b, x*g)
        adj[k + b].append((a, invs[g]))      # (B_b, y) -> (A_a, y*g^-1)
    total = 0
    for s in range(nb):
        seen = bytearray(nb * N)
        start = s * N                        # identity fiber element is 0
        seen[start] = 1
        count = 1
        frontier = [start]
        for _ in range(D):
            nxt = []
            for u in frontier:
                base, x = divmod(u, N)
                row = T[x]
                for tb, g in adj[base]:
                    v = tb * N + row[g]
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += nb * N - count
    return total


def _anneal(N, k, T, invs, pairs, d, D, rng, iters, deadline):
    """Anneal the voltages of a fixed base pattern until no pair is unreached."""
    mult = {}
    for p in pairs:
        mult[p] = mult.get(p, 0) + 1
    darts = []
    for (a, b), c in mult.items():
        for g in rng.sample(range(N), c):
            darts.append([a, b, g])
    cur = _unreached(N, k, T, invs, darts, D)
    for it in range(iters):
        if cur == 0:
            return darts
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        i = rng.randrange(len(darts))
        a, b, old = darts[i]
        g = rng.randrange(N)
        if g == old or any(x[0] == a and x[1] == b and x[2] == g for x in darts):
            continue
        darts[i][2] = g
        v = _unreached(N, k, T, invs, darts, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            darts[i][2] = old
    return darts if cur == 0 else None


def _attempt(N, k, d, D, rng, deadline):
    """Try groups of order N with random base patterns until a valid lift is found or time runs out."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, kk, r in groups[:MAX_GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        pairs = _pattern(k, d, rng)
        _, mul, inv = lib.semidirect_group(m, kk, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        darts = _anneal(N, k, T, invs, pairs, d, D, rng, ITERS, deadline)
        if darts is not None:
            return T, darts
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, 0.85 * time_limit - 1.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = (1, [])

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

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

    moore = lib._moore_bound(d, D)
    budget = 0.5
    while time.monotonic() < deadline:
        progressed = False
        for k in range(1, KMAX + 1):
            if time.monotonic() >= deadline:
                break
            # Smallest N whose lift (2kN vertices) beats the current best.
            N = max(best[0] // (2 * k) + 1, d)
            if 2 * k * N > moore:
                continue
            att = min(deadline, time.monotonic() + budget)
            res = _attempt(N, k, d, D, rng, att)
            if res is not None:
                T, darts = res
                edges = []
                for a, b, g in darts:
                    for x in range(N):
                        edges.append((a * N + x, (k + b) * N + T[x][g]))
                consider(2 * k * N, edges)
                progressed = True
        if not progressed:
            budget *= 2

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
