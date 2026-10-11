import itertools
import math
import random
import time

import lib

ITERS = 700                   # annealing steps per (p, N, group) attempt
T_HOT = 8.0                   # initial temperature (unreached-pair units)
T_COLD = 0.3                  # final temperature
P_CHOICES = (2, 3, 4)         # base-graph sizes per side (p = 1 is the parent's family)
WINDOW = 24                   # search orders with 2pN in (best_n, best_n + WINDOW]
GROUP_MOVE_PROB = 0.5         # chance a voltage move is a product of two voltages
SWAP_PROB = 0.25              # chance a move swaps two targets within one layer
BUDGET_START = 2.5            # seconds per attempt, first try
BUDGET_CAP = 8.0              # cap on per-attempt seconds


# ----------------------------------------------------------------------------
# Safe fallbacks (always checked with lib.is_valid before use).
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
# Bipartite voltage lifts over non-cyclic groups with p base vertices per side.
#
# Base: p A-vertices and p B-vertices, d "layers". Layer l gives each A_i one dart
# to B_{sig_l(i)} with voltage volt_l(i). The lift has vertices A(i,x) and B(j,y)
# for x, y in G, and edges A(i,x) -- B(j, x*g) for each dart (i, j, g).
# Left multiplication by h in G is an automorphism, so eccentricities from the
# 2p identity vertices decide the diameter. The graph is bipartite (A vs B) and
# has 2pN vertices. The parent's bi-Cayley search is the p = 1 case.
# ----------------------------------------------------------------------------

def _groups(N):
    """Semidirect parameters (m, k, r) giving groups Z_m x|_r Z_k of order N."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _adjacency(p, N, d, T, sig, volt):
    """Adjacency lists of the lift (may contain duplicates; only used for BFS)."""
    n = 2 * p * N
    adj = [[] for _ in range(n)]
    for l in range(d):
        sl = sig[l]
        vl = volt[l]
        for i in range(p):
            j = sl[i]
            g = vl[i]
            ai = i * N
            bj = (p + j) * N
            for x in range(N):
                a = ai + x
                b = bj + T[x][g]
                adj[a].append(b)
                adj[b].append(a)
    return adj


def _unreached(n, adj, sources, D):
    """Total count of (source, vertex) pairs not within distance D."""
    total = 0
    for s in sources:
        seen = bytearray(n)
        seen[s] = 1
        frontier = [s]
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
        total += n - count
    return total


def _edges(p, N, d, T, sig, volt):
    """Deduplicated edge list of the lift."""
    es = set()
    for l in range(d):
        for i in range(p):
            j = sig[l][i]
            g = volt[l][i]
            for x in range(N):
                a = i * N + x
                b = (p + j) * N + T[x][g]
                es.add((a, b))
    return list(es)


def _anneal(p, N, d, D, T, rng, iters, deadline):
    """Anneal targets and voltages to make every base-vertex eccentricity <= D."""
    n = 2 * p * N
    sources = [b * N for b in range(2 * p)]
    sig = [rng.sample(range(p), p) for _ in range(d)]
    volt = [[rng.randrange(N) for _ in range(p)] for _ in range(d)]

    def cost():
        return _unreached(n, _adjacency(p, N, d, T, sig, volt), sources, D)

    cur = cost()
    for it in range(iters):
        if cur == 0:
            break
        if time.monotonic() > deadline:
            return None
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        l = rng.randrange(d)
        if p >= 2 and rng.random() < SWAP_PROB:
            i1, i2 = rng.sample(range(p), 2)
            row = sig[l]
            row[i1], row[i2] = row[i2], row[i1]
            v = cost()
            if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
                cur = v
            else:
                row[i1], row[i2] = row[i2], row[i1]
        else:
            i = rng.randrange(p)
            old = volt[l][i]
            if rng.random() < GROUP_MOVE_PROB:
                a = volt[rng.randrange(d)][rng.randrange(p)]
                b = volt[rng.randrange(d)][rng.randrange(p)]
                new = T[a][b]
            else:
                new = rng.randrange(N)
            if new == old:
                continue
            volt[l][i] = new
            v = cost()
            if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
                cur = v
            else:
                volt[l][i] = old
    if cur == 0:
        return sig, volt
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + min(0.8 * time_limit, time_limit - 6.0)

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

    if d < 2 or D < 2 or time.monotonic() >= deadline:
        return best

    moore = lib.moore_bound(d, D)
    rng = random.Random(seed)
    budget = BUDGET_START

    while time.monotonic() < deadline:
        cands = []
        for p in P_CHOICES:
            hi = min(moore, best_n + WINDOW) // (2 * p)
            lo = best_n // (2 * p) + 1
            for N in range(max(lo, 2), hi + 1):
                cands.append((p, N))
        if not cands:
            break
        rng.shuffle(cands)
        success = False
        for p, N in cands:
            if time.monotonic() >= deadline:
                break
            groups = _groups(N)
            if not groups:
                continue
            m, k, r = rng.choice(groups)
            _, mul, _ = lib.semidirect_group(m, k, r)
            T = [[mul(x, g) for g in range(N)] for x in range(N)]
            att_deadline = min(deadline, time.monotonic() + budget)
            res = _anneal(p, N, d, D, T, rng, ITERS, att_deadline)
            if res is None:
                continue
            sig, volt = res
            consider(2 * p * N, _edges(p, N, d, T, sig, volt))
            success = True
            break
        if success:
            budget = BUDGET_START
        else:
            budget = min(BUDGET_CAP, budget * 1.5)

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
