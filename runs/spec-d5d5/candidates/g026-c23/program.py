import itertools
import math
import random
import time

import numpy as np

import lib

MAX_GROUPS_PER_ATTEMPT = 40   # groups tried per order N within one attempt
ITERS = 1500                  # annealing steps per (group, connection set) try


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
# Bi-Cayley search over semidirect products Z_m x| Z_k of order N.
#
# Vertices A_x and B_y (x, y in G). Edge A_x -- B_{x s} for s in S, |S| = d.
# Left multiplication is an automorphism, so BFS from A_0 and B_0 decides the
# diameter. Identity is WLOG in S.
#
# New in this version: a vectorised, frontier-based BFS evaluator. Each BFS
# layer is one numpy fancy-indexing step over the whole frontier, using two
# precomputed tables:
#   T[x, g]  = x * g    (A_x -> B_{x g})
#   TI[y, g] = y * g^-1 (B_y -> A_{y g^-1})
# so the search can afford far more annealing steps per second.
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


def _tables(N, m, k, r):
    """Build the right-multiplication table T and the right-division table TI as int64 arrays."""
    _, mul, inv = lib.semidirect_group(m, k, r)
    T = np.array([[mul(x, g) for g in range(N)] for x in range(N)], dtype=np.int64)
    invs = [inv(g) for g in range(N)]
    TI = np.array([[mul(x, invs[g]) for g in range(N)] for x in range(N)], dtype=np.int64)
    return T, TI


def _expand(frontier, table, S, N):
    """Boolean vector of all vertices on the other side adjacent to some vertex in the frontier."""
    out = np.zeros(N, dtype=bool)
    idx = np.flatnonzero(frontier)
    if idx.size:
        out[table[np.ix_(idx, S)].ravel()] = True
    return out


def _unreached(N, T, TI, S, D):
    """Count (source, vertex) pairs not within distance D, for sources A_0 and B_0."""
    total = 0
    for src in (0, N):
        seen_a = np.zeros(N, dtype=bool)
        seen_b = np.zeros(N, dtype=bool)
        fa = np.zeros(N, dtype=bool)
        fb = np.zeros(N, dtype=bool)
        if src < N:
            seen_a[src] = True
            fa[src] = True
        else:
            seen_b[src - N] = True
            fb[src - N] = True
        for _ in range(D):
            nb = _expand(fa, T, S, N) & ~seen_b
            na = _expand(fb, TI, S, N) & ~seen_a
            if not nb.any() and not na.any():
                break
            seen_b |= nb
            seen_a |= na
            fa, fb = na, nb
        total += 2 * N - int(seen_a.sum()) - int(seen_b.sum())
    return total


def _anneal(N, T, TI, d, D, rng, iters, deadline):
    """Simulated annealing over S = {0, s_1, ..., s_{d-1}} to zero unreached pairs."""
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _unreached(N, T, TI, np.array(S, dtype=np.int64), D)
    for it in range(iters):
        if cur == 0:
            return S
        if time.monotonic() > deadline:
            break
        temp = max(0.05, 2.0 * (1.0 - it / iters))
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _unreached(N, T, TI, np.array(S2, dtype=np.int64), D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            S, cur = S2, v
    return S if cur == 0 else None


def _attempt(N, d, D, rng, deadline):
    """Try groups of order N until one yields a connection set with diameter <= D, or time runs out."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        T, TI = _tables(N, m, k, r)
        S = _anneal(N, T, TI, d, D, rng, ITERS, deadline)
        if S is not None:
            return T, S
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + min(0.85 * time_limit, time_limit - 3.0)
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

    if D >= 2 and d >= 1:
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

    Nmax = lib._moore_bound(d, D) // 2   # bi-Cayley graph has 2N vertices
    # The faster evaluator lets the search reach a little further above Nmax // 2.
    top = min(Nmax, Nmax // 2 + 8)
    cands = set(range(d + 1, top + 1))

    budget = 0.4
    while time.monotonic() < deadline and cands:
        success = False
        for N in sorted(cands, reverse=True):
            now = time.monotonic()
            if now >= deadline:
                break
            att_deadline = min(deadline, now + budget)
            res = _attempt(N, d, D, rng, att_deadline)
            if res is None:
                continue
            T, TI_unused = None, None
            T, S = res
            # Rebuild edges from the table found in the attempt.
            edges = [(x, N + int(T[x][g])) for x in range(N) for g in S]
            consider(2 * N, edges)
            # Only larger orders can improve now; allow one step above the success.
            cands = {M for M in cands if M > N}
            if N + 1 <= Nmax:
                cands.add(N + 1)
            success = True
            break
        if not success:
            budget *= 2

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
