import itertools
import math
import random
import time

import numpy as np

import lib

MAX_GROUPS_PER_ATTEMPT = 30   # groups tried per order N within one attempt
ITERS = 800                   # annealing steps per (group, connection set) try
TOP_SLACK = 8                 # search orders up to Nmax//2 + TOP_SLACK
PARENT_SHARE = 0.25           # share of the budget for the bi-Cayley search
SAFETY = 0.80                 # use this fraction of time_limit in total


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
# Bi-Cayley search over semidirect products Z_m x| Z_k of order N (parent method).
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
    """Simulated annealing over S = {0, s_1, ..., s_{d-1}} to zero unreached pairs."""
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _unreached(N, T, invs, S, D)
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
        v = _unreached(N, T, invs, S2, D)
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
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        S = _anneal(N, T, invs, d, D, rng, ITERS, deadline)
        if S is not None:
            return T, S
    return None


def _parent_search(d, D, rng, deadline, consider):
    """Bi-Cayley search over semidirect products (the parent's method), limited to the deadline."""
    Nmax = lib._moore_bound(d, D) // 2
    top = min(Nmax, Nmax // 2 + TOP_SLACK)
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
            T, S = res
            edges = [(x, N + T[x][g]) for x in range(N) for g in S]
            consider(2 * N, edges)
            cands = {M for M in cands if M > N}
            if N + 1 <= Nmax:
                cands.add(N + 1)
            success = True
            break
        if not success:
            budget *= 1.5


# ----------------------------------------------------------------------------
# NEW bold construction: random d-regular bipartite graphs on N + N vertices,
# repaired by degree-preserving 2-switches that minimise unordered pairs at
# distance > D. No group structure is imposed.
# ----------------------------------------------------------------------------

def _swap(ea, eb, Bm, e1, e2):
    """Double-edge switch: (a1,b1),(a2,b2) -> (a1,b2),(a2,b1). Self-inverse when applied again to (e1,e2)."""
    a1 = int(ea[e1]); a2 = int(ea[e2])
    b1 = int(eb[e1]); b2 = int(eb[e2])
    if a1 == a2 or b1 == b2 or Bm[a1, b2] or Bm[a2, b1]:
        return False
    Bm[a1, b1] = False
    Bm[a2, b2] = False
    Bm[a1, b2] = True
    Bm[a2, b1] = True
    eb[e1] = b2
    eb[e2] = b1
    return True


def _nbr(N, d, ea, eb):
    """Neighbour table (2N x d). A-vertices are 0..N-1, B-vertices are N..2N-1."""
    nbr = np.empty((2 * N, d), dtype=np.int64)
    nbr[:N] = (N + eb).reshape(N, d)           # edges of A-vertex a are a*d .. a*d+d-1
    idx = np.argsort(eb, kind="stable")        # edges grouped by B-vertex, d each
    nbr[N:] = ea[idx].reshape(N, d)
    return nbr


def _unreached_rows(nbr, D):
    """Return (unordered pairs at distance > D, per-vertex count of such partners)."""
    n = nbr.shape[0]
    R = np.eye(n, dtype=bool)
    for _ in range(D):
        new = R.copy()
        for k in range(nbr.shape[1]):
            new |= R[nbr[:, k]]
        R = new
    rowbad = n - R.sum(axis=1)
    return int(rowbad.sum()) // 2, rowbad


def _local_search(N, d, D, rng, deadline):
    """Find a bipartite d-regular graph on N+N vertices with diameter <= D, or return None."""
    E = N * d
    ea = np.repeat(np.arange(N, dtype=np.int64), d)
    eb = np.empty(E, dtype=np.int64)
    shifts = rng.sample(range(N), d)
    for a in range(N):
        for k in range(d):
            eb[a * d + k] = (a + shifts[k]) % N
    Bm = np.zeros((N, N), dtype=bool)
    Bm[ea, eb] = True
    # Randomise the start (simple, degree-preserving).
    for _ in range(4 * E):
        _swap(ea, eb, Bm, rng.randrange(E), rng.randrange(E))

    cur, rowbad = _unreached_rows(_nbr(N, d, ea, eb), D)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while cur > 0:
        now = time.monotonic()
        if now >= deadline:
            return None
        temp = max(0.12, 1.0 * (1.0 - (now - t0) / span))

        # Choose the first edge, biased towards vertices involved in bad pairs.
        if rowbad.any() and rng.random() < 0.7:
            bad_vs = np.flatnonzero(rowbad)
            v = int(bad_vs[rng.randrange(len(bad_vs))])
            if v < N:
                e1 = v * d + rng.randrange(d)
            else:
                cand = np.flatnonzero(eb == v - N)
                e1 = int(cand[rng.randrange(len(cand))])
        else:
            e1 = rng.randrange(E)
        e2 = rng.randrange(E)

        if not _swap(ea, eb, Bm, e1, e2):
            continue
        new, newrow = _unreached_rows(_nbr(N, d, ea, eb), D)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            cur, rowbad = new, newrow
        else:
            _swap(ea, eb, Bm, e1, e2)  # undo

    return [(int(ea[e]), N + int(eb[e])) for e in range(E)]


def _graph_search(d, D, rng, deadline, consider):
    """Binary-style search over the half-order N, using the local search at each N."""
    half = lib._moore_bound(d, D) // 2
    N = max(d + 1, int(0.48 * half))
    lo = None
    hi = None
    step = 6
    while True:
        remaining = deadline - time.monotonic()
        if remaining < 1.0 or N <= d or N > half:
            break
        budget = min(remaining, max(4.0, 0.4 * remaining))
        edges = _local_search(N, d, D, rng, time.monotonic() + budget)
        if edges is not None:
            consider(2 * N, edges)
            lo = N if lo is None else max(lo, N)
            N = N + step if hi is None else (lo + hi) // 2
        else:
            hi = N if hi is None else min(hi, N)
            N = N - step if lo is None else (lo + hi) // 2
        if lo is not None and hi is not None and hi - lo <= 1:
            break


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = SAFETY * time_limit
    deadline_all = start + total
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
    if D >= 4 and time.monotonic() < deadline_all:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if d < 2 or D < 2:
        return best

    # Phase 1: parent's bi-Cayley search, a short slice as a safety floor.
    _parent_search(d, D, rng, start + PARENT_SHARE * total, consider)

    # Phase 2: random-regular repair search (the bold change), for the rest of the budget.
    if d >= 3 and time.monotonic() < deadline_all:
        _graph_search(d, D, rng, deadline_all, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
