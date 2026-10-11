import itertools
import math
import random
import time

import numpy as np

import lib

MAX_GROUPS_PER_ATTEMPT = 30   # groups tried per attempt (one anneal each)
ITERS_SINGLE = 1500           # annealing steps per (group, pattern) for the single-orbit phase
ITERS_MULTI = 3000            # annealing steps per (group, pattern) for the multi-orbit phase
TOP_SLACK = 8                 # single-orbit phase searches orders up to Nmax//2 + TOP_SLACK
SEARCH_FRAC = 0.8             # share of time_limit used before the final check
SINGLE_FRAC = 0.35            # share of the search time given to the single-orbit phase


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
# Multi-orbit bi-Cayley lifts.
#
# Base graph: b vertices A_0..A_{b-1} and b vertices B_0..B_{b-1}; each vertex
# is a copy of a finite group G of order N (orbits). A(i,x) is adjacent to
# B(j, x*s) for every s in S[i][j]. Left multiplication by G is an automorphism,
# so the diameter is decided by BFS from A(i,e) and B(j,e), i.e. 2b sources.
#
# A pattern c (b x b matrix with all row and column sums equal to d) gives the
# sizes |S[i][j]| = c[i][j]; the sum of d random permutation matrices yields such
# a pattern, so every vertex has degree exactly d.
# Normalization: S[0][j] contains the identity (relabel column j), which is the
# b=1 WLOG of the single-orbit search, generalized.
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


def _pattern(b, d, rng):
    """Random b x b integer matrix with all row and column sums d (sum of d permutation matrices)."""
    c = [[0] * b for _ in range(b)]
    for _ in range(200):
        c = [[0] * b for _ in range(b)]
        for _ in range(d):
            perm = list(range(b))
            rng.shuffle(perm)
            for i in range(b):
                c[i][perm[i]] += 1
        if b == 1 or all(c[i][j] > 0 for i in range(b) for j in range(b)):
            return c
    return c


def _sample(N, b, c, rng):
    """Random connection sets S[i][j] of size c[i][j]; row 0 always contains the identity (index 0)."""
    S = [[[] for _ in range(b)] for _ in range(b)]
    for i in range(b):
        for j in range(b):
            k = c[i][j]
            if k == 0:
                continue
            if i == 0:
                S[i][j] = [0] + rng.sample(range(1, N), k - 1)
            else:
                S[i][j] = rng.sample(range(N), k)
    return S


def _slots(b, c):
    """Mutable (i, j, position) slots; the identity slots in row 0 are fixed."""
    return [(i, j, p) for i in range(b) for j in range(b)
            for p in range(c[i][j]) if not (i == 0 and p == 0)]


def _nbr_table(N, b, d, Tn, invn, S):
    """Regular neighbour table (V x d) of the bi-Cayley graph, built with vectorised gathers.

    Vertex A(i,x) = i*N + x, vertex B(j,y) = b*N + j*N + y.
    Edge A(i,x)--B(j, x*s) for s in S[i][j]; B(j,y) receives A(i, y*s^{-1}).
    """
    V = 2 * b * N
    nbr = np.empty((V, d), dtype=np.int64)
    ca = [0] * b
    cb = [0] * b
    for i in range(b):
        for j in range(b):
            for s in S[i][j]:
                nbr[i * N:(i + 1) * N, ca[i]] = b * N + j * N + Tn[:, s]
                nbr[b * N + j * N:b * N + (j + 1) * N, cb[j]] = i * N + Tn[:, invn[s]]
                ca[i] += 1
                cb[j] += 1
    return nbr


def _unreached(nbr, b, N, D, d):
    """Number of (source, vertex) pairs not within distance D, sources A(i,e) and B(j,e)."""
    V = 2 * b * N
    sources = [i * N for i in range(b)] + [b * N + j * N for j in range(b)]
    k = len(sources)
    F = np.zeros((k, V), dtype=bool)
    F[np.arange(k), sources] = True
    reach = F.copy()
    for _ in range(D):
        Nxt = np.zeros((k, V), dtype=bool)
        for t in range(d):
            Nxt |= F[:, nbr[:, t]]
        Nxt &= ~reach
        if not Nxt.any():
            break
        reach |= Nxt
        F = Nxt
    return k * V - int(reach.sum())


def _anneal(N, b, d, Tn, invn, c, D, rng, iters, deadline):
    """Simulated annealing over connection sets to zero the unreached pairs."""
    S = _sample(N, b, c, rng)
    slots = _slots(b, c)
    if not slots:
        return None
    cur = _unreached(_nbr_table(N, b, d, Tn, invn, S), b, N, D, d)
    for it in range(iters):
        if cur == 0:
            return S
        if time.monotonic() > deadline:
            break
        i, j, p = rng.choice(slots)
        g = rng.randrange(N)
        if g in S[i][j]:
            continue
        old = S[i][j][p]
        S[i][j][p] = g
        v = _unreached(_nbr_table(N, b, d, Tn, invn, S), b, N, D, d)
        temp = max(0.05, 2.0 * (1.0 - it / iters))
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            S[i][j][p] = old
    return S if cur == 0 else None


def _attempt(N, b, d, D, rng, deadline, iters):
    """Try groups of order N (one anneal each) until a connection set reaches diameter D."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        _, mul, inv = lib.semidirect_group(m, k, r)
        Tn = np.array([[mul(x, g) for g in range(N)] for x in range(N)], dtype=np.int64)
        invn = [inv(g) for g in range(N)]
        c = _pattern(b, d, rng)
        S = _anneal(N, b, d, Tn, invn, c, D, rng, iters, deadline)
        if S is not None:
            return N, b, c, Tn, S
    return None


def _edges(N, b, Tn, S):
    """Explicit (n, edges) of the bi-Cayley graph described by Tn and S."""
    edges = []
    for i in range(b):
        for j in range(b):
            for s in S[i][j]:
                for x in range(N):
                    edges.append((i * N + x, b * N + j * N + int(Tn[x, s])))
    return 2 * b * N, edges


def _phase_single(d, D, rng, deadline, moore, consider):
    """Single-orbit (b=1) search, descending over candidate orders (as in the parent)."""
    Nmax = moore // 2
    top = min(Nmax, Nmax // 2 + TOP_SLACK)
    cands = set(range(d + 1, top + 1))
    budget = 0.4
    while time.monotonic() < deadline and cands:
        success = False
        for N in sorted(cands, reverse=True):
            now = time.monotonic()
            if now >= deadline:
                break
            res = _attempt(N, 1, d, D, rng, min(deadline, now + budget), ITERS_SINGLE)
            if res is None:
                continue
            N_, b_, c, Tn, S = res
            n, e = _edges(N_, 1, Tn, S)
            consider(n, e)
            cands = {M for M in cands if M > N}
            if N + 1 <= Nmax:
                cands.add(N + 1)
            success = True
            break
        if not success:
            budget *= 1.5


def _phase_multi(d, D, rng, deadline, moore, best_n_fn, consider):
    """Multi-orbit search: for b in {2, 3}, aim just above the current best order."""
    budget = {2: 0.8, 3: 0.8}
    turn = 0
    while time.monotonic() < deadline:
        best_n = best_n_fn()
        feasible = [b for b in (2, 3) if best_n // (2 * b) + 1 <= moore // (2 * b)]
        if not feasible:
            break
        b = feasible[turn % len(feasible)]
        turn += 1
        N = best_n // (2 * b) + 1
        now = time.monotonic()
        res = _attempt(N, b, d, D, rng, min(deadline, now + budget[b]), ITERS_MULTI)
        if res is None:
            budget[b] *= 1.3
            continue
        N_, b_, c, Tn, S = res
        n, e = _edges(N_, b_, Tn, S)
        consider(n, e)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + SEARCH_FRAC * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    st = {"best": (1, [])}

    def consider(n, e):
        if n > st["best"][0] and lib.is_valid(n, e, d, D):
            st["best"] = (n, e)

    # Record-matching case: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return st["best"]

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
        return st["best"]

    moore = lib._moore_bound(d, D)
    now = time.monotonic()
    single_deadline = now + SINGLE_FRAC * (deadline - now)
    try:
        _phase_single(d, D, rng, single_deadline, moore, consider)
    except Exception:
        pass
    try:
        _phase_multi(d, D, rng, deadline, moore, lambda: st["best"][0], consider)
    except Exception:
        pass

    n, e = st["best"]
    if not lib.is_valid(n, e, d, D):
        return 1, []
    return n, e
