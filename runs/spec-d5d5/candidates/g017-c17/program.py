import itertools
import math
import random
import time

import numpy as np

import lib

MAX_GROUPS_PER_ATTEMPT = 12   # groups tried per order N within one attempt
BATCH = 24                    # candidate connection sets evaluated together per step
ITERS = 500                   # batched annealing steps per (group, attempt)
T_HOT = 1.2                   # initial temperature (in unreached-pair units)
T_COLD = 0.1                  # final temperature
BIG = 1e18                    # cost for invalid (duplicate-element) candidates


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
# Left multiplication is an automorphism, so the diameter is <= D iff the
# eccentricities of A_0 and B_0 are <= D. Identity (element 0) is WLOG in S.
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


# ----------------------------------------------------------------------------
# NEW helper: batched numpy reachability evaluator.
#
# Given K connection sets at once (array Sb of shape (K, d)), it computes for
# every candidate the total number of (source, vertex) pairs that are NOT within
# distance D, for the sources A_0 and B_0. Each BFS step is a gather over
# precomputed multiplication tables, so a whole batch costs a handful of numpy
# calls instead of K Python BFS runs.
#
#   R[x, g]  = x * g           (A_x -- B_{x g})
#   RI[y, g] = y * g^{-1}      (B_y -- A_{y g^{-1}})
# ----------------------------------------------------------------------------

def _unreached_batch(R, RI, N, Sb, D):
    K, d = Sb.shape
    ar = np.arange(K)[:, None, None]
    idx_b_from_a = RI[:, Sb].transpose(1, 0, 2)   # (K, N, d): for B_y, the A-neighbours y*s^-1
    idx_a_from_b = R[:, Sb].transpose(1, 0, 2)    # (K, N, d): for A_x, the B-neighbours x*s
    total = np.zeros(K, dtype=np.int64)
    for src_type in (0, 1):
        A = np.zeros((K, N), dtype=bool)
        B = np.zeros((K, N), dtype=bool)
        if src_type == 0:
            A[:, 0] = True
        else:
            B[:, 0] = True
        for _ in range(D):
            newB = B | A[ar, idx_b_from_a].any(axis=2)
            newA = A | B[ar, idx_a_from_b].any(axis=2)
            A, B = newA, newB
        reached = A.sum(axis=1) + B.sum(axis=1)
        total += 2 * N - reached
    return total


def _anneal_batch(R, RI, N, d, D, rng, deadline, iters):
    """Batched annealing: each step proposes BATCH single-coordinate mutations of S,
    evaluates them together, and moves to the best one (Metropolis-style acceptance).
    Returns a connection set with zero unreached pairs, or None."""
    nrng = np.random.default_rng(rng.randrange(1 << 30))
    S = np.array([0] + rng.sample(range(1, N), d - 1), dtype=np.int64)
    cur = float(_unreached_batch(R, RI, N, S[None, :], D)[0])
    if cur == 0:
        return S
    for it in range(iters):
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        cands = np.repeat(S[None, :], BATCH, axis=0)
        pos = nrng.integers(1, d, size=BATCH)
        vals = nrng.integers(1, N, size=BATCH)
        cands[np.arange(BATCH), pos] = vals
        srt = np.sort(cands, axis=1)
        dup = (srt[:, 1:] == srt[:, :-1]).any(axis=1)
        costs = _unreached_batch(R, RI, N, cands, D).astype(float)
        costs[dup] = BIG
        j = int(np.argmin(costs))
        v = costs[j]
        if v <= cur or nrng.random() < math.exp(-(v - cur) / temp):
            S = cands[j].copy()
            cur = v
            if cur == 0:
                return S
    return None


def _attempt(N, d, D, rng, deadline):
    """Try groups of order N until one yields a connection set with diameter <= D, or time runs out."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, k, r)
        R = np.array([[mul(x, g) for g in range(N)] for x in range(N)], dtype=np.int64)
        invs = np.array([inv(g) for g in range(N)], dtype=np.int64)
        RI = R[:, invs]
        S = _anneal_batch(R, RI, N, d, D, rng, deadline, ITERS)
        if S is not None:
            return R, S
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
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

    if d < 2 or D < 2:
        return best

    Nmax = lib._moore_bound(d, D) // 2   # bi-Cayley graph has 2N vertices
    top = min(Nmax, Nmax // 2 + 6)
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
            R, S = res
            edges = [(x, N + int(R[x, g])) for x in range(N) for g in S.tolist()]
            consider(2 * N, edges)
            # Only larger orders can improve now.
            cands = {M for M in cands if M > N}
            success = True
            break
        if not success:
            budget *= 2

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
