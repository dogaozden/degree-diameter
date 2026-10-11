import itertools
import math
import random
import time

import numpy as np

import lib

ITERS = 800                 # annealing steps per (group, connection set) try
GROUPS_PER_ATTEMPT = 40     # groups tried for one order N within one attempt
TOP_SLACK = 16              # search orders up to Nmax//2 + TOP_SLACK
FIRST_BUDGET = 0.25         # seconds per order in the first round
BUDGET_GROWTH = 1.4         # budget multiplier after a failed round
DEADLINE_FRACTION = 0.8     # leave margin for the final validity check


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
# NEW: group families as vectorised multiplication tables.
#
# Besides the metacyclic groups Z_m x| Z_k, we also search abelian groups
# Z_a x Z_b. Every group is held as an N x N numpy table T[x, g] = x*g with
# identity 0, so one search loop serves all families.
# ----------------------------------------------------------------------------

def _group_params(N):
    """Parameters of every group of order N in the two families used here."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append(("sd", m, k, r))
    for a in range(1, math.isqrt(N) + 1):
        if N % a == 0:
            out.append(("ab", a, N // a))
    return out


def _table(p):
    """Vectorised N x N multiplication table for the group described by p."""
    if p[0] == "sd":
        _, m, k, r = p
        N = m * k
        idx = np.arange(N, dtype=np.int64)
        a = idx // k
        b = idx % k
        pw = np.array([pow(r, j, m) for j in range(k)], dtype=np.int64)
        A = a[:, None]
        B = b[:, None]
        C = a[None, :]
        Dd = b[None, :]
        return ((A + pw[B] * C) % m) * k + (B + Dd) % k
    _, a, b = p
    N = a * b
    idx = np.arange(N, dtype=np.int64)
    I = idx // b
    J = idx % b
    return ((I[:, None] + I[None, :]) % a) * b + (J[:, None] + J[None, :]) % b


# ----------------------------------------------------------------------------
# Bi-Cayley search. Vertices A_x and B_y (x, y in G); edge A_x -- B_{x s}
# for s in S with |S| = d and 0 (the identity) in S WLOG.
#
# NEW: BFS is vectorised over frontiers with numpy boolean masks instead of
# Python loops, so each annealing step is much cheaper.
# ----------------------------------------------------------------------------

def _unreached(N, T, invs, S, D):
    """Count (vertex, source) pairs not within distance D, for sources A_0 and B_0."""
    S_arr = np.asarray(S, dtype=np.int64)
    Sinv = invs[S_arr]
    total = 0
    for src_is_a in (True, False):
        seenA = np.zeros(N, dtype=bool)
        seenB = np.zeros(N, dtype=bool)
        if src_is_a:
            seenA[0] = True
            fA = np.array([0], dtype=np.int64)
            fB = np.zeros(0, dtype=np.int64)
        else:
            seenB[0] = True
            fB = np.array([0], dtype=np.int64)
            fA = np.zeros(0, dtype=np.int64)
        count = 1
        for _ in range(D):
            if fA.size == 0 and fB.size == 0:
                break
            nB = np.zeros(N, dtype=bool)
            if fA.size:
                nB[T[np.ix_(fA, S_arr)]] = True   # A_x -> B_{x s}
                nB &= ~seenB
            nA = np.zeros(N, dtype=bool)
            if fB.size:
                nA[T[np.ix_(fB, Sinv)]] = True    # B_y -> A_{y s^-1}
                nA &= ~seenA
            seenB |= nB
            seenA |= nA
            fB = np.flatnonzero(nB)
            fA = np.flatnonzero(nA)
            count += fA.size + fB.size
        total += 2 * N - count
    return int(total)


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
    """Try groups of order N until one yields a connection set of diameter <= D, or time runs out."""
    groups = _group_params(N)
    rng.shuffle(groups)
    for p in groups[:GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        T = _table(p)
        invs = np.argmax(T == 0, axis=1)   # unique y with x*y = identity
        S = _anneal(N, T, invs, d, D, rng, ITERS, deadline)
        if S is not None:
            return T, S
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + DEADLINE_FRACTION * time_limit
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
    top = min(Nmax, Nmax // 2 + TOP_SLACK)
    cands = set(range(d + 1, top + 1))

    budget = FIRST_BUDGET
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
            edges = [(x, N + int(T[x, g])) for x in range(N) for g in S]
            consider(2 * N, edges)
            # Only larger orders can improve now.
            cands = {M for M in cands if M > N}
            success = True
            break
        if not success:
            budget *= BUDGET_GROWTH

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
