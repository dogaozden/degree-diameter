import itertools
import math
import random
import time

import numpy as np

import lib

MAX_GROUPS_PER_ATTEMPT = 30   # groups tried per order N within one attempt
K_BATCH = 48                  # neighbours evaluated together per tabu step
STEPS_PER_GROUP = 300         # tabu steps per (group, N) before moving on
STALL = 60                    # non-improving steps before a random restart
TENURE = 7                    # steps a removed connection element stays tabu
TOP_SLACK = 12                # search orders up to Nmax//2 + TOP_SLACK


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
# Left multiplication is an automorphism, so eccentricities from A_0 and B_0
# decide the diameter. Identity is WLOG in S.
#
# New helper: _batch_cost evaluates K connection sets at once with boolean
# matrix products (one 0/1 matrix per candidate), so a tabu search can look at
# K neighbours per step instead of one.
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


def _table(N, mul):
    """Multiplication table T[x, g] = x*g as an int64 array."""
    T = np.empty((N, N), dtype=np.int64)
    for x in range(N):
        for g in range(N):
            T[x, g] = mul(x, g)
    return T


def _batch_cost(T, Sb, N, D):
    """Unreached (source, vertex) pairs for each connection set (row of Sb), sources A_0 and B_0.

    Sb has shape (K, d). Each candidate gets its own N x N 0/1 matrix M with
    M[x, y] = 1 iff y = x*s for some s in the set; BFS runs as batched matmuls.
    """
    K = Sb.shape[0]
    P = T[:, Sb].transpose(1, 0, 2)            # (K, N, d): P[k, x, j] = x * s_j
    M = np.zeros((K, N, N), dtype=np.float32)
    kk = np.arange(K)[:, None, None]
    xx = np.arange(N)[None, :, None]
    M[kk, xx, P] = 1.0
    MT = np.ascontiguousarray(M.transpose(0, 2, 1))

    vA = np.zeros((K, 2, N), dtype=bool)       # A-side vertices reached, per source
    vB = np.zeros((K, 2, N), dtype=bool)       # B-side vertices reached, per source
    vA[:, 0, 0] = True                         # source 0 is A_0
    vB[:, 1, 0] = True                         # source 1 is B_0
    fA = vA.copy()
    fB = vB.copy()
    for _ in range(D):
        nB = (np.matmul(fA.astype(np.float32), M) > 0) & ~vB
        nA = (np.matmul(fB.astype(np.float32), MT) > 0) & ~vA
        vB |= nB
        vA |= nA
        fA, fB = nA, nB
    reached = vA.sum(axis=(1, 2)) + vB.sum(axis=(1, 2))
    return 4 * N - reached


def _tabu_search(N, T, d, D, rng, deadline, steps):
    """Tabu search over S = {0, s_1, ..., s_{d-1}} minimising unreached pairs. Returns S or None."""
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = int(_batch_cost(T, np.array([S]), N, D)[0])
    best = cur
    tabu = {}
    stall = 0
    for step in range(steps):
        if cur == 0:
            return S
        if time.monotonic() > deadline:
            return None
        cand, pos, vals = [], [], []
        for _ in range(K_BATCH):
            i = rng.randrange(1, d)
            c = rng.randrange(1, N)
            while c in S:
                c = rng.randrange(1, N)
            S2 = S[:]
            S2[i] = c
            cand.append(S2)
            pos.append(i)
            vals.append(c)
        costs = _batch_cost(T, np.array(cand), N, D)
        order = np.argsort(costs, kind="stable")
        chosen = None
        for j in order:
            j = int(j)
            if tabu.get(vals[j], -1) > step and int(costs[j]) >= best:
                continue
            chosen = j
            break
        if chosen is None:
            chosen = int(order[0])
        old = S[pos[chosen]]
        tabu[old] = step + TENURE
        S = cand[chosen]
        cur = int(costs[chosen])
        if cur < best:
            best = cur
            stall = 0
        else:
            stall += 1
        if stall > STALL:
            S = [0] + rng.sample(range(1, N), d - 1)
            cur = int(_batch_cost(T, np.array([S]), N, D)[0])
            best = cur
            tabu.clear()
            stall = 0
    return S if cur == 0 else None


def _attempt(N, d, D, rng, deadline):
    """Try groups of order N until one yields a connection set with diameter <= D, or time runs out."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = _table(N, mul)
        S = _tabu_search(N, T, d, D, rng, deadline, STEPS_PER_GROUP)
        if S is not None:
            return S, T
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
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
            S, T = res
            edges = [(x, N + int(T[x, g])) for x in range(N) for g in S]
            consider(2 * N, edges)
            # Only larger orders can improve now; allow one step above the success.
            cands = {M for M in cands if M > N}
            if N + 1 <= Nmax:
                cands.add(N + 1)
            success = True
            break
        if not success:
            budget *= 1.5

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
