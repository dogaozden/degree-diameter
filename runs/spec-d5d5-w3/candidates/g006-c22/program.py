import itertools
import math
import random
import time

import numpy as np

import lib

MAX_GROUPS_PER_ATTEMPT = 30   # groups tried per order N within one attempt
ITERS = 1500                  # annealing steps per restart
RESTARTS = 4                  # fresh random connection sets per group before moving on
TOP_SLACK = 12                # search orders up to Nmax//2 + TOP_SLACK


# ----------------------------------------------------------------------------
# Baseline families (fast, validated by lib.is_valid before use).
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
# NEW helper: vectorised distance check for bi-Cayley graphs.
#
# Vertices A_x and B_y (x, y in G). Edge A_x -- B_{x s} for s in S.
# Left multiplication is an automorphism, so the reach of A_0 and B_0 decides
# the diameter. Frontiers are index arrays; each BFS layer is one fancy-indexed
# gather M[frontier][:, S], which replaces the Python inner loops.
# ----------------------------------------------------------------------------

def _unreached_np(M, S, Sinv, N, D):
    """Count (source, vertex) pairs not within distance D, for sources A_0 and B_0.

    M[x, g] = x*g in the group. From A_x the neighbours are B_{x*s} (s in S);
    from B_y the neighbours are A_{y*s^-1} (s in S), i.e. M[y][Sinv].
    """
    total = 0
    for side in (0, 1):
        seen = [np.zeros(N, dtype=bool), np.zeros(N, dtype=bool)]
        seen[side][0] = True
        frontier = np.array([0], dtype=np.int64)
        cur = side
        count = 1
        for _ in range(D):
            tab = S if cur == 0 else Sinv
            tgt = M[frontier][:, tab].ravel()
            mark = np.zeros(N, dtype=bool)
            mark[tgt] = True
            mark &= ~seen[1 - cur]
            seen[1 - cur] |= mark
            frontier = np.nonzero(mark)[0]
            count += int(frontier.size)
            cur = 1 - cur
            if frontier.size == 0:
                break
        total += 2 * N - count
    return total


# ----------------------------------------------------------------------------
# Bi-Cayley search over semidirect products Z_m x| Z_k of order N.
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


def _anneal(N, M, invs, d, D, rng, iters, deadline):
    """Simulated annealing over S = {0, s_1, ..., s_{d-1}} to zero unreached pairs."""
    S = [0] + rng.sample(range(1, N), d - 1)
    Sa = np.array(S, dtype=np.int64)
    cur = _unreached_np(M, Sa, invs[Sa], N, D)
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
        S2a = np.array(S2, dtype=np.int64)
        v = _unreached_np(M, S2a, invs[S2a], N, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            S, cur = S2, v
    return S if cur == 0 else None


def _attempt(N, d, D, rng, deadline):
    """Try groups of order N; for each group run several independent annealing restarts."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        _, mul, inv = lib.semidirect_group(m, k, r)
        M = np.array([[mul(x, g) for g in range(N)] for x in range(N)], dtype=np.int64)
        invs = np.array([inv(g) for g in range(N)], dtype=np.int64)
        for _ in range(RESTARTS):
            if time.monotonic() > deadline:
                return None
            S = _anneal(N, M, invs, d, D, rng, ITERS, deadline)
            if S is not None:
                return M, S
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
            M, S = res
            edges = [(x, N + int(M[x, g])) for x in range(N) for g in S]
            consider(2 * N, edges)
            # Only larger orders can improve now; allow one step above the success.
            cands = {K for K in cands if K > N}
            if N + 1 <= Nmax:
                cands.add(N + 1)
            success = True
            break
        if not success:
            budget *= 1.5

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
