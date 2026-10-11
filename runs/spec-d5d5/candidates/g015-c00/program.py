import math
import random
import time

import itertools

import lib

SAMPLE = 24        # candidate replacements scored per annealing step
ITERS = 500        # steps per (group, connection set) try
MAX_GROUPS = 14    # groups tried per order N within one attempt


# ----------------------------------------------------------------------------
# Baseline families: always checked with lib.is_valid before use.
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
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley graphs over Z_m x|_r Z_k.
#
# Vertices A_x, B_y (x, y in G, |G| = N). Edge A_x -- B_{x s} for s in S, |S| = d.
# Left multiplication is an automorphism that preserves the sides, and it is
# transitive on each side, so diameter <= D iff every vertex lies within D of
# A_0 and of B_0.
#
# New routine: "stamp BFS + sampled steepest descent".
#  * The BFS uses a per-source stamp array instead of allocating a bytearray,
#    so each cost evaluation costs only its neighbour scans.
#  * Each annealing step scores SAMPLE random single-element replacements and
#    keeps the best one (then applies Metropolis acceptance to it), rather than
#    taking one random proposal per step. This converges to zero-cost sets
#    in far fewer evaluations.
# ----------------------------------------------------------------------------

def _groups(N):
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _cost(N, T, S, Sinv, D, mark, box):
    """Number of (source, vertex) pairs at distance > D from A_0 or B_0."""
    total = 0
    for src in (0, N):
        box[0] += 1
        st = box[0]
        mark[src] = st
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < N:
                    row = T[u]
                    for g in S:
                        v = N + row[g]
                        if mark[v] != st:
                            mark[v] = st
                            nxt.append(v)
                else:
                    row = T[u - N]
                    for h in Sinv:
                        v = row[h]
                        if mark[v] != st:
                            mark[v] = st
                            nxt.append(v)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += 2 * N - count
    return total


def _search(N, T, invs, d, D, rng, deadline, iters):
    """Sampled steepest-descent annealing over S = {0, s_1, ..., s_{d-1}}."""
    mark = [0] * (2 * N)
    box = [0]
    S = [0] + rng.sample(range(1, N), d - 1)
    Sinv = [invs[g] for g in S]
    cur = _cost(N, T, S, Sinv, D, mark, box)
    for it in range(iters):
        if cur == 0:
            return S
        if time.monotonic() > deadline:
            break
        best_c = None
        for _ in range(SAMPLE):
            i = rng.randrange(1, d)
            c = rng.randrange(1, N)
            if c in S:
                continue
            S2 = S[:]
            S2[i] = c
            Sinv2 = [invs[g] for g in S2]
            v = _cost(N, T, S2, Sinv2, D, mark, box)
            if best_c is None or v < best_c[0]:
                best_c = (v, S2, Sinv2)
        if best_c is None:
            continue
        v, S2, Sinv2 = best_c
        temp = max(0.05, 2.0 * (1.0 - it / iters))
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            S, Sinv, cur = S2, Sinv2, v
    return S if cur == 0 else None


def _attempt(N, d, D, rng, deadline):
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            return None
        _, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        S = _search(N, T, invs, d, D, rng, deadline, ITERS)
        if S is not None:
            return T, S
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.7 * time_limit
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
    top = min(Nmax, Nmax // 2 + 5)
    cands = set(range(d + 1, top + 1))

    budget = 0.5
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
            # Only larger orders can improve now; try one step above the success.
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
