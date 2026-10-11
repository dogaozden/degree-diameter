import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Structured baselines: projective planes (D = 3) and W(q) (D = 4).
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
    """W(q) for the largest prime power q with q + 1 <= d, capped at q = 7 for speed."""
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over Z_m x|_r Z_k, searched by simulated annealing.
#
# Vertices: A_x = x and B_y = N + y for x, y in the group (coded 0..N-1).
# Edges:    A_x ~ B_{x*g} for every g in S, |S| = d.
# WLOG the identity lies in S (relabel B_y -> B_{y g0^-1}). Left translation is
# an automorphism, so checking distances from A_0 and B_0 covers all pairs.
# ----------------------------------------------------------------------------

MAX_GROUPS = 8        # groups tried per order N
PER_GROUP = 5.0       # seconds of annealing per group
ANNEAL_STALL = 1500   # restart the annealing after this many non-improving steps
ORDER_WINDOW = 4      # candidate orders N in [lo, lo + ORDER_WINDOW)


def _groups(N):
    """Semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


class _Group:
    """Semidirect group with cached right-multiplication tables R(g)[x] = x*g."""

    def __init__(self, m, k, r):
        self.N, self.mul, self.inv = lib.semidirect_group(m, k, r)
        self._R = {}

    def R(self, g):
        t = self._R.get(g)
        if t is None:
            mul = self.mul
            t = [mul(x, g) for x in range(self.N)]
            self._R[g] = t
        return t


def _unreached(N, Rf, Rb, D):
    """Count (source, vertex) pairs at distance > D from A_0 and from B_0.

    Rf[i][x] = x*g_i (A -> B step); Rb[i][y] = y*g_i^-1 (B -> A step).
    """
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
                    for R in Rf:
                        v = N + R[u]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    y = u - N
                    for R in Rb:
                        v = R[y]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += 2 * N - count
    return total


def _anneal_group(grp, N, d, D, rng, deadline):
    """Simulated annealing over connection sets S (identity fixed, d elements).

    Returns S with zero unreached pairs, or None if the deadline passes first.
    """
    def evaluate(S):
        Rf = [grp.R(g) for g in S]
        Rb = [grp.R(grp.inv(g)) for g in S]
        return _unreached(N, Rf, Rb, D)

    def fresh():
        S = [0] + rng.sample(range(1, N), d - 1)
        return S, evaluate(S)

    S, cur = fresh()
    best_cost = cur
    T = 2.0
    stall = 0
    while cur > 0:
        if time.monotonic() > deadline:
            return None
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = evaluate(S2)
        delta = v - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            S, cur = S2, v
        T = max(0.3, T * 0.999)
        if cur < best_cost:
            best_cost = cur
            stall = 0
        else:
            stall += 1
        if stall > ANNEAL_STALL:
            S, cur = fresh()
            best_cost = cur
            T = 2.0
            stall = 0
    return S


def _bicayley_edges(grp, N, S):
    edges = []
    for g in S:
        R = grp.R(g)
        for x in range(N):
            edges.append((x, N + R[x]))
    return 2 * N, edges


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.3, min(0.85 * time_limit, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for any D >= 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if D == 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Main search: bi-Cayley lifts with 2N vertices, N just above the record half.
    while best[0] < moore and time.monotonic() < deadline and d >= 2:
        lo = best[0] // 2 + 1
        if lo > moore // 2:
            break
        N = lo + rng.randrange(ORDER_WINDOW)
        if 2 * N > moore:
            N = moore // 2
        if N < lo or N < d:
            break

        groups = _groups(N)
        rng.shuffle(groups)
        found = None
        for m, k, r in groups[:MAX_GROUPS]:
            now = time.monotonic()
            if now >= deadline:
                break
            grp = _Group(m, k, r)
            per_deadline = min(deadline, now + PER_GROUP)
            S = _anneal_group(grp, N, d, D, rng, per_deadline)
            if S is not None:
                found = (grp, S)
                break

        if found is not None:
            grp, S = found
            n2, e2 = _bicayley_edges(grp, N, S)
            consider(n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
