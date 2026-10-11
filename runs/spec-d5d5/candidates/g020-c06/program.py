import itertools
import math
import random
import time

import lib

MAX_GROUPS_PER_ATTEMPT = 12   # single-orbit: groups tried per order N
ITERS = 600                   # single-orbit: annealing steps per try
T_HOT = 1.5
T_COLD = 0.15

MAX_GROUPS_2 = 8              # two-orbit: groups tried per order N
ITERS2 = 900                  # two-orbit: annealing steps per try
T_HOT2 = 2.0
T_COLD2 = 0.1
PER_N_BUDGET = 3.0            # seconds spent on one order N in the two-orbit scan


class _Best:
    """Holds the best valid graph found so far."""

    def __init__(self, d, D):
        self.d, self.D = d, D
        self.n, self.edges = 1, []

    def offer(self, n, edges):
        if n > self.n and lib.is_valid(n, edges, self.d, self.D):
            self.n, self.edges = n, edges


# ----------------------------------------------------------------------------
# Baseline families.
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
# Single-orbit bi-Cayley search over Z_m x| Z_k (order N, 2N vertices).
# ----------------------------------------------------------------------------

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
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _unreached(N, T, invs, S, D)
    for it in range(iters):
        if cur == 0:
            return S
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _unreached(N, T, invs, S2, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            S, cur = S2, v
    if cur == 0:
        return S
    return None


def _attempt(N, d, D, rng, deadline):
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


def _single_orbit(d, D, rng, deadline, best):
    Nmax = lib._moore_bound(d, D) // 2
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
            T, S = res
            edges = [(x, N + T[x][g]) for x in range(N) for g in S]
            best.offer(2 * N, edges)
            cands = {M for M in cands if M > N}
            if N + 1 <= Nmax:
                cands.add(N + 1)
            success = True
            break
        if not success:
            budget *= 2


# ----------------------------------------------------------------------------
# NEW: two-orbit voltage lift over a semidirect group.
#
# Base graph: two A-orbits (A_0, A_1) and two B-orbits (B_0, B_1), each of size N.
# Each A_a has d darts: p to B_0 and d-p to B_1 for a = 0; d-p to B_0 and p to
# B_1 for a = 1. Then every B_b also receives exactly d darts, so the lift is
# d-regular and bipartite with 4N vertices. A dart (a, b, g) joins A_a,x to
# B_b,(x*g) for every x. Left multiplication is an automorphism, so the four
# orbit representatives are sufficient sources for the diameter check. The
# voltages are searched by simulated annealing, and each dart's voltage is
# kept distinct within its (a, b) class to avoid duplicate edges.
# ----------------------------------------------------------------------------

def _darts_init(d, p, N, rng):
    darts = []
    for a in (0, 1):
        pa = p if a == 0 else d - p
        for b, cnt in ((0, pa), (1, d - pa)):
            for g in rng.sample(range(N), cnt):
                darts.append([a, b, g])
    return darts


def _cost2(N, T, darts, D):
    """Total unreached (source, vertex) pairs over the four orbit representatives."""
    V = 4 * N
    adj = [[] for _ in range(V)]
    for a, b, g in darts:
        base = (2 + b) * N
        for x in range(N):
            u = a * N + x
            v = base + T[x][g]
            adj[u].append(v)
            adj[v].append(u)
    total = 0
    for src in (0, N, 2 * N, 3 * N):
        seen = bytearray(V)
        seen[src] = 1
        frontier = [src]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            cnt += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += V - cnt
    return total


def _anneal2(N, T, d, D, rng, p, iters, deadline):
    darts = _darts_init(d, p, N, rng)
    cur = _cost2(N, T, darts, D)
    for it in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        temp = T_HOT2 * (T_COLD2 / T_HOT2) ** (it / iters)
        i = rng.randrange(len(darts))
        a, b, old = darts[i]
        used = {darts[j][2] for j in range(len(darts))
                if j != i and darts[j][0] == a and darts[j][1] == b}
        g = rng.randrange(N)
        if g in used or g == old:
            continue
        darts[i][2] = g
        v = _cost2(N, T, darts, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            darts[i][2] = old
    return darts if cur == 0 else None


def _edges2(N, T, darts):
    edges = []
    for a, b, g in darts:
        for x in range(N):
            edges.append((a * N + x, (2 + b) * N + T[x][g]))
    return edges


def _two_orbit(d, D, rng, deadline, best):
    Nlo = max(d + 1, best.n // 4 + 1)
    Nhi = lib._moore_bound(d, D) // 4
    N = Nlo
    while N <= Nhi and time.monotonic() < deadline:
        groups = _groups(N)
        rng.shuffle(groups)
        per_deadline = min(deadline, time.monotonic() + PER_N_BUDGET)
        for m, k, r in groups[:MAX_GROUPS_2]:
            if time.monotonic() > per_deadline:
                break
            order, mul, inv = lib.semidirect_group(m, k, r)
            T = [[mul(x, g) for g in range(N)] for x in range(N)]
            p = rng.randrange(1, d)
            darts = _anneal2(N, T, d, D, rng, p, ITERS2, per_deadline)
            if darts is not None:
                best.offer(4 * N, _edges2(N, T, darts))
                break
        N += 1


def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = _Best(d, D)

    # Record-matching case: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        best.offer(n, e)
        return best.n, best.edges

    if D >= 2:
        best.offer(*lib.haar_graph(d, range(d)))
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            best.offer(pg[0], pg[1])
    if D >= 4 and time.monotonic() < start + 0.1 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            best.offer(gq[0], gq[1])

    if d < 2 or D < 2:
        return best.n, best.edges

    # Phase 1: single-orbit bi-Cayley search (secures the record-level baseline).
    _single_orbit(d, D, rng, start + 0.25 * time_limit, best)

    # Phase 2: two-orbit voltage lifts, aiming above the current best order.
    _two_orbit(d, D, rng, start + 0.85 * time_limit, best)

    if not lib.is_valid(best.n, best.edges, d, D):
        return 1, []
    return best.n, best.edges
