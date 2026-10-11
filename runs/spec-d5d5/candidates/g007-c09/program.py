import itertools
import math
import random
import time

import lib

MAX_GROUPS_PER_ATTEMPT = 30   # groups tried per (order, base) within one attempt
ITERS = 800                   # annealing steps for bi-Cayley tries
LIFT_ITERS = 500              # annealing steps for multi-orbit lift tries
TOP_SLACK = 8                 # search orders up to Nmax//2 + TOP_SLACK
LIFT_BASES = (2, 3)           # number of base vertices per side for lifts


# ----------------------------------------------------------------------------
# Safe baseline families (fast, validated before use).
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


class _Best:
    """Holds the best validated graph found so far."""

    def __init__(self):
        self.n = 1
        self.edges = []

    def offer(self, n, edges, d, D):
        if n > self.n and lib.is_valid(n, edges, d, D):
            self.n = n
            self.edges = edges


# ----------------------------------------------------------------------------
# Groups: semidirect products Z_m x|_r Z_k of order N, coded as a*k+b, identity 0.
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
# Family A: bi-Cayley graphs (one orbit per side). Parent's construction.
# ----------------------------------------------------------------------------

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
    """Try groups of order N until one yields a connection set with diameter <= D."""
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


def _bicayley_phase(d, D, rng, deadline, best, moore):
    """Bi-Cayley search: A_x -- B_{x s} for s in S, |S| = d."""
    if d < 2:
        return
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
            att_deadline = min(deadline, now + budget)
            res = _attempt(N, d, D, rng, att_deadline)
            if res is None:
                continue
            T, S = res
            edges = [(x, N + T[x][g]) for x in range(N) for g in S]
            best.offer(2 * N, edges, d, D)
            cands = {M for M in cands if M > N}
            if N + 1 <= Nmax:
                cands.add(N + 1)
            success = True
            break
        if not success:
            budget *= 1.5


# ----------------------------------------------------------------------------
# Family B (new): multi-orbit voltage lifts over groups.
#
# Base: a A-vertices and a B-vertices, d darts per vertex on each side, so the
# base is a d-regular bipartite multigraph. Dart p = (I[p], J[p], G[p]) with
# I[p] = p // d joins A-orbit I to B-orbit J with voltage G in the group.
# Lift vertices: A node i*N + x, B node a*N + j*N + y (x, y in G).
# Edge: (i, x) -- (j, x * g) for every dart (i, j, g).
# Simple iff all darts have distinct (i, j, g) triples.
# Left multiplication by G is an automorphism, so checking eccentricity from
# one representative per orbit (i, e) and (j, e) decides diameter <= D.
# ----------------------------------------------------------------------------

def _simple(I, J, G):
    return len(set(zip(I, J, G))) == len(I)


def _lift_bad(a, N, T, invs, I, J, G, D):
    """Count (source, vertex) pairs at distance > D, over the 2a orbit representatives."""
    aN = a * N
    V = 2 * aN
    adjA = [[] for _ in range(a)]
    adjB = [[] for _ in range(a)]
    for p in range(len(I)):
        i, j, g = I[p], J[p], G[p]
        adjA[i].append((j, g))
        adjB[j].append((i, invs[g]))
    sources = [i * N for i in range(a)] + [aN + j * N for j in range(a)]
    total = 0
    for s in sources:
        seen = bytearray(V)
        seen[s] = 1
        frontier = [s]
        reached = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < aN:
                    i, x = divmod(u, N)
                    row = T[x]
                    for j, g in adjA[i]:
                        v = aN + j * N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    j, y = divmod(u - aN, N)
                    row = T[y]
                    for i, gi in adjB[j]:
                        v = i * N + row[gi]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            reached += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += V - reached
    return total


def _lift_anneal(a, N, T, invs, d, D, rng, iters, deadline):
    """Anneal base-graph balancing (J swaps) and voltages (G rerolls) to zero bad pairs."""
    P = a * d
    I = [p // d for p in range(P)]
    J = [j for j in range(a) for _ in range(d)]
    rng.shuffle(J)
    G = [rng.randrange(N) for _ in range(P)]
    tries = 0
    while not _simple(I, J, G):
        tries += 1
        if tries > 300:
            return None
        G[rng.randrange(P)] = rng.randrange(N)

    cur = _lift_bad(a, N, T, invs, I, J, G, D)
    for it in range(iters):
        if cur == 0:
            break
        if time.monotonic() > deadline:
            break
        temp = max(0.05, 2.0 * (1.0 - it / iters))
        Jn = J[:]
        Gn = G[:]
        if rng.random() < 0.5:
            p, q = rng.sample(range(P), 2)
            Jn[p], Jn[q] = Jn[q], Jn[p]
        else:
            Gn[rng.randrange(P)] = rng.randrange(N)
        if not _simple(I, Jn, Gn):
            continue
        v = _lift_bad(a, N, T, invs, I, Jn, Gn, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            J, G, cur = Jn, Gn, v
    if cur == 0:
        return I, J, G
    return None


def _lift_edges(a, N, T, I, J, G):
    aN = a * N
    edges = []
    for p in range(len(I)):
        i, j, g = I[p], J[p], G[p]
        bu = i * N
        bv = aN + j * N
        for x in range(N):
            edges.append((bu + x, bv + T[x][g]))
    return 2 * aN, edges


def _lift_attempt(a, N, d, D, rng, deadline):
    """Try groups of order N for an a-base lift; return (n, edges) on success."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        res = _lift_anneal(a, N, T, invs, d, D, rng, LIFT_ITERS, deadline)
        if res is not None:
            I, J, G = res
            return _lift_edges(a, N, T, I, J, G)
    return None


def _lift_phase(d, D, rng, deadline, best, moore):
    """Search multi-orbit lifts whose order beats the current best, highest order first."""
    cands = []
    for a in LIFT_BASES:
        lo = max(2, best.n // (2 * a) + 1)
        hi = min(moore // (2 * a), moore // (4 * a) + TOP_SLACK)
        for N in range(lo, hi + 1):
            cands.append((a, N))
    budget = 0.4
    while time.monotonic() < deadline and cands:
        cands.sort(key=lambda t: -(2 * t[0] * t[1]))
        success = False
        for a, N in list(cands):
            now = time.monotonic()
            if now >= deadline:
                break
            att_deadline = min(deadline, now + budget)
            res = _lift_attempt(a, N, d, D, rng, att_deadline)
            if res is None:
                continue
            n, edges = res
            best.offer(n, edges, d, D)
            cands = [(b, M) for (b, M) in cands if 2 * b * M > best.n]
            success = True
            break
        if not success:
            budget *= 1.5


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = _Best()

    # Record-matching case: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        best.offer(n, e, d, D)
        return best.n, best.edges

    if D >= 2:
        best.offer(*lib.haar_graph(d, range(d)), d, D)
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            best.offer(pg[0], pg[1], d, D)
    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            best.offer(gq[0], gq[1], d, D)

    if d < 2 or D < 2:
        if not lib.is_valid(best.n, best.edges, d, D):
            return 1, []
        return best.n, best.edges

    moore = lib._moore_bound(d, D)

    # Phase 1: bi-Cayley baseline (keeps the known-good construction).
    phase1_end = min(deadline, start + 0.4 * time_limit)
    try:
        _bicayley_phase(d, D, rng, phase1_end, best, moore)
    except Exception:
        pass

    # Phase 2: multi-orbit voltage lifts, aiming above the current best.
    if d >= 3:
        try:
            _lift_phase(d, D, rng, deadline, best, moore)
        except Exception:
            pass

    if not lib.is_valid(best.n, best.edges, d, D):
        return 1, []
    return best.n, best.edges
