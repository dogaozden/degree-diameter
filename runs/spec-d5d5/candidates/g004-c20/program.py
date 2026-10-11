import itertools
import math
import random
import time

import lib

MAX_GROUPS_PER_ATTEMPT = 30   # groups tried per order N within one bi-Cayley attempt
ITERS = 800                   # annealing steps per bi-Cayley (group, set) try
TOP_SLACK = 8                 # bi-Cayley orders searched up to Nmax//2 + TOP_SLACK

LIFT_GROUPS = 12              # groups tried per order N in the 2-by-2 lift search
LIFT_ITERS = 500              # annealing steps per lift (group, darts) try
LIFT_BUDGET0 = 0.6            # initial seconds per order N in the lift search


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
# Groups: semidirect products Z_m x|_r Z_k of order N.
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
# Family A: bi-Cayley graphs (one base vertex per side), as in the parent.
# Vertices A_x and B_y, edge A_x -- B_{x s} for s in S, |S| = d.
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


def _bicayley_search(d, D, rng, deadline, consider, best_n):
    """Search bi-Cayley orders N (graph order 2N), only above the current best."""
    if d < 2 or D < 2:
        return
    Nmax = lib._moore_bound(d, D) // 2
    top = min(Nmax, Nmax // 2 + TOP_SLACK)
    lo = max(d + 1, best_n() // 2 + 1)
    cands = set(range(lo, top + 1))

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
# Family B (new): 2-by-2 group lifts. Vertices A_i^x (i in {0,1}) and B_j^y
# (j in {0,1}), x, y in G, |G| = N, so 4N vertices. Dart sets S[i][j] of sizes
#   [[a, d-a], [d-a, a]]  give every vertex degree d.
# Edge A_i^x -- B_j^{x g} for g in S[i][j]. Left multiplication is an
# automorphism, so the four representatives A_0^e, A_1^e, B_0^e, B_1^e
# determine the diameter.
# ----------------------------------------------------------------------------

def _lift_cost(N, T, invs, S, D):
    """Count (representative, vertex) pairs not within distance D over the four orbit representatives."""
    n = 4 * N
    outA = [[(j, S[i][j]) for j in (0, 1)] for i in (0, 1)]
    inB = [[(i, [invs[g] for g in S[i][j]]) for i in (0, 1)] for j in (0, 1)]
    total = 0
    for src in (0, N, 2 * N, 3 * N):
        seen = bytearray(n)
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < 2 * N:
                    i = u // N
                    row = T[u - i * N]
                    for j, gs in outA[i]:
                        base = 2 * N + j * N
                        for g in gs:
                            v = base + row[g]
                            if not seen[v]:
                                seen[v] = 1
                                nxt.append(v)
                else:
                    rel = u - 2 * N
                    j = rel // N
                    row = T[rel - j * N]
                    for i, hs in inB[j]:
                        base = i * N
                        for h in hs:
                            v = base + row[h]
                            if not seen[v]:
                                seen[v] = 1
                                nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += n - count
    return total


def _lift_anneal(N, T, invs, a, d, D, rng, iters, deadline):
    """Anneal dart sets of sizes [[a, d-a], [d-a, a]] to zero unreached pairs."""
    sizes = [[a, d - a], [d - a, a]]
    S = [[rng.sample(range(N), sizes[i][j]) for j in (0, 1)] for i in (0, 1)]
    cur = _lift_cost(N, T, invs, S, D)
    for it in range(iters):
        if cur == 0:
            return S
        if time.monotonic() > deadline:
            break
        temp = max(0.05, 2.0 * (1.0 - it / iters))
        i = rng.randrange(2)
        j = rng.randrange(2)
        cell = S[i][j]
        p = rng.randrange(len(cell))
        c = rng.randrange(N)
        if c in cell:
            continue
        S2 = [[list(S[x][y]) for y in (0, 1)] for x in (0, 1)]
        S2[i][j][p] = c
        v = _lift_cost(N, T, invs, S2, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            S, cur = S2, v
    return S if cur == 0 else None


def _lift_attempt(N, d, D, rng, deadline):
    """Try groups of order N for a 2-by-2 lift with diameter <= D."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:LIFT_GROUPS]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        a = rng.randrange(1, d)
        S = _lift_anneal(N, T, invs, a, d, D, rng, LIFT_ITERS, deadline)
        if S is not None:
            return T, S
    return None


def _lift_edges(N, T, S):
    """Edge list of the 2-by-2 lift: A_i^x = i*N + x, B_j^y = 2N + j*N + y."""
    edges = []
    for i in (0, 1):
        for j in (0, 1):
            for x in range(N):
                row = T[x]
                for g in S[i][j]:
                    edges.append((i * N + x, 2 * N + j * N + row[g]))
    return edges


def _lift_search(d, D, rng, deadline, consider, best_n):
    """Sweep N upward (graph order 4N, only above the current best) with growing budgets."""
    if d < 2 or D < 2:
        return
    Nmax = lib._moore_bound(d, D) // 4
    budget = LIFT_BUDGET0
    while time.monotonic() < deadline:
        Nlo = max(d, best_n() // 4 + 1)
        if Nlo > Nmax:
            return
        N = Nlo
        while N <= Nmax and time.monotonic() < deadline:
            res = _lift_attempt(N, d, D, rng, min(deadline, time.monotonic() + budget))
            if res is not None:
                T, S = res
                consider(4 * N, _lift_edges(N, T, S))
            N += 1
        budget *= 1.5


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = [(1, [])]

    def best_n():
        return best[0][0]

    def consider(n, e):
        if n > best[0][0] and lib.is_valid(n, e, d, D):
            best[0] = (n, e)

    # Record-matching case: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best[0]

    if D >= 2:
        consider(*lib.haar_graph(d, range(d)))
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D >= 4 and time.monotonic() < start + 0.2 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if d < 2 or D < 2:
        return best[0]

    # Phase A: classic bi-Cayley search (secures the parent's level).
    _bicayley_search(d, D, rng, start + 0.35 * time_limit, consider, best_n)
    # Phase B: new 2-by-2 group-lift search, aiming above the current best.
    _lift_search(d, D, rng, start + 0.72 * time_limit, consider, best_n)
    # Phase C: resume bi-Cayley with whatever time is left.
    _bicayley_search(d, D, rng, start + 0.85 * time_limit, consider, best_n)

    n, e = best[0]
    if not lib.is_valid(n, e, d, D):
        return 1, []
    return n, e
