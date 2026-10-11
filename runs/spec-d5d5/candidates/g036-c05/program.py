import itertools
import math
import random
import time

import lib

ITERS = 800                   # annealing steps for single-orbit bi-Cayley tries
MAX_GROUPS_PER_ATTEMPT = 30   # groups tried per order N within one attempt
TOP_SLACK = 8                 # single-orbit search orders up to Nmax//2 + TOP_SLACK

MULTI_ITERS = 700             # annealing steps for two-class voltage lifts
MULTI_GROUPS = 25             # groups tried per order N in one multi-class attempt
MULTI_BUDGET0 = 0.3           # initial seconds per order N in the multi-class search
MULTI_SHARE = 0.6             # fraction of the working budget given to the multi-class search


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
# Group helpers shared by both searches.
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


def _consider(B, n, e, d, D):
    """Keep (n, e) in B = [best_n, best_edges] if it is strictly larger and valid."""
    if n > B[0] and lib.is_valid(n, e, d, D):
        B[0], B[1] = n, e


# ----------------------------------------------------------------------------
# NEW: two-class voltage lifts over semidirect groups.
#
# Base graph: two A-vertices A_0, A_1 and two B-vertices B_0, B_1. Between A_i and
# B_j there are C[i][j] darts, with C = [[a, d-a], [d-a, a]] so every base vertex
# has degree d. Each dart carries a distinct group voltage g, and the lift has
#   A_{i,x} -- B_{j, x*g}   for all x in G.
# This gives 4|G| vertices, is bipartite by construction, and is simple since the
# voltages on each class pair are distinct. Left multiplication by G is an
# automorphism, so the diameter only needs BFS from the four identity vertices.
# A single-orbit bi-Cayley search (the parent's method) cannot reach these
# orders with the same group size, so this covers a different part of the space.
# ----------------------------------------------------------------------------

def _multi_cost(N, T, invs, V, D):
    """Count (source, vertex) pairs not within distance D, for the four identity sources."""
    adj = [None] * (4 * N)
    for x in range(N):
        row = T[x]
        for i in (0, 1):
            lst = []
            for j in (0, 1):
                for g in V[i][j]:
                    lst.append(2 * N + j * N + row[g])
            adj[i * N + x] = lst
        for j in (0, 1):
            lst = []
            for i in (0, 1):
                for g in V[i][j]:
                    lst.append(i * N + row[invs[g]])
            adj[2 * N + j * N + x] = lst

    total = 0
    tot_n = 4 * N
    for src in (0, N, 2 * N, 3 * N):
        seen = bytearray(tot_n)
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += tot_n - count
    return total


def _multi_anneal(N, T, invs, C, D, rng, iters, deadline):
    """Anneal the voltages V[i][j] (distinct elements, |V[i][j]| = C[i][j]) to zero unreached pairs."""
    V = [[rng.sample(range(N), C[i][j]) for j in (0, 1)] for i in (0, 1)]
    cur = _multi_cost(N, T, invs, V, D)
    for it in range(iters):
        if cur == 0:
            break
        if time.monotonic() > deadline:
            break
        temp = max(0.05, 2.0 * (1.0 - it / iters))
        i = rng.randrange(2)
        j = rng.randrange(2)
        k = rng.randrange(C[i][j])
        g = rng.randrange(N)
        if g in V[i][j]:
            continue
        old = V[i][j][k]
        V[i][j][k] = g
        v = _multi_cost(N, T, invs, V, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            V[i][j][k] = old
    return V if cur == 0 else None


def _multi_attempt(N, d, D, rng, deadline):
    """Try groups of order N for a two-class lift of diameter <= D; return (T, V) or None."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MULTI_GROUPS]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        a = rng.randint(1, d // 2)
        C = [[a, d - a], [d - a, a]]
        V = _multi_anneal(N, T, invs, C, D, rng, MULTI_ITERS, deadline)
        if V is not None:
            return T, V
    return None


def _multi_edges(N, T, V):
    """Edges of the two-class lift: A_{i,x} = i*N+x, B_{j,y} = 2N+j*N+y."""
    edges = []
    for i in (0, 1):
        for j in (0, 1):
            for g in V[i][j]:
                for x in range(N):
                    edges.append((i * N + x, 2 * N + j * N + T[x][g]))
    return edges


def _multi_phase(d, D, rng, deadline, B):
    """Search two-class lifts with 4N vertices, largest N first, growing budgets."""
    Nmax = lib._moore_bound(d, D) // 4
    lo = max(d + 1, Nmax // 2)
    cands = set(range(lo, Nmax + 1))
    budget = MULTI_BUDGET0
    while time.monotonic() < deadline and cands:
        success = False
        for N in sorted(cands, reverse=True):
            now = time.monotonic()
            if now >= deadline:
                break
            att_deadline = min(deadline, now + budget)
            res = _multi_attempt(N, d, D, rng, att_deadline)
            if res is None:
                continue
            T, V = res
            _consider(B, 4 * N, _multi_edges(N, T, V), d, D)
            # Only larger orders can improve now.
            cands = {M for M in cands if M > N}
            success = True
            break
        if not success:
            budget *= 1.3


# ----------------------------------------------------------------------------
# Single-orbit bi-Cayley search (parent's method) over Z_m x| Z_k.
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


def _single_phase(d, D, rng, deadline, B):
    """Single-orbit bi-Cayley search with 2N vertices, largest N first, growing budgets."""
    Nmax = lib._moore_bound(d, D) // 2
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
            _consider(B, 2 * N, edges, d, D)
            cands = {M for M in cands if M > N}
            if N + 1 <= Nmax:
                cands.add(N + 1)
            success = True
            break
        if not success:
            budget *= 1.5


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    B = [1, []]  # [best_n, best_edges]

    # Record-matching case: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        _consider(B, n, e, d, D)
        if lib.is_valid(B[0], B[1], d, D):
            return B[0], B[1]
        return 1, []

    if D >= 2:
        _consider(B, *lib.haar_graph(d, range(d)), d, D)
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            _consider(B, pg[0], pg[1], d, D)
    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            _consider(B, gq[0], gq[1], d, D)

    if d >= 2 and D >= 2:
        now = time.monotonic()
        work = deadline - now
        multi_deadline = now + MULTI_SHARE * work
        _multi_phase(d, D, rng, multi_deadline, B)
        _single_phase(d, D, rng, deadline, B)

    if not lib.is_valid(B[0], B[1], d, D):
        return 1, []
    return B[0], B[1]
