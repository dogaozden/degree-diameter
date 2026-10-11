import itertools
import math
import random
import time

import lib

MAX_GROUPS_PER_ATTEMPT = 30   # groups tried per order N within one bi-Cayley attempt
ITERS = 800                   # annealing steps per (group, connection set) try
TOP_SLACK = 8                 # bi-Cayley orders searched up to Nmax//2 + TOP_SLACK
BICAYLEY_FRAC = 0.30          # share of the time budget given to bi-Cayley search
SWAP_SLICE = 9.0              # seconds per random restart of the swap search
SAFETY = 0.80                 # use this fraction of time_limit in total


# ----------------------------------------------------------------------------
# Baseline families (fast, validated before use).
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
# Bi-Cayley search over semidirect products Z_m x| Z_k of order N (earlier family).
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


# ----------------------------------------------------------------------------
# New family: d-regular bipartite graphs found by edge-swap annealing.
#
# No group structure is imposed. We start from a random d-regular bipartite
# graph on N + N vertices (A = 0..N-1, B = N..2N-1) and repeatedly swap
# endpoints of two edges, which keeps the graph d-regular and bipartite.
# The cost is the number of ordered (vertex, vertex) pairs at distance > D.
# ----------------------------------------------------------------------------

def _bad_pairs_bip(N, A, Bl, D):
    """A[a] is a set of B-indices; Bl[b] is a list of A-indices. Return the count of unreached ordered pairs."""
    n = 2 * N
    nbr = [None] * n
    for a in range(N):
        nbr[a] = [N + b for b in A[a]]
    for b in range(N):
        nbr[N + b] = Bl[b]
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        changed = False
        for v in range(n):
            r = reach[v]
            for u in nbr[v]:
                r |= reach[u]
            new[v] = r
            if r != reach[v]:
                changed = True
        reach = new
        if not changed:
            break
    return sum(n - r.bit_count() for r in reach)


def _random_regular(N, d, rng):
    """Return list of sets A with each a having d distinct neighbours and each b having degree d, or None."""
    A = [set() for _ in range(N)]
    for _ in range(d):
        ok = False
        for _try in range(300):
            perm = list(range(N))
            rng.shuffle(perm)
            if all(perm[a] not in A[a] for a in range(N)):
                ok = True
                break
        if not ok:
            return None
        for a in range(N):
            A[a].add(perm[a])
    return A


def _swap_search(N, d, D, rng, deadline):
    """Anneal edge swaps from a random d-regular bipartite graph until diameter <= D. Return A or None."""
    A = _random_regular(N, d, rng)
    if A is None:
        return None
    E = [(a, b) for a in range(N) for b in A[a]]

    def evaluate():
        Bl = [[] for _ in range(N)]
        for a in range(N):
            for b in A[a]:
                Bl[b].append(a)
        return _bad_pairs_bip(N, A, Bl, D)

    cur = evaluate()
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    m_edges = len(E)
    while cur > 0 and time.monotonic() < deadline:
        frac = (time.monotonic() - t0) / span
        temp = 0.3 + 4.0 * (1.0 - frac)
        i = rng.randrange(m_edges)
        j = rng.randrange(m_edges)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        if b2 in A[a1] or b1 in A[a2]:
            continue
        A[a1].discard(b1)
        A[a2].discard(b2)
        A[a1].add(b2)
        A[a2].add(b1)
        new = evaluate()
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            cur = new
            E[i] = (a1, b2)
            E[j] = (a2, b1)
        else:
            A[a1].discard(b2)
            A[a2].discard(b1)
            A[a1].add(b1)
            A[a2].add(b2)
    return A if cur == 0 else None


def _regular_edges(N, A):
    return [(a, N + b) for a in range(N) for b in A[a]]


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + SAFETY * time_limit
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

    Nmax = lib._moore_bound(d, D) // 2   # bipartite regular graph with 2N vertices

    # Phase 1: bi-Cayley search (earlier family), limited share of the time.
    bi_deadline = start + BICAYLEY_FRAC * SAFETY * time_limit
    top = min(Nmax, Nmax // 2 + TOP_SLACK)
    cands = set(range(d + 1, top + 1))
    budget = 0.4
    while time.monotonic() < bi_deadline and cands:
        success = False
        for N in sorted(cands, reverse=True):
            now = time.monotonic()
            if now >= bi_deadline:
                break
            att_deadline = min(bi_deadline, now + budget)
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

    # Phase 2: edge-swap annealing on random regular bipartite graphs,
    # aiming one step above the best order found so far.
    N = max(d + 1, best_n // 2 + 1)
    while time.monotonic() < deadline and N <= Nmax:
        now = time.monotonic()
        slice_end = min(deadline, now + SWAP_SLICE)
        A = _swap_search(N, d, D, rng, slice_end)
        if A is not None:
            edges = _regular_edges(N, A)
            consider(2 * N, edges)
            if best_n >= 2 * N:
                N = best_n // 2 + 1
            else:
                N += 1
        # On failure keep the same N and restart with fresh randomness.

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
