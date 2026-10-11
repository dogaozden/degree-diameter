import itertools
import math
import random
import time

import lib

# Bi-Cayley phase (parent construction, kept as a safety net).
MAX_GROUPS_PER_ATTEMPT = 12
BC_ITERS = 600
BC_T_HOT = 1.5
BC_T_COLD = 0.15

# Local-search phase: unstructured bipartite d-regular graphs improved by edge switches.
LS_T_HOT = 3.0
LS_T_COLD = 0.2
BC_SHARE = 0.25        # fraction of the budget given to the bi-Cayley phase
TOTAL_SHARE = 0.8      # fraction of time_limit we are willing to use


# ----------------------------------------------------------------------------
# Baseline families (instant, always valid when they pass lib.is_valid).
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
# Phase A: bi-Cayley search over semidirect products (parent construction).
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


def _unreached(N, T, invs, S, D):
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


def _anneal_bc(N, T, invs, d, D, rng, iters, deadline):
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _unreached(N, T, invs, S, D)
    for it in range(iters):
        if cur == 0:
            return S
        if time.monotonic() > deadline:
            break
        temp = BC_T_HOT * (BC_T_COLD / BC_T_HOT) ** (it / iters)
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


def _attempt_bc(N, d, D, rng, deadline):
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        S = _anneal_bc(N, T, invs, d, D, rng, BC_ITERS, deadline)
        if S is not None:
            return T, S
    return None


def _bicayley_phase(d, D, rng, deadline, consider):
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
            res = _attempt_bc(N, d, D, rng, att_deadline)
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
            budget *= 2


# ----------------------------------------------------------------------------
# Phase B (bold): unstructured search. Bipartite near-regular graph on N+N
# vertices, improved by degree-preserving edge switches, minimizing the number
# of ordered vertex pairs at distance > D.
# ----------------------------------------------------------------------------

def _regular_start(N, d, rng):
    E = set()
    degA = [0] * N
    degB = [0] * N
    for _ in range(d):
        perm = list(range(N))
        rng.shuffle(perm)
        for a in range(N):
            b = perm[a]
            if (a, b) not in E and degA[a] < d and degB[b] < d:
                E.add((a, b))
                degA[a] += 1
                degB[b] += 1
    # Fill any leftover deficiency with random admissible pairs.
    tries = 20 * N * d
    for _ in range(tries):
        a = rng.randrange(N)
        b = rng.randrange(N)
        if degA[a] < d and degB[b] < d and (a, b) not in E:
            E.add((a, b))
            degA[a] += 1
            degB[b] += 1
    return list(E)


def _cost(N, E, D):
    """Number of ordered pairs (x, y) with dist > D, x, y in the 2N-vertex graph."""
    M = 2 * N
    adj = [[] for _ in range(M)]
    for a, b in E:
        adj[a].append(N + b)
        adj[N + b].append(a)
    reach = [1 << v for v in range(M)]
    for _ in range(D):
        new = []
        for v in range(M):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(M - r.bit_count() for r in reach)


def _anneal_graph(N, d, D, rng, deadline):
    E = _regular_start(N, d, rng)
    if not E:
        return None
    Es = set(E)
    cur = _cost(N, E, D)
    t0 = time.monotonic()
    span = max(1e-6, deadline - t0)
    m = len(E)
    while cur > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        if m < 2:
            break
        frac = (now - t0) / span
        temp = LS_T_HOT * (LS_T_COLD / LS_T_HOT) ** frac
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        n1 = (a1, b2)
        n2 = (a2, b1)
        if n1 in Es or n2 in Es:
            continue
        E[i] = n1
        E[j] = n2
        v = _cost(N, E, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
            Es.discard((a1, b1))
            Es.discard((a2, b2))
            Es.add(n1)
            Es.add(n2)
        else:
            E[i] = (a1, b1)
            E[j] = (a2, b2)
    if cur == 0:
        return E
    return None


def _local_phase(d, D, rng, deadline, consider, lo, hi):
    """Binary search on N: find the largest N for which annealing reaches diameter <= D."""
    while time.monotonic() < deadline and lo < hi:
        N = (lo + hi + 1) // 2
        now = time.monotonic()
        remaining = deadline - now
        att_deadline = min(deadline, now + max(4.0, remaining / 3.0))
        E = _anneal_graph(N, d, D, rng, att_deadline)
        if E is not None:
            edges = [(a, N + b) for a, b in E]
            consider(2 * N, edges)
            lo = N
        else:
            hi = N - 1


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = TOTAL_SHARE * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = [(1, [])]
    best_n = [1]

    def consider(n, e):
        if n > best_n[0] and lib.is_valid(n, e, d, D):
            best[0] = (n, e)
            best_n[0] = n

    # Record-matching case: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best[0]

    # Instant baselines.
    if D >= 2:
        consider(*lib.haar_graph(d, range(d)))
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D >= 4 and time.monotonic() - start < total:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if d < 3 or D < 2:
        if not lib.is_valid(best[0][0], best[0][1], d, D):
            return 1, []
        return best[0]

    # Phase A: bi-Cayley safety net.
    _bicayley_phase(d, D, rng, start + BC_SHARE * total, consider)

    # Phase B: unstructured local search with binary search on N.
    Nmax = lib._moore_bound(d, D) // 2
    if Nmax > d + 1:
        _local_phase(d, D, rng, start + total, consider, d + 1, Nmax)

    if not lib.is_valid(best[0][0], best[0][1], d, D):
        return 1, []
    return best[0]

