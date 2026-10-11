import itertools
import math
import random
import time

import lib

MAX_GROUPS_PER_ATTEMPT = 30   # groups tried per order within one attempt
ITERS = 800                   # annealing steps per bi-Cayley (group, set) try
TOP_SLACK = 8                 # bi-Cayley orders up to Nmax//2 + TOP_SLACK
LIFT_ITERS = 700              # annealing steps per two-orbit lift try
BICAYLEY_SHARE = 0.3          # fraction of the search time given to bi-Cayley


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
# Shared group enumeration: all semidirect parameters (m, k, r), m*k = N.
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
# Stage A: bi-Cayley search over groups of order N (2N vertices).
# A_x -- B_{x s} for s in S, |S| = d, identity WLOG in S.
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


def _bicayley_search(d, D, rng, deadline, consider):
    """Search bi-Cayley graphs of increasing order; report each success via consider()."""
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
            consider(2 * N, edges)
            cands = {M for M in cands if M > N}
            if N + 1 <= Nmax:
                cands.add(N + 1)
            success = True
            break
        if not success:
            budget *= 1.5


# ----------------------------------------------------------------------------
# Stage B (new): two-orbit block voltage lift over a finite group.
#
# Base graph: A_0, A_1 on one side, B_0, B_1 on the other. The dart matrix is
#     M = [[a, d-a], [d-a, a]]   (row and column sums d, so every base vertex
# has degree d). Each block (i, j) carries M[i][j] distinct voltages g, giving
# the edges A_i,x -- B_j,(x*g). The lift has 4N vertices. Left multiplication by
# any group element is an automorphism that acts transitively on each of the
# four orbits, so the diameter is decided by BFS from A_0, A_1, B_0, B_1 at the
# identity. The order 4N > 336 is needed to beat the record for d=5, D=5.
# ----------------------------------------------------------------------------

def _lift_tables(N, mul, inv):
    """Multiplication table T[x][g] = x*g and the inverse list for a group on 0..N-1."""
    T = [[mul(x, g) for g in range(N)] for x in range(N)]
    invs = [inv(g) for g in range(N)]
    return T, invs


def _lift_cost(N, T, invs, vol, D):
    """Total unreached (source, vertex) pairs over the four orbit representatives."""
    V = 4 * N
    adj = [[] for _ in range(V)]
    for i in (0, 1):
        for x in range(N):
            lst = adj[i * N + x]
            row = T[x]
            for j in (0, 1):
                base = 2 * N + j * N
                for g in vol[i][j]:
                    lst.append(base + row[g])
    for j in (0, 1):
        for y in range(N):
            lst = adj[2 * N + j * N + y]
            row = T[y]
            for i in (0, 1):
                for g in vol[i][j]:
                    lst.append(i * N + row[invs[g]])
    total = 0
    for s in (0, N, 2 * N, 3 * N):
        seen = bytearray(V)
        seen[s] = 1
        frontier = [s]
        count = 1
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
        total += V - count
    return total


def _lift_anneal(N, T, invs, d, a, D, rng, iters, deadline):
    """Anneal the voltages of the four blocks to zero unreached pairs; return vol or None."""
    M = [[a, d - a], [d - a, a]]
    vol = [[rng.sample(range(N), M[i][j]) for j in range(2)] for i in range(2)]
    cur = _lift_cost(N, T, invs, vol, D)
    for it in range(iters):
        if cur == 0:
            break
        if time.monotonic() > deadline:
            break
        temp = max(0.05, 3.0 * (1.0 - it / iters))
        i = rng.randrange(2)
        j = rng.randrange(2)
        blk = vol[i][j]
        t = rng.randrange(len(blk))
        c = rng.randrange(N)
        if c in blk:
            continue
        old = blk[t]
        blk[t] = c
        v = _lift_cost(N, T, invs, vol, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            blk[t] = old
    return vol if cur == 0 else None


def _lift_edges(N, T, vol):
    """Edge list of the two-orbit lift: A_i,x = i*N+x, B_j,y = 2N+j*N+y."""
    edges = []
    for i in (0, 1):
        for x in range(N):
            u = i * N + x
            for j in (0, 1):
                base = 2 * N + j * N
                for g in vol[i][j]:
                    edges.append((u, base + T[x][g]))
    return 4 * N, edges


def _lift_search(d, D, rng, deadline, best_n, consider):
    """Search two-orbit lifts of increasing order 4N > best_n."""
    if d < 2 or D < 2:
        return
    Nmax = lib._moore_bound(d, D) // 4
    t = best_n // 4 + 1
    budget = 0.6
    avals = list(range(1, d // 2 + 1))   # a and d-a give isomorphic lifts
    while time.monotonic() < deadline and t <= Nmax:
        att_deadline = min(deadline, time.monotonic() + budget)
        groups = _groups(t)
        rng.shuffle(groups)
        found = None
        for m, k, r in groups[:MAX_GROUPS_PER_ATTEMPT]:
            if time.monotonic() > att_deadline:
                break
            order, mul, inv = lib.semidirect_group(m, k, r)
            T, invs = _lift_tables(t, mul, inv)
            a_list = avals[:]
            rng.shuffle(a_list)
            for a in a_list:
                if time.monotonic() > att_deadline:
                    break
                vol = _lift_anneal(t, T, invs, d, a, D, rng, LIFT_ITERS, att_deadline)
                if vol is not None:
                    found = (vol, T)
                    break
            if found is not None:
                break
        if found is not None:
            n, e = _lift_edges(t, found[1], found[0])
            consider(n, e)
            t += 1
            budget = 0.6
        else:
            budget *= 1.5


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = (1, [])

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
            return True
        return False

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

    # Stage A: bi-Cayley search gets a fixed share of the time.
    bi_deadline = start + BICAYLEY_SHARE * 0.85 * time_limit
    _bicayley_search(d, D, rng, bi_deadline, consider)

    # Stage B: two-orbit block voltage lifts over semidirect products, aiming above best.
    _lift_search(d, D, rng, deadline, best[0], consider)

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
