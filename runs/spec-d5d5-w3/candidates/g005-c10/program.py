import itertools
import math
import random
import time

import lib

ITERS = 500              # annealing steps per restart
RESTARTS = 3             # fresh random base graphs and voltages per group
DEADLINE_FRAC = 0.82     # fraction of time_limit we are willing to use
MAX_SIDES = 4            # largest number of vertex orbits per side tried
HEAD = 12                # choose among this many smallest feasible sizes


# ----------------------------------------------------------------------------
# Baseline families kept from the parent (small, fast, always checked).
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
# NEW IDEA: multi-orbit voltage search.
#
# The parent only searches bi-Cayley graphs: one orbit of A-vertices and one
# orbit of B-vertices under a group G of order N (2N vertices). Here we use s
# orbits per side. The base graph is a d-regular bipartite multigraph on s+s
# vertices, given as a list of s*d darts (i, j) (each i and each j occurs d
# times, built as a sum of d random permutation matrices). Every dart carries a
# voltage g in G, giving edges A_{i,x} -- B_{j, x*g} for all x in G. Darts with
# the same (i, j) need distinct voltages, so there are no duplicate edges.
#
# Result: a graph with 2*s*N vertices, degree d, bipartite by construction.
# Left multiplication by G is an automorphism, so the eccentricity check only
# needs BFS from A_{i,e} and B_{j,e} for each orbit index i, j (2s sources).
# Annealing over the voltages minimizes the number of pairs at distance > D.
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


def _random_base(s, d, rng):
    """Random d-regular bipartite multigraph on s+s vertices as a list of s*d darts (i, j)."""
    darts = []
    for _ in range(d):
        p = list(range(s))
        rng.shuffle(p)
        for i in range(s):
            darts.append((i, p[i]))
    return darts


def _unreached(N, s, D, T, darts, volts):
    """Count (source, vertex) pairs at distance > D, over the 2s orbit representatives."""
    V = 2 * s * N
    base_b = s * N
    adj = [[] for _ in range(V)]
    for t, (i, j) in enumerate(darts):
        g = volts[t]
        ai = i * N
        bj = base_b + j * N
        for x in range(N):
            a = ai + x
            b = bj + T[x][g]
            adj[a].append(b)
            adj[b].append(a)
    sources = [i * N for i in range(s)] + [base_b + j * N for j in range(s)]
    total = 0
    for src in sources:
        seen = bytearray(V)
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
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += V - count
    return total


def _anneal(N, s, D, T, darts, rng, iters, deadline):
    """Simulated annealing over voltages; returns the voltage list or None."""
    L = len(darts)
    used = {}
    volts = []
    for ij in darts:
        st = used.setdefault(ij, set())
        g = rng.randrange(N)
        while g in st:
            g = rng.randrange(N)
        st.add(g)
        volts.append(g)
    cur = _unreached(N, s, D, T, darts, volts)
    for it in range(iters):
        if cur == 0:
            return volts
        if time.monotonic() > deadline:
            break
        temp = max(0.05, 1.5 * (1.0 - it / iters))
        t = rng.randrange(L)
        st = used[darts[t]]
        g = rng.randrange(N)
        if g in st:
            continue
        old = volts[t]
        volts[t] = g
        v = _unreached(N, s, D, T, darts, volts)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            st.discard(old)
            st.add(g)
            cur = v
        else:
            volts[t] = old
    return volts if cur == 0 else None


def _attempt(s, N, d, D, rng, deadline):
    """Pick a random group of order N, then try random base graphs with annealed voltages."""
    groups = _groups(N)
    if not groups:
        return None
    m, k, r = rng.choice(groups)
    _, mul, _ = lib.semidirect_group(m, k, r)
    T = [[mul(x, g) for g in range(N)] for x in range(N)]
    for _ in range(RESTARTS):
        if time.monotonic() > deadline:
            return None
        darts = _random_base(s, d, rng)
        volts = _anneal(N, s, D, T, darts, rng, ITERS, deadline)
        if volts is not None:
            return darts, volts, T
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + DEADLINE_FRAC * time_limit
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

    # Record-matching calibration: incidence graph of PG(2, d-1).
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

    bound = lib._moore_bound(d, D)
    cands = []
    for s in range(1, MAX_SIDES + 1):
        for N in range(d + 1, bound // (2 * s) + 1):
            tot = 2 * s * N
            if tot <= bound:
                cands.append((tot, s, N))
    cands.sort()

    budget = 3.0
    while time.monotonic() < deadline:
        pool = [c for c in cands if c[0] > best_n]
        if not pool:
            break
        head = pool[:HEAD]
        tot, s, N = head[rng.randrange(len(head))]
        now = time.monotonic()
        if now >= deadline:
            break
        att_deadline = min(deadline, now + budget)
        res = _attempt(s, N, d, D, rng, att_deadline)
        if res is None:
            budget = min(budget * 1.2, 15.0)
            continue
        darts, volts, T = res
        B0 = s * N
        edges = []
        for t, (i, j) in enumerate(darts):
            g = volts[t]
            for x in range(N):
                edges.append((i * N + x, B0 + j * N + T[x][g]))
        consider(2 * s * N, edges)

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
