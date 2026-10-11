"""Multi-orbit voltage lifts, searched with left-invariant multi-source diameter checks.

New in this version: instead of only 2-orbit bi-Cayley graphs (2N vertices, one dart per
connection), each search uses k A-orbits and k B-orbits (2kN vertices). The base graph is
a k x k multigraph with row and column sums d, built as a sum of d random permutation
matrices, so it is d-regular by construction. Each dart (i, j) carries a voltage g in a
finite group G of order N, and parallel darts get distinct voltages. Left multiplication
by G is an automorphism of the lift, so the diameter check needs only 2k BFS sources (one
identity vertex per orbit). Annealing over voltages with random restarts over bases and
groups targets orders above the current best. The parent's bi-Cayley search is kept as a
fallback for the remaining time.
"""
import itertools
import math
import random
import time

import lib

ITERS = 500                 # annealing steps per restart
TRACK_KS = (2, 3, 4)        # number of A-orbits (and B-orbits) per lift track
WINDOW = 3                  # try group orders N in [N_track, N_track + WINDOW)
TOP_SLACK = 8               # bi-Cayley fallback: orders up to Nmax//2 + TOP_SLACK


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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Groups: semidirect products Z_m x| Z_k of order N (r = 1 gives direct products).
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
# NEW: k-orbit voltage lifts with permutation-sum base graphs.
#
# Vertices: A_i x -> i*N + x (i < k), B_j y -> k*N + j*N + y.
# Base dart t = (i, j) with voltage g_t: edges (A_i x, B_j (x * g_t)) for all x.
# Left multiplication by G is an automorphism, so the BFS sources are the identity
# vertex of each orbit, 2k sources in total.
# ----------------------------------------------------------------------------

def _base_darts(k, d, rng):
    """Base multigraph: sum of d random permutation matrices, so every orbit has degree d."""
    pairs = []
    for _ in range(d):
        perm = list(range(k))
        rng.shuffle(perm)
        pairs.extend((i, perm[i]) for i in range(k))
    return pairs


def _connected_base(k, pairs):
    """True if the base multigraph on 2k orbit-vertices is connected."""
    parent = list(range(2 * k))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    for i, j in pairs:
        parent[find(i)] = find(k + j)
    return len({find(x) for x in range(2 * k)}) == 1


def _random_volt(pairs, same, N, rng):
    """Random voltages with parallel darts (same base pair) receiving distinct values."""
    volt = [None] * len(pairs)
    for t in range(len(pairs)):
        while True:
            g = rng.randrange(N)
            if all(volt[s] != g for s in same[t] if volt[s] is not None):
                break
        volt[t] = g
    return volt


def _lift_edges(k, N, T, pairs, volt):
    """Edge list of the lift for the given voltages."""
    out = []
    for t, (i, j) in enumerate(pairs):
        g = volt[t]
        base_a = i * N
        base_b = k * N + j * N
        for x in range(N):
            out.append((base_a + x, base_b + T[x][g]))
    return out


def _unreached_multi(V, adj, sources, D):
    """Count (source, vertex) pairs at distance > D, summed over the given sources."""
    total = 0
    for s in sources:
        seen_flag = bytearray(V)
        seen_flag[s] = 1
        seen = 1
        frontier = [s]
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen_flag[v]:
                        seen_flag[v] = 1
                        nxt.append(v)
            if not nxt:
                break
            seen += len(nxt)
            frontier = nxt
        total += V - seen
    return total


def _eval(k, N, D, T, pairs, volt, sources):
    V = 2 * k * N
    adj = [[] for _ in range(V)]
    for a, b in _lift_edges(k, N, T, pairs, volt):
        adj[a].append(b)
        adj[b].append(a)
    return _unreached_multi(V, adj, sources, D)


def _attempt(k, N, d, D, groups, rng, deadline):
    """Random restarts (base, group, voltages) with annealing until a lift of diameter <= D is found."""
    sources = [i * N for i in range(k)] + [k * N + j * N for j in range(k)]
    while time.monotonic() < deadline:
        pairs = _base_darts(k, d, rng)
        if not _connected_base(k, pairs):
            continue
        m, kk, r = groups[rng.randrange(len(groups))]
        _, mul, inv = lib.semidirect_group(m, kk, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        same = [[s for s in range(len(pairs)) if s != t and pairs[s] == pairs[t]]
                for t in range(len(pairs))]
        volt = _random_volt(pairs, same, N, rng)
        cur = _eval(k, N, D, T, pairs, volt, sources)
        for it in range(ITERS):
            if cur == 0:
                break
            if time.monotonic() > deadline:
                return None
            t = rng.randrange(len(pairs))
            g = rng.randrange(N)
            if any(volt[s] == g for s in same[t]):
                continue
            old = volt[t]
            volt[t] = g
            v = _eval(k, N, D, T, pairs, volt, sources)
            temp = max(0.2, 2.0 * (1.0 - it / ITERS))
            if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
                cur = v
            else:
                volt[t] = old
        if cur == 0:
            return 2 * k * N, _lift_edges(k, N, T, pairs, volt)
    return None


def _lift_search(d, D, rng, deadline, consider, state):
    """Round-robin over k-orbit tracks; each track keeps pushing its order above the best so far."""
    tracks = {k: {'N': 0, 'budget': 2.0} for k in TRACK_KS}
    cache = {}
    while time.monotonic() < deadline:
        for k in TRACK_KS:
            now = time.monotonic()
            if now >= deadline:
                break
            tr = tracks[k]
            tr['N'] = max(tr['N'], state['n'] // (2 * k) + 1, d + 1)
            N = tr['N'] + rng.randrange(WINDOW)
            if N not in cache:
                cache[N] = _groups(N)
            res = _attempt(k, N, d, D, cache[N], rng, min(deadline, now + tr['budget']))
            if res is None:
                tr['budget'] *= 1.3
            else:
                consider(*res)
                tr['budget'] = 2.0


# ----------------------------------------------------------------------------
# Parent fallback: bi-Cayley search over Z_m x| Z_k (2N vertices, one dart per connection).
# ----------------------------------------------------------------------------

def _bc_unreached(N, T, invs, S, D):
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


def _bc_anneal(N, T, invs, d, D, rng, iters, deadline):
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _bc_unreached(N, T, invs, S, D)
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
        v = _bc_unreached(N, T, invs, S2, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            S, cur = S2, v
    return S if cur == 0 else None


def _bc_attempt(N, d, D, rng, deadline):
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:30]:
        if time.monotonic() > deadline:
            return None
        _, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        S = _bc_anneal(N, T, invs, d, D, rng, 800, deadline)
        if S is not None:
            return T, S
    return None


def _bicayley_search(d, D, rng, deadline, consider):
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
            res = _bc_attempt(N, d, D, rng, min(deadline, now + budget))
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
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    state = {'n': 1, 'e': []}

    def consider(n, e):
        if n > state['n'] and lib.is_valid(n, e, d, D):
            state['n'] = n
            state['e'] = e

    # Record-matching case: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return state['n'], state['e']

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
        return state['n'], state['e']

    lift_deadline = start + 0.5 * time_limit
    end = start + 0.8 * time_limit

    # New family: k-orbit permutation-base voltage lifts.
    _lift_search(d, D, rng, lift_deadline, consider, state)

    # Parent fallback with whatever time remains.
    _bicayley_search(d, D, rng, end, consider)

    if not lib.is_valid(state['n'], state['e'], d, D):
        return 1, []
    return state['n'], state['e']
