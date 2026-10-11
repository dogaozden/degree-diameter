import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Structured baselines: projective planes (D = 3) and generalized quadrangles
# (diameter 4, which also has diameter <= 5).
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
# Bi-Cayley lifts over Z_m x|_r Z_k (one base vertex per side), then
# repair by degree-preserving edge switches (simulated annealing on the
# number of vertex pairs at distance > D).
# ----------------------------------------------------------------------------

MAX_GROUPS = 6        # groups tried per order N
CLIMB_ITERS = 800     # hill-climb steps per group
STALL_LIMIT = 250     # re-randomize after this many non-improving steps
N_WINDOW = 4          # candidate orders just above the current lower bound
REPAIR_PROB = 0.5     # chance an attempt includes an edge-switch repair phase
_TABLE_CACHE = {}


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


def _tables(m, k, r):
    """Cached (order, mul, T, invs) for Z_m x|_r Z_k, where T[x][g] = x*g and invs[g] = g^-1."""
    key = (m, k, r)
    hit = _TABLE_CACHE.get(key)
    if hit is not None:
        return hit
    order, mul, inv = lib.semidirect_group(m, k, r)
    T = [[mul(x, g) for g in range(order)] for x in range(order)]
    invs = [inv(g) for g in range(order)]
    val = (order, mul, T, invs)
    if len(_TABLE_CACHE) >= 48:
        _TABLE_CACHE.clear()
    _TABLE_CACHE[key] = val
    return val


def _unreached(N, T, invs, S, D):
    """Pairs (source, target) not within distance D, from A_0 and B_0 (vertex-transitive per side)."""
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


def _climb(N, T, invs, d, D, rng, iters, deadline):
    """Hill-climb a connection set S (identity fixed as one dart) to minimize unreached pairs.

    Returns (best S seen, its cost). Cost 0 means a valid bi-Cayley lift.
    """
    def fresh():
        S = [0] + rng.sample(range(1, N), d - 1)
        return S, _unreached(N, T, invs, S, D)

    S, cur = fresh()
    bestS, bestc = list(S), cur
    stall = 0
    for _ in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _unreached(N, T, invs, S2, D)
        stall = 0 if v < cur else stall + 1
        if v <= cur:
            S, cur = S2, v
        if cur < bestc:
            bestS, bestc = list(S), cur
        if stall > STALL_LIMIT:
            S, cur = fresh()
            stall = 0
            if cur < bestc:
                bestS, bestc = list(S), cur
    return bestS, bestc


def _balls_radius(n, adj, r):
    """Bitmask per vertex of all vertices within distance r."""
    ball = [1 << v for v in range(n)]
    for _ in range(r):
        new = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new.append(x)
        ball = new
    return ball


def _bad_count(n, adj, D):
    """Number of unordered vertex pairs at distance > D (unreachable pairs included)."""
    balls = _balls_radius(n, adj, D)
    return sum(n - b.bit_count() for b in balls) // 2


def _repair(N, E, D, rng, deadline):
    """Degree-preserving edge-switch annealing on a bipartite graph with parts [0,N) and [N,2N).

    E is a list of [a, b] pairs (a in A, b in B). Returns (n, edges) if the diameter becomes <= D.
    """
    n = 2 * N
    adj = [[] for _ in range(n)]
    eset = set()
    for a, b in E:
        adj[a].append(b)
        adj[b].append(a)
        eset.add((a, b))
    cost = _bad_count(n, adj, D)
    m_edges = len(E)
    it = 0
    T0 = 1.0
    while cost > 0 and time.monotonic() < deadline:
        it += 1
        T = max(0.05, T0 * (1.0 - min(1.0, it / 20000.0)))
        i = rng.randrange(m_edges)
        j = rng.randrange(m_edges)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        if (a1, b2) in eset or (a2, b1) in eset:
            continue
        adj[a1].remove(b1)
        adj[b1].remove(a1)
        adj[a2].remove(b2)
        adj[b2].remove(a2)
        adj[a1].append(b2)
        adj[b2].append(a1)
        adj[a2].append(b1)
        adj[b1].append(a2)
        c2 = _bad_count(n, adj, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            eset.discard((a1, b1))
            eset.discard((a2, b2))
            eset.add((a1, b2))
            eset.add((a2, b1))
            E[i] = [a1, b2]
            E[j] = [a2, b1]
            cost = c2
        else:
            adj[a1].remove(b2)
            adj[b2].remove(a1)
            adj[a2].remove(b1)
            adj[b1].remove(a2)
            adj[a1].append(b1)
            adj[b1].append(a1)
            adj[a2].append(b2)
            adj[b2].append(a2)
    if cost == 0:
        return n, [(a, b) for a, b in E]
    return None


def _attempt(N, d, D, rng, climb_deadline, repair_deadline):
    """Try several groups of order N; return (n, edges) for a valid graph, else None.

    If no exact bi-Cayley lift is found and repair_deadline is set, edge-switch
    repair is run from the best near-miss.
    """
    groups = _groups(N)
    if not groups:
        return None
    rng.shuffle(groups)
    best_c = None
    best_S = None
    best_T = None
    for m, k2, r in groups[:MAX_GROUPS]:
        if time.monotonic() > climb_deadline:
            break
        _, _, T, invs = _tables(m, k2, r)
        S, c = _climb(N, T, invs, d, D, rng, CLIMB_ITERS, climb_deadline)
        if c == 0:
            edges = [(x, N + T[x][g]) for x in range(N) for g in S]
            return 2 * N, edges
        if best_c is None or c < best_c:
            best_c, best_S, best_T = c, S, T
    if repair_deadline is not None and best_S is not None and time.monotonic() < repair_deadline:
        E = [[x, N + best_T[x][g]] for x in range(N) for g in best_S]
        return _repair(N, E, D, rng, repair_deadline)
    return None


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Structured baselines.
    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Main search: bi-Cayley lifts just above the current record, with
    # edge-switch repair of near-miss lifts as the bolder second phase.
    while best[0] < moore and time.monotonic() < deadline:
        n_best = best[0]
        lo = max(d, n_best // 2 + 1)
        if lo > moore // 2:
            break
        N = lo + rng.randrange(N_WINDOW)
        now = time.monotonic()
        remaining = deadline - now
        if remaining <= 0:
            break
        if rng.random() < REPAIR_PROB:
            climb_deadline = now + 0.5 * remaining
            repair_deadline = now + remaining
        else:
            climb_deadline = deadline
            repair_deadline = None
        res = _attempt(N, d, D, rng, climb_deadline, repair_deadline)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
