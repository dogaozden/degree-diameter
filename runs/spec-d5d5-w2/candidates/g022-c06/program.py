import itertools
import math
import random
import time

import lib

ITERS = 500          # annealing steps per (N, group) attempt
T_HOT = 1.5          # initial temperature (unreached-pair units)
T_COLD = 0.15        # final temperature
MAX_GROUPS = 8       # groups tried per order N
P_SWAP = 0.25        # probability of a label-swap move (multi-orbit only)


# ----------------------------------------------------------------------------
# Baseline families: always valid when they pass lib.is_valid.
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q."""
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Multi-orbit group lifts (bold change).
#
# Vertices: A_{i,x} = i*N + x and B_{j,y} = b*N + j*N + y, with i, j in 0..b-1
# and x, y in a group G of order N. Each A-orbit row i has d "slots"; slot s
# of row i points to B-orbit J[i][s] with voltage V[i][s] in G, giving edges
# A_{i,x} -- B_{J, x*V}. The b*d slot labels are balanced so every B-orbit
# receives exactly d slots, so the graph is d-regular and bipartite.
#
# Left multiplication by G is an automorphism, so diameter <= D is equivalent
# to every one of the 2b "identity" vertices reaching all 2bN vertices within D
# steps. That is checked with bitmask BFS over the 2b sources.
# With b = 1 this is the single-orbit bi-Cayley search, so the same code also
# serves as a fallback.
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


def _cost(b, N, d, D, T, J, V):
    """Number of (source, vertex) pairs not within distance D, over the 2b identity sources."""
    n = 2 * b * N
    adj = [[] for _ in range(n)]
    for i in range(b):
        Ji, Vi = J[i], V[i]
        for s in range(d):
            j, g = Ji[s], Vi[s]
            off = b * N + j * N
            for x in range(N):
                a = i * N + x
                bb = off + T[x][g]
                adj[a].append(bb)
                adj[bb].append(a)
    srcs = [i * N for i in range(b)] + [b * N + j * N for j in range(b)]
    K = len(srcs)
    reach = [0] * n
    for k, sv in enumerate(srcs):
        reach[sv] |= 1 << k
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(K - reach[v].bit_count() for v in range(n))


def _row_ok(J, V, i, d):
    """Row i must have distinct (label, voltage) pairs so that no parallel edges appear."""
    return len({(J[i][s], V[i][s]) for s in range(d)}) == d


def _anneal(b, N, d, D, T, rng, t_end):
    """Anneal slot labels and voltages until every identity source reaches everything within D."""
    labels = [j for j in range(b) for _ in range(d)]
    rng.shuffle(labels)
    J = [labels[i * d:(i + 1) * d] for i in range(b)]
    V = [[rng.randrange(N) for _ in range(d)] for _ in range(b)]
    for i in range(b):
        tries = 0
        while not _row_ok(J, V, i, d) and tries < 100:
            V[i] = [rng.randrange(N) for _ in range(d)]
            tries += 1
        if not _row_ok(J, V, i, d):
            return None

    cur = _cost(b, N, d, D, T, J, V)
    for it in range(ITERS):
        if cur == 0 or time.monotonic() >= t_end:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / ITERS)
        if b > 1 and rng.random() < P_SWAP:
            # Swap two labels: keeps every B-orbit at exactly d slots.
            i1, s1 = rng.randrange(b), rng.randrange(d)
            i2, s2 = rng.randrange(b), rng.randrange(d)
            if J[i1][s1] == J[i2][s2]:
                continue
            J[i1][s1], J[i2][s2] = J[i2][s2], J[i1][s1]
            v = None
            if _row_ok(J, V, i1, d) and _row_ok(J, V, i2, d):
                v = _cost(b, N, d, D, T, J, V)
            if v is not None and (v <= cur or rng.random() < math.exp(-(v - cur) / temp)):
                cur = v
            else:
                J[i1][s1], J[i2][s2] = J[i2][s2], J[i1][s1]
        else:
            # Change one voltage.
            i = rng.randrange(b)
            s = rng.randrange(d)
            old = V[i][s]
            V[i][s] = rng.randrange(N)
            v = None
            if _row_ok(J, V, i, d):
                v = _cost(b, N, d, D, T, J, V)
            if v is not None and (v <= cur or rng.random() < math.exp(-(v - cur) / temp)):
                cur = v
            else:
                V[i][s] = old

    if cur == 0 and all(_row_ok(J, V, i, d) for i in range(b)):
        return J, V
    return None


def _edges(b, N, d, T, J, V):
    """Expand the base description into the explicit edge list."""
    edges = []
    for i in range(b):
        for s in range(d):
            j, g = J[i][s], V[i][s]
            off = b * N + j * N
            for x in range(N):
                edges.append((i * N + x, off + T[x][g]))
    return edges


def _try_N(b, N, d, D, rng, t_end):
    """Try several groups of order N; return (n, edges) for the first success."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS]:
        if time.monotonic() >= t_end:
            return None
        _, mul, _ = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        res = _anneal(b, N, d, D, T, rng, t_end)
        if res is not None:
            J, V = res
            return 2 * b * N, _edges(b, N, d, T, J, V)
    return None


def _search(b, d, D, rng, t_end, floor_total, consider):
    """Search N from the top of the Moore window downward, widening when passes fail."""
    Nmax = lib.moore_bound(d, D) // (2 * b)
    lo = max(d + 1, floor_total // (2 * b) + 1)
    cands = list(range(lo, Nmax + 1))
    if not cands:
        return
    W = 4
    budget = 1.0
    while cands and time.monotonic() < t_end:
        window = cands[-min(W, len(cands)):]
        rng.shuffle(window)
        found = None
        for N in window:
            now = time.monotonic()
            if now >= t_end:
                break
            res = _try_N(b, N, d, D, rng, min(t_end, now + budget))
            if res is not None:
                consider(*res)
                found = N
                break
        if found is not None:
            # Only larger orders can improve on this result now.
            cands = [c for c in cands if c > found]
            W = 4
            budget = 1.0
        else:
            W = min(len(cands), W + 4)
            budget = min(3.0, budget * 1.4)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    t_end = start + max(1.0, 0.85 * time_limit - 2.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    state = {"best": (1, []), "best_n": 1}

    def consider(n, e):
        if n > state["best_n"] and lib.is_valid(n, e, d, D):
            state["best"] = (n, e)
            state["best_n"] = n

    if D == 1:
        consider(2, [(0, 1)])
        return state["best"]

    # Record-matching case: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return state["best"]

    # Safe baselines.
    consider(*lib.haar_graph(d, range(d)))   # K_{d,d}, diameter 2
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D >= 4 and time.monotonic() < t_end:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if d < 2 or D < 2:
        return state["best"]

    # Bold path: two-orbit lifts (b = 2) get most of the budget.
    mid = start + 0.75 * (t_end - start)
    _search(2, d, D, rng, mid, state["best_n"], consider)
    # Fallback path: single-orbit bi-Cayley search over the remaining time.
    _search(1, d, D, rng, t_end, state["best_n"], consider)

    n, e = state["best"]
    if not lib.is_valid(n, e, d, D):
        return 1, []
    return n, e
