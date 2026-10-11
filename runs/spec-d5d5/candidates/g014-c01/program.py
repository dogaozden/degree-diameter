import itertools
import math
import random
import time

import lib

MAX_GROUPS = 10     # groups tried per (p, N) option within one attempt
ITERS = 500         # annealing steps per random start
RESTARTS = 2        # random base structures per group
MAX_TRIED = 60      # sizes examined per sweep round

_TABLE_CACHE = {}


# ----------------------------------------------------------------------------
# Baseline families (fast, valid when they pass lib.is_valid).
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
# Multi-base voltage lifts over semidirect products Z_m x|_r Z_k.
#
# Base graph: p vertices on side A and p on side B, with d darts at each base
# vertex (a d-regular bipartite multigraph). Each dart (a, b, g) with g in G
# lifts to the edges (A, a, x) -- (B, b, x*g) for all x in G. Distinct labels
# are required for darts on the same (a, b) pair. Left multiplication by G is
# an automorphism, so the diameter is decided by BFS from the identity of each
# of the 2p base vertices.
#
# Vertex ids: A (a, x) -> a*N + x ; B (b, y) -> (p+b)*N + y.
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


def _tables(m, k, r):
    """Cached multiplication table T[x][g] and inverse list for the group Z_m x|_r Z_k."""
    key = (m, k, r)
    t = _TABLE_CACHE.get(key)
    if t is None:
        N = m * k
        _, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        t = (T, invs)
        if len(_TABLE_CACHE) > 64:
            _TABLE_CACHE.clear()
        _TABLE_CACHE[key] = t
    return t


def _random_darts(p, d, rng):
    """d-regular bipartite base multigraph on p+p vertices, built from d random permutations."""
    darts = []
    for _ in range(d):
        perm = list(range(p))
        rng.shuffle(perm)
        for a in range(p):
            darts.append([a, perm[a], 0])
    return darts


def _relabel(darts, k, N, rng):
    """Give dart k a random group label not used by other darts on the same (a, b) pair."""
    a, b, _ = darts[k]
    used = {darts[i][2] for i in range(len(darts))
            if i != k and darts[i][0] == a and darts[i][1] == b}
    free = [g for g in range(N) if g not in used]
    darts[k][2] = rng.choice(free)


def _unreached(p, N, D, darts, T, invs):
    """Count (source, vertex) pairs not within distance D, over the 2p base sources."""
    dA = [[] for _ in range(p)]
    dB = [[] for _ in range(p)]
    for a, b, g in darts:
        dA[a].append((b, g))
        dB[b].append((a, invs[g]))
    V = 2 * p * N
    total = 0
    for src in range(2 * p):
        seen = bytearray(V)
        s = src * N
        seen[s] = 1
        frontier = [s]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                base, x = divmod(u, N)
                row = T[x]
                if base < p:
                    for b, g in dA[base]:
                        v = (p + b) * N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    for a, gi in dB[base - p]:
                        v = a * N + row[gi]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += V - count
    return total


def _edges(p, N, darts, T):
    """Expand base darts into the lifted edge list."""
    E = []
    for a, b, g in darts:
        for x in range(N):
            E.append((a * N + x, (p + b) * N + T[x][g]))
    return E


def _anneal(p, N, D, darts, T, invs, rng, iters, deadline):
    """Simulated annealing over labels and (occasionally) double-swaps of base darts."""
    cur = _unreached(p, N, D, darts, T, invs)
    for it in range(iters):
        if cur == 0:
            return darts
        if time.monotonic() > deadline:
            break
        temp = max(0.05, 2.0 * (1.0 - it / iters))
        cand = [list(x) for x in darts]
        i = rng.randrange(len(cand))
        if p > 1 and rng.random() < 0.3:
            j = rng.randrange(len(cand))
            if cand[i][0] == cand[j][0] or cand[i][1] == cand[j][1]:
                continue
            # Double swap keeps all row and column sums unchanged.
            cand[i][1], cand[j][1] = cand[j][1], cand[i][1]
            _relabel(cand, i, N, rng)
            _relabel(cand, j, N, rng)
        else:
            _relabel(cand, i, N, rng)
        v = _unreached(p, N, D, cand, T, invs)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            darts, cur = cand, v
    return darts if cur == 0 else None


def _attempt(p, N, d, D, rng, deadline):
    """Search groups of order N for a base structure with diameter <= D within the deadline."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            return None
        T, invs = _tables(m, k, r)
        for _ in range(RESTARTS):
            darts = _random_darts(p, d, rng)
            for idx in range(len(darts)):
                _relabel(darts, idx, N, rng)
            res = _anneal(p, N, D, darts, T, invs, rng, ITERS, deadline)
            if res is not None:
                return res, T
            if time.monotonic() > deadline:
                return None
    return None


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit - 0.5
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
            return True
        return False

    # Trivial cases: K2 has diameter 1 and max degree 1.
    if d == 1 or D == 1:
        consider(2, [(0, 1)])
        return best

    # Record-matching case: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        if consider(n, e):
            return best

    # Safe baselines.
    consider(*lib.haar_graph(d, range(d)))   # K_{d,d}, diameter 2
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Multi-base voltage lift sweep, ascending in order above the current best.
    moore = lib._moore_bound(d, D)
    rounds = 0
    while time.monotonic() < deadline and best_n < moore:
        slice_t = 0.5 * (2 ** rounds)
        rounds += 1
        tried = 0
        s = best_n + 1
        while s <= moore and tried < MAX_TRIED and time.monotonic() < deadline:
            opts = [(p, s // (2 * p)) for p in (1, 2, 3)
                    if s % (2 * p) == 0 and s // (2 * p) >= d + 1]
            if opts:
                tried += 1
                rng.shuffle(opts)
                per = slice_t / len(opts)
                for p, N in opts:
                    if best_n >= s or time.monotonic() >= deadline:
                        break
                    end = min(deadline, time.monotonic() + per)
                    res = _attempt(p, N, d, D, rng, end)
                    if res is not None:
                        (darts, T) = res
                        if consider(2 * p * N, _edges(p, N, darts, T)):
                            break
            s += 1
        if tried == 0:
            break

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
