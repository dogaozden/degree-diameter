import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Safe baselines: record Araujo-Pardo/Lopez graph, projective plane incidence,
# and K_{d,d} (diameter 2, valid for any D >= 2).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# New construction: multi-base-vertex group lifts ("m-base bi-Cayley" graphs).
#
# Take a finite group G of order N and m base vertices per side. Vertices are
# (i, x) with i in 0..2m-1 (i < m: A-side, i >= m: B-side) and x in G.
# Darts (i, j, g) with i an A-base and j a B-base join (i, x) to (m+j, x*g)
# for every x. Each base vertex carries exactly d darts, so the graph is
# d-regular and bipartite on 2mN vertices.
#
# Left multiplication by G is an automorphism, so the graph is vertex-transitive
# within each base class. Diameter <= 3 therefore reduces to checking, for each
# of the 2m base representatives (u, e), that the radius-3 ball covers all
# vertices. The cost is the total number of uncovered vertices over these
# representatives; zero means diameter <= 3.
#
# m = 1 is the ordinary bi-Cayley family. m >= 2 gives more freedom in the
# base structure, which is the change from the previous program.
# Search: simulated annealing over the dart shifts, with random base matrices
# (sums of d permutation matrices) and several groups of order N.
# ----------------------------------------------------------------------------

def _bits(x):
    """Indices of set bits of a non-negative int."""
    out = []
    while x:
        low = x & -x
        out.append(low.bit_length() - 1)
        x ^= low
    return out


def _popcount(x):
    return bin(x).count("1")


def _cost(m, N, M, darts):
    """Number of (base representative, vertex) pairs not within distance 3."""
    n = 2 * m * N
    adj = [[] for _ in range(n)]
    for i, j, g in darts:
        base_a = i * N
        base_b = (m + j) * N
        for x in range(N):
            a = base_a + x
            b = base_b + M[x][g]
            adj[a].append(b)
            adj[b].append(a)
    mk = [0] * n
    for v in range(n):
        s = 0
        for w in adj[v]:
            s |= 1 << w
        mk[v] = s
    total = 0
    for u in range(2 * m):
        v = u * N
        ball1 = mk[v] | (1 << v)
        ball2 = ball1
        for w in _bits(mk[v]):
            ball2 |= mk[w]
        shell = ball2 & ~ball1
        ball3 = ball2
        for w in _bits(shell):
            ball3 |= mk[w]
        total += n - _popcount(ball3)
    return total


def _anneal(m, N, d, M, rng, deadline, moves):
    """Find darts giving diameter <= 3 for this group table M; None on failure or timeout."""
    counts = {}
    for _ in range(d):
        perm = list(range(m))
        rng.shuffle(perm)
        for i in range(m):
            key = (i, perm[i])
            counts[key] = counts.get(key, 0) + 1
    if any(c > N for c in counts.values()):
        return None
    darts = []
    used = {}
    for (i, j), c in counts.items():
        gs = rng.sample(range(N), c)
        used[(i, j)] = set(gs)
        for g in gs:
            darts.append([i, j, g])
    cur = _cost(m, N, M, darts)
    if cur == 0:
        return darts
    for it in range(moves):
        if (it & 31) == 0 and time.monotonic() >= deadline:
            return None
        k = rng.randrange(len(darts))
        i, j, g = darts[k]
        g2 = rng.randrange(N)
        s = used[(i, j)]
        if g2 in s:
            continue
        T = 1.5 * (0.02 ** (it / moves))
        darts[k][2] = g2
        c = _cost(m, N, M, darts)
        if c <= cur or rng.random() < math.exp(-(c - cur) / T):
            s.discard(g)
            s.add(g2)
            cur = c
            if cur == 0:
                return darts
        else:
            darts[k][2] = g
    return None


def _specs(N, rng, cap=8):
    """Candidate groups of order N: None means cyclic; otherwise (a, k, r) for Z_a x| Z_k."""
    cands = []
    for k in range(2, N + 1):
        if N % k:
            continue
        a = N // k
        if a < 2:
            continue
        for r in range(1, a):
            if math.gcd(r, a) == 1 and pow(r, k, a) == 1 % a:
                cands.append((a, k, r))
    rng.shuffle(cands)
    return [None] + cands[:cap]


def _group_table(spec, N):
    """Multiplication table M[x][y] for the group named by spec."""
    if spec is None:
        _, mul, _ = lib.cyclic_group(N)
    else:
        a, k, r = spec
        _, mul, _ = lib.semidirect_group(a, k, r)
    return [[mul(x, y) for y in range(N)] for x in range(N)]


def _search_N(m, N, d, rng, deadline):
    """Search for valid darts with m base vertices per side and group order N. Returns (darts, M) or None."""
    specs = _specs(N, rng)
    tabs = {}
    rounds = 0
    while time.monotonic() < deadline:
        spec = specs[rounds % len(specs)]
        rounds += 1
        if spec not in tabs:
            try:
                tabs[spec] = _group_table(spec, N)
            except Exception:
                tabs[spec] = None
        M = tabs[spec]
        if M is None:
            continue
        darts = _anneal(m, N, d, M, rng, deadline, 20000)
        if darts is not None:
            return darts, M
    return None


def _edges(m, N, M, darts):
    """Expand darts into (n, edges) with A-vertices i*N+x and B-vertices (m+j)*N+y."""
    edges = []
    for i, j, g in darts:
        for x in range(N):
            edges.append((i * N + x, (m + j) * N + M[x][g]))
    return 2 * m * N, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.6 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    if D < 3 or d < 2:
        return best

    try:
        # Known record family for d = q + 2, q a prime power.
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                n_a, e_a = lib.araujo_lopez_graph(d - 2)
                if n_a > best[0] and lib.is_valid(n_a, e_a, d, D):
                    best = (n_a, e_a)
            except Exception:
                pass
        pg = _best_pg(d)
        if pg is not None and pg[0] > best[0] and lib.is_valid(pg[0], pg[1], d, D):
            best = pg

        # New search: multi-base-vertex group lifts with diameter-3 annealing.
        dmax = d * (d - 1) + 1
        for m in (2, 3, 1, 4):
            while time.monotonic() < deadline:
                N = best[0] // (2 * m) + 1
                if N > dmax // m:
                    break
                rem = deadline - time.monotonic()
                budget_end = min(deadline, time.monotonic() + max(1.0, 0.4 * rem))
                res = _search_N(m, N, d, rng, budget_end)
                if res is None:
                    break
                darts, M = res
                n, e = _edges(m, N, M, darts)
                if n > best[0] and lib.is_valid(n, e, d, D):
                    best = (n, e)
                else:
                    break
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
