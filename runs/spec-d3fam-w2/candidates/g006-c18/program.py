import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Baselines (safe fallbacks): record AL graph, projective plane incidence,
# and K_{d,d}.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley graphs over groups (one orbit per side): a_x ~ b_{x s}, s in S,
# with S S^-1 = G giving diameter 3 and order 2N.
# ----------------------------------------------------------------------------

def _delta(cnt, S, skip, v, sign, Q):
    """Add (sign>0) or remove (sign<0) the quotients created by element v against S[j], j != skip.

    Returns the change in the number of uncovered non-identity group elements.
    """
    change = 0
    for j, b in enumerate(S):
        if j == skip:
            continue
        for y in (Q[v][b], Q[b][v]):
            if sign > 0:
                if cnt[y] == 0:
                    change -= 1
                cnt[y] += 1
            else:
                cnt[y] -= 1
                if cnt[y] == 0:
                    change += 1
    return change


def _anneal(N, d, Q, rng, deadline, moves):
    """Find S of size d, containing the identity 0, with S S^-1 = G; None on failure or timeout."""
    S = [0] + rng.sample(range(1, N), d - 1)
    cnt = [0] * N
    unc = N - 1
    for j in range(d):
        for k in range(d):
            if j != k:
                y = Q[S[j]][S[k]]
                if cnt[y] == 0:
                    unc -= 1
                cnt[y] += 1
    if unc == 0:
        return S
    for it in range(moves):
        if (it & 255) == 0 and time.monotonic() >= deadline:
            return None
        T = 0.5 * (0.02 ** (it / moves))
        idx = rng.randrange(1, d)
        x = rng.randrange(1, N)
        if x in S:
            continue
        old = S[idx]
        delta = _delta(cnt, S, idx, old, -1, Q) + _delta(cnt, S, idx, x, 1, Q)
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            S[idx] = x
            unc += delta
            if unc == 0:
                return S
        else:
            _delta(cnt, S, idx, x, -1, Q)
            _delta(cnt, S, idx, old, 1, Q)
    return None


def _specs(N, rng, cap=16):
    """Candidate groups of order N: the cyclic group plus a sample of semidirect products Z_a x| Z_k."""
    cands = []
    for k in range(2, N + 1):
        if N % k:
            continue
        a = N // k
        if a == 1:
            continue  # same as cyclic
        for r in range(1, a):
            if math.gcd(r, a) == 1 and pow(r, k, a) == 1:
                cands.append((a, k, r))
    rng.shuffle(cands)
    return [("cyc",)] + cands[:cap]


def _tables(spec, N):
    """Multiplication table M and quotient table Q[x][y] = x * y^-1 for the group named by spec."""
    if spec[0] == "cyc":
        _, mul, inv = lib.cyclic_group(N)
    else:
        a, k, r = spec
        _, mul, inv = lib.semidirect_group(a, k, r)
    M = [[mul(x, y) for y in range(N)] for x in range(N)]
    I = [inv(x) for x in range(N)]
    Q = [[M[x][I[y]] for y in range(N)] for x in range(N)]
    return M, Q


def _search_N(N, d, rng, deadline):
    """Search for a valid S in some group of order N before the deadline. Returns (S, M) or None."""
    specs = _specs(N, rng)
    cache = {}
    rounds = 0
    while time.monotonic() < deadline:
        spec = specs[rounds % len(specs)]
        rounds += 1
        if spec not in cache:
            try:
                cache[spec] = _tables(spec, N)
            except Exception:
                cache[spec] = None
        tab = cache[spec]
        if tab is None:
            continue
        M, Q = tab
        S = _anneal(N, d, Q, rng, deadline, 30000)
        if S is not None:
            return S, M
    return None


def _edges_from(N, d, S, M):
    """Bi-Cayley edges: a_x = x joins b_y = N + x*s for s in S."""
    return [(x, N + M[x][s]) for x in range(N) for s in S]


# ----------------------------------------------------------------------------
# NEW: two-orbit group lifts ("2-orbit bi-Cayley").
#
# Vertices: a_{x,i} = i*N + x (i in {0,1}), b_{y,j} = 2N + j*N + y (j in {0,1}).
# A dart (i, j, g) joins a_{x,i} to b_{x g, j} for every x in G.
# Choose 2d darts: exactly d with each A-label i and exactly d with each
# B-label j, all triples (i, j, g) distinct. Then every vertex has degree d
# and the graph has order 4N, which beats 2N whenever N > (best)/4.
# A simulated annealing search over the darts minimises the number of vertex
# pairs at distance > 3; cost 0 gives a valid diameter-3 graph.
# ----------------------------------------------------------------------------

def _darts_distinct(darts):
    """True if all (i, j, g) triples are pairwise distinct."""
    return len({(i, j, g) for i, j, g in darts}) == len(darts)


def _cost2(darts, N, M):
    """Number of ordered vertex pairs at distance > 3 in the two-orbit lift."""
    n = 4 * N
    adj = [[] for _ in range(n)]
    for i, j, g in darts:
        for x in range(N):
            a = i * N + x
            b = 2 * N + j * N + M[x][g]
            adj[a].append(b)
            adj[b].append(a)
    reach = [1 << v for v in range(n)]
    for _ in range(3):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(n - r.bit_count() for r in reach)


def _anneal2(N, d, M, rng, deadline, moves):
    """Search darts for the two-orbit lift; returns the dart list with cost 0, or None."""
    m2 = 2 * d
    js = [0] * d + [1] * d
    rng.shuffle(js)
    darts = [[t // d, js[t], rng.randrange(N)] for t in range(m2)]
    seen = set()
    for dart in darts:
        while (dart[0], dart[1], dart[2]) in seen:
            dart[2] = rng.randrange(N)
        seen.add((dart[0], dart[1], dart[2]))
    if not _darts_distinct(darts):
        return None
    cost = _cost2(darts, N, M)
    for it in range(moves):
        if cost == 0:
            return darts
        if (it & 63) == 0 and time.monotonic() >= deadline:
            return None
        T = 3.0 * (0.03 ** (it / moves))
        t = rng.randrange(m2)
        if rng.random() < 0.5:
            old = darts[t][2]
            darts[t][2] = rng.randrange(N)
            undo = ("g", t, old)
        else:
            u = rng.randrange(m2)
            if darts[u][1] == darts[t][1]:
                continue
            darts[t][1], darts[u][1] = darts[u][1], darts[t][1]
            undo = ("j", t, u)
        if not _darts_distinct(darts):
            if undo[0] == "g":
                darts[undo[1]][2] = undo[2]
            else:
                darts[undo[1]][1], darts[undo[2]][1] = darts[undo[2]][1], darts[undo[1]][1]
            continue
        new_cost = _cost2(darts, N, M)
        delta = new_cost - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = new_cost
        else:
            if undo[0] == "g":
                darts[undo[1]][2] = undo[2]
            else:
                darts[undo[1]][1], darts[undo[2]][1] = darts[undo[2]][1], darts[undo[1]][1]
    return darts if cost == 0 else None


def _search_lift2(N, d, rng, deadline):
    """Search a two-orbit lift of order 4N over several groups. Returns (darts, M) or None."""
    specs = _specs(N, rng, cap=6)
    cache = {}
    k = 0
    while time.monotonic() < deadline:
        spec = specs[k % len(specs)]
        k += 1
        if spec not in cache:
            try:
                cache[spec] = _tables(spec, N)[0]
            except Exception:
                cache[spec] = None
        M = cache[spec]
        if M is None:
            if k > 4 * len(specs):
                break
            continue
        chunk = min(deadline, time.monotonic() + 6.0)
        darts = _anneal2(N, d, M, rng, chunk, 20000)
        if darts is not None:
            return darts, M
    return None


def _edges2(N, darts, M):
    """Edges of the two-orbit lift: order 4N."""
    edges = set()
    for i, j, g in darts:
        for x in range(N):
            a = i * N + x
            b = 2 * N + j * N + M[x][g]
            edges.add((a, b))
    return 4 * N, sorted(edges)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.5 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
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

        # Bi-Cayley search over groups (order 2N).
        max_N = d * (d - 1) + 1
        N = best[0] // 2 + 1
        while N <= max_N and N >= d and time.monotonic() < deadline:
            rem = deadline - time.monotonic()
            budget = 0.7 * rem
            res = _search_N(N, d, rng, time.monotonic() + budget)
            if res is None:
                break
            S, M = res
            n, e = 2 * N, _edges_from(N, d, S, M)
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
            N += 1
    except Exception:
        pass

    # New: two-orbit group lifts (order 4N) using the remaining time.
    try:
        if D == 3 and d >= 6:
            hard = start + 0.85 * time_limit
            lo = max(d, best[0] // 4 + 1)
            hi = (d * d - d + 1) // 2  # 4N <= 2(d^2 - d + 1), the diameter-3 Moore bound
            for N in range(lo, hi + 1):
                now = time.monotonic()
                rem = hard - now
                if rem < 2.0:
                    break
                res = _search_lift2(N, d, rng, now + 0.45 * rem)
                if res is None:
                    continue
                darts, M = res
                n, e = _edges2(N, darts, M)
                if n > best[0] and lib.is_valid(n, e, d, D):
                    best = (n, e)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
