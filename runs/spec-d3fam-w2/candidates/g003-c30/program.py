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
# NEW construction: multi-orbit voltage lifts with orbit-representative cost.
#
# Base graph: k vertices A_0..A_{k-1} and k vertices B_0..B_{k-1}. Each A_i has
# d darts, and the darts are spread so every B_j also receives exactly d darts
# (dart m = i*d + t goes to B_{m mod k}). A dart (i, j, g) of a group G of
# order N joins (A_i, x) to (B_j, x*g) for every x in G. Each dart set with
# distinct (i, j, g) triples gives a simple d-regular bipartite graph on 2kN
# vertices.
#
# Key fact used: left multiplication by h, x -> h*x on every orbit, is an
# automorphism. So each of the 2k orbits is vertex-transitive, and the
# diameter is at most D iff the 2k representatives (orbit_o, identity) reach
# all 2kN vertices within D steps. The annealing cost is therefore
#   sum over representatives of (unreached vertices) + 100 * (duplicate darts),
# which is about 2k BFS runs instead of one per vertex.
# ----------------------------------------------------------------------------

def _ball(adj, s, D, n):
    """Number of vertices within distance D of s."""
    seen = bytearray(n)
    seen[s] = 1
    frontier = [s]
    cnt = 1
    for _ in range(D):
        nxt = []
        for u in frontier:
            for v in adj[u]:
                if not seen[v]:
                    seen[v] = 1
                    nxt.append(v)
        cnt += len(nxt)
        frontier = nxt
        if not frontier:
            break
    return cnt


def _lift_cost(k, N, M, darts, D):
    """Cost of a multi-orbit lift: unreached pairs from orbit representatives plus duplicate-dart penalty."""
    n = 2 * k * N
    adj = [[] for _ in range(n)]
    seen = set()
    dup = 0
    for i, j, g in darts:
        key = (i, j, g)
        if key in seen:
            dup += 1
        else:
            seen.add(key)
        ai = i * N
        bj = (k + j) * N
        for x in range(N):
            a = ai + x
            b = bj + M[x][g]
            adj[a].append(b)
            adj[b].append(a)
    bad = 0
    for o in range(2 * k):
        bad += n - _ball(adj, o * N, D, n)
    return bad + 100 * dup


def _anneal_lift(k, N, d, M, D, rng, deadline):
    """Anneal voltages of a k-orbit lift until all orbit representatives reach everything within D."""
    while time.monotonic() < deadline:
        darts = [[i, (i * d + t) % k, rng.randrange(N)] for i in range(k) for t in range(d)]
        cur = _lift_cost(k, N, M, darts, D)
        moves = 4000
        for it in range(moves):
            if cur == 0:
                return darts
            if (it & 63) == 0 and time.monotonic() >= deadline:
                return None
            T = 1.0 * (0.05 ** (it / moves))
            idx = rng.randrange(len(darts))
            old = darts[idx][2]
            darts[idx][2] = rng.randrange(N)
            c = _lift_cost(k, N, M, darts, D)
            if c <= cur or rng.random() < math.exp(-(c - cur) / T):
                cur = c
            else:
                darts[idx][2] = old
        if cur == 0:
            return darts
    return None


def _lift_edges(k, N, M, darts):
    """Expand darts into the edge list of the lift; A vertices are 0..kN-1, B vertices kN..2kN-1."""
    E = []
    for i, j, g in darts:
        ai = i * N
        bj = (k + j) * N
        for x in range(N):
            E.append((ai + x, bj + M[x][g]))
    return 2 * k * N, E


# ----------------------------------------------------------------------------
# Bi-Cayley graphs over non-abelian groups (parent's search, kept as a fallback).
#
# Let G be a group of order N and S a subset of G with |S| = d and 1 in S.
# Vertices a_x and b_y (x, y in G); a_x ~ b_{x s} for s in S.
# Diameter <= 3 holds iff S S^-1 = G, giving order 2N with N <= d(d-1)+1.
# ----------------------------------------------------------------------------

def _delta(cnt, S, skip, v, sign, Q):
    """Add (sign>0) or remove (sign<0) the quotients created by element v against S[j], j != skip."""
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
            continue
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
# Driver: lift search for the new family, then bi-Cayley search for the rest.
# ----------------------------------------------------------------------------

def _lift_search(d, D, rng, deadline, best):
    """Grow multi-orbit lifts (k = 2, 3, 4 orbits per side) while the order beats the current best."""
    moore = lib.moore_bound(d, D)
    for k in (2, 3, 4):
        N = best[0] // (2 * k) + 1
        while 2 * k * N <= moore and time.monotonic() < deadline:
            specs = _specs(N, rng, cap=6)
            found = None
            for spec in specs:
                now = time.monotonic()
                if now >= deadline:
                    break
                sub = min(deadline, now + max(2.0, (deadline - now) / 3))
                try:
                    M, _ = _tables(spec, N)
                except Exception:
                    continue
                darts = _anneal_lift(k, N, d, M, D, rng, sub)
                if darts is not None:
                    found = (darts, M)
                    break
            if found is None:
                break
            n, E = _lift_edges(k, N, found[1], found[0])
            if n > best[0] and lib.is_valid(n, E, d, D):
                best = (n, E)
            N += 1
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
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
    except Exception:
        pass

    # New: multi-orbit voltage lifts, searched until half the budget is used.
    try:
        if lib.moore_bound(d, D) > best[0]:
            best = _lift_search(d, D, rng, start + 0.5 * time_limit, best)
    except Exception:
        pass

    # Parent: bi-Cayley graphs over non-abelian groups for the remaining time.
    try:
        max_N = d * (d - 1) + 1
        N = best[0] // 2 + 1
        deadline = start + 0.8 * time_limit
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

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
