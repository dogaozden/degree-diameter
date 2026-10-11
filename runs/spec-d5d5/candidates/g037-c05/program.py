import math
import random
import time

import lib

# ----------------------------------------------------------------------------
# Search families for bipartite graphs with max degree d and diameter D.
#
# NEW in this version: non-cyclic abelian groups Z_a x Z_b (gcd(a, b) > 1) are
# added to the bi-Cayley family. The parent only used cyclic and semidirect
# groups, and abelian groups give a different set of connection-set
# landscapes. Groups are unified into one (order, T, invs) representation, where
# T[x][g] = x*g and invs[g] = g^-1, so the same annealers run on every family.
# ----------------------------------------------------------------------------

MAX_GROUPS = 8
CLIMB_ITERS = 800
ANNEAL_ITERS = 600
_BIG = 10 ** 9
_CACHE = {}


def _group_specs(N):
    """Group descriptors of order N: semidirect Z_m x|_r Z_k and non-cyclic abelian Z_a x Z_b."""
    specs = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                specs.append(("semi", m, k, r))
    for a in range(2, math.isqrt(N) + 1):
        if N % a == 0:
            b = N // a
            if math.gcd(a, b) > 1:  # gcd 1 gives a cyclic group, already covered
                specs.append(("abel", a, b, 0))
    return specs


def _group(spec):
    """Return (order, T, invs) for a group descriptor, cached."""
    hit = _CACHE.get(spec)
    if hit is not None:
        return hit
    kind, a, b, r = spec
    if kind == "semi":
        order, mul, inv = lib.semidirect_group(a, b, r)
    else:
        order = a * b

        def mul(x, y):
            i1, j1 = divmod(x, b)
            i2, j2 = divmod(y, b)
            return ((i1 + i2) % a) * b + (j1 + j2) % b

        def inv(x):
            i, j = divmod(x, b)
            return ((-i) % a) * b + (-j) % b

    T = [[mul(x, g) for g in range(order)] for x in range(order)]
    invs = [inv(g) for g in range(order)]
    val = (order, T, invs)
    if len(_CACHE) >= 64:
        _CACHE.clear()
    _CACHE[spec] = val
    return val


# ----------------------------------------------------------------------------
# Bi-Cayley lifts: A_x ~ B_{x g} for g in S. Left translation is an automorphism,
# so checking eccentricities from A_0 and B_0 suffices.
# ----------------------------------------------------------------------------

def _unreached(N, T, invs, S, D):
    """Number of (source, vertex) pairs at distance > D, for sources A_0 and B_0."""
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
    """Simulated annealing over S (identity fixed WLOG). Returns valid S or None."""
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _unreached(N, T, invs, S, D)
    best_S, best_v = S, cur
    T0 = 4.0 + 0.05 * cur
    for step in range(iters):
        if best_v == 0 or time.monotonic() > deadline:
            break
        temp = T0 * (1.0 - step / iters) + 0.2
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _unreached(N, T, invs, S2, D)
        delta = v - cur
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            S, cur = S2, v
            if cur < best_v:
                best_S, best_v = S, cur
    return best_S if best_v == 0 else None


# ----------------------------------------------------------------------------
# Multi-base voltage lifts with k base vertices per side over a group of order G.
# Each layer is a perfect matching between A-bases and B-bases, so every vertex
# has degree d (duplicates only lower degree, which is still valid).
# ----------------------------------------------------------------------------

def _perm(T, G, s):
    """Right-multiplication permutation g -> g*s."""
    return [T[g][s] for g in range(G)]


def _cost(k, G, D, darts, perms):
    """Unreached (representative, vertex) pairs. Zero means valid."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        base_a = i * G
        base_b = (k + j) * G
        for g in range(G):
            a = base_a + g
            b = base_b + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in reps:
        seen = [False] * N
        seen[src] = True
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = True
                        nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - count
    return total


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, spec, rng, deadline, iters):
    """Annealing over voltages and per-layer B-assignments. Returns (n, edges) or None."""
    G, T, _ = _group(spec)
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_perm(T, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)
    T0 = max(1.0, 0.05 * cost) if cost < _BIG else 1.0
    T_end = 0.5
    decay = (T_end / T0) ** (1.0 / max(1, iters)) if T0 > T_end else 1.0
    temp = T0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        temp = max(T_end, temp * decay)
        if k == 1 or rng.random() < 0.7:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_perm = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = _perm(T, G, new_s)
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / temp):
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_perm
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / temp):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
    if cost == 0:
        return _edges(k, G, darts, perms)
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

    # K_{d,d}: bipartite, degree d, diameter 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # D = 3: projective plane incidence graph of PG(2, q), q the largest prime power <= d-1.
    if D == 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                consider(*lib.projective_plane_incidence(q))
                break

    # Main search: bi-Cayley lifts (cyclic, semidirect, abelian) and multi-base lifts.
    pbi = 0.7 if D >= 4 else 0.6
    while best[0] < moore and time.monotonic() < deadline:
        n_best = best[0]

        if rng.random() < pbi:
            lo = n_best // 2 + 1
            if lo > moore // 2:
                break
            N = lo + rng.randrange(max(2, lo // 10))
            if N < d:
                continue
            specs = _group_specs(N)
            if not specs:
                continue
            rng.shuffle(specs)
            found = None
            for spec in specs[:MAX_GROUPS]:
                if time.monotonic() > deadline:
                    break
                _, T, invs = _group(spec)
                S = _climb(N, T, invs, d, D, rng, CLIMB_ITERS, deadline)
                if S is not None:
                    found = (T, S)
                    break
            if found is not None:
                T, S = found
                edges = [(x, N + T[x][g]) for x in range(N) for g in S]
                consider(2 * N, edges)
        else:
            k = rng.choice((2, 3))
            lo = n_best // (2 * k) + 1
            if 2 * k * lo > moore:
                continue
            G = lo + rng.randrange(max(2, lo // 10))
            if G < 2:
                continue
            specs = _group_specs(G)
            if not specs:
                continue
            res = _anneal(d, D, k, rng.choice(specs), rng, deadline, ANNEAL_ITERS)
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
