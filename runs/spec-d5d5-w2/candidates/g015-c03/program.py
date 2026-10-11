import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Strategy:
#   * Safe fallback: K_{d,d} (diameter 2), checked with lib.is_valid.
#   * D = 3: incidence graph of PG(2, q), the largest prime power q with q+1 <= d.
#   * Otherwise: bi-Cayley graphs (one base vertex per side) over semidirect
#     products Z_m x|_r Z_k, found by simulated annealing on the number of
#     unreached pairs. The sweep targets orders just above the current best.
#   * Occasionally: multi-base voltage lifts (k = 2, 3 base vertices per side)
#     over the same family of groups, annealed the same way.
# Every candidate is validated with lib.is_valid before it is accepted.
# ----------------------------------------------------------------------------

MAX_GROUPS = 10     # groups tried per bi-Cayley order N before moving on
BC_ITERS = 2500     # annealing steps per group for bi-Cayley search
ML_ITERS = 1500     # annealing steps for multi-base lifts
BAND = 6            # window above the lower bound swept before wrapping
_BIG = 10 ** 9
_TABLE_CACHE = {}


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


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
    """Cached (order, mul, T, invs) with T[x][g] = x*g and invs[g] = g^-1."""
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
    """Pairs (source, target) not within distance D, from A_0 and B_0.

    Bi-Cayley graph: A_x ~ B_{x g} for g in S. Left translation is an automorphism
    acting transitively on each side, so eccentricities of A_0 and B_0 suffice.
    """
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


def _anneal_bc(N, T, invs, d, D, rng, iters, deadline):
    """Simulated annealing over a d-element connection set S of Z-group elements."""
    S = rng.sample(range(N), d)
    cost = _unreached(N, T, invs, S, D)
    temp0 = 3.0
    for it in range(iters):
        if cost == 0:
            break
        if (it & 31) == 0 and time.monotonic() > deadline:
            break
        temp = temp0 * (1.0 - it / iters) + 0.05
        i = rng.randrange(d)
        c = rng.randrange(N)
        if c in S:
            continue
        old = S[i]
        S[i] = c
        v = _unreached(N, T, invs, S, D)
        if v <= cost or rng.random() < math.exp(-(v - cost) / temp):
            cost = v
        else:
            S[i] = old
    return list(S) if cost == 0 else None


# ----------------------------------------------------------------------------
# Multi-base voltage lifts over semidirect products, annealed.
# ----------------------------------------------------------------------------

def _right_perm(mul, G, s):
    """Permutation g -> g*s of the group."""
    return [mul(g, s) for g in range(G)]


def _cost(k, G, D, darts, perms):
    """Pairs (representative, vertex) not reached within distance D. Zero means valid."""
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


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    """Annealing over voltages and per-layer B-assignments for a k-base lift."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

    T0 = max(1.0, 0.05 * cost) if cost < _BIG else 1.0
    T_end = 0.5
    decay = (T_end / T0) ** (1.0 / max(1, iters)) if T0 > T_end else 1.0
    T = T0

    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(T_end, T * decay)

        if rng.random() < 0.7:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_perm = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = _right_perm(mul, G, new_s)
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
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
            if delta <= 0 or rng.random() < math.exp(-delta / T):
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
    budget = max(0.5, min(0.8 * time_limit, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is bipartite.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Main search: aim above the current best order.
    ml_ks = (2, 3)
    N_try = best[0] // 2 + 1
    while time.monotonic() < deadline and best[0] < moore:
        if rng.random() < 0.7:
            # Bi-Cayley lift: 2N vertices, N = order of the group.
            N_lo = best[0] // 2 + 1
            if N_lo > moore // 2:
                break
            if N_try < N_lo or N_try > N_lo + BAND:
                N_try = N_lo
            N = N_try
            N_try += 1
            if N < d:
                continue
            groups = _groups(N)
            rng.shuffle(groups)
            for m, k2, r in groups[:MAX_GROUPS]:
                if time.monotonic() > deadline:
                    break
                _, _, T, invs = _tables(m, k2, r)
                S = _anneal_bc(N, T, invs, d, D, rng, BC_ITERS, deadline)
                if S is not None:
                    edges = [(x, N + T[x][g]) for x in range(N) for g in S]
                    consider(2 * N, edges)
                    break
        else:
            # Multi-base voltage lift with k base vertices per side.
            k = rng.choice(ml_ks)
            G = best[0] // (2 * k) + 1 + rng.randrange(3)
            if G < 2 or 2 * k * G > moore:
                continue
            m, k2, r = rng.choice(_groups(G))
            order, mul, _ = lib.semidirect_group(m, k2, r)
            res = _anneal(d, D, k, order, mul, rng, deadline, ML_ITERS)
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
