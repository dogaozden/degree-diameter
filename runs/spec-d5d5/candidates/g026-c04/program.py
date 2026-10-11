import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# D = 3 baseline: incidence graph of PG(2, q) for the largest prime power q
# with q + 1 <= d (meets the Moore bound when d - 1 is a prime power).
# ----------------------------------------------------------------------------

def _best_pg(d):
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# NEW helper: bitset cyclic bi-Cayley cost.
# For the cyclic group Z_N, the Haar graph A_x ~ B_{x+g} (g in S) is
# vertex-transitive on each side, so eccentricities from A_0 and B_0 suffice.
# Rotations of N-bit integers replace per-vertex BFS, so one cost evaluation
# is O(D * d) big-int operations instead of O(N * d) Python steps.
# ----------------------------------------------------------------------------

def _cyc_cost(N, S, D):
    """Unreached (source, vertex) pairs within distance D; 0 means the Haar graph H(Z_N, S) is valid."""
    mask = (1 << N) - 1
    neg = [(-g) % N for g in S]
    fwd = [g % N for g in S]

    def rot(X, g):
        if g == 0:
            return X
        return ((X << g) | (X >> (N - g))) & mask

    total = 0
    for side in (0, 1):
        reachA = 1 if side == 0 else 0
        reachB = 1 if side == 1 else 0
        fA, fB = reachA, reachB
        for step in range(D):
            if step % 2 == 0:
                if fA == 0:
                    break
                nb = 0
                for g in fwd:
                    nb |= rot(fA, g)
                nb &= ~reachB & mask
                reachB |= nb
                fB, fA = nb, 0
            else:
                if fB == 0:
                    break
                na = 0
                for h in neg:
                    na |= rot(fB, h)
                na &= ~reachA & mask
                reachA |= na
                fA, fB = na, 0
        total += 2 * N - reachA.bit_count() - reachB.bit_count()
    return total


def _climb_cyc(N, d, D, rng, iters, deadline):
    """Hill-climb a cyclic connection set S (WLOG 0 in S) to zero cost, with restarts."""
    def fresh():
        S = [0] + rng.sample(range(1, N), d - 1)
        return S, _cyc_cost(N, S, D)

    S, cur = fresh()
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
        v = _cyc_cost(N, S2, D)
        stall = 0 if v < cur else stall + 1
        if v <= cur:
            S, cur = S2, v
        if stall > 300:
            S, cur = fresh()
            stall = 0
    return S if cur == 0 else None


def _search_cyclic(d, D, N, rng, deadline):
    S = _climb_cyc(N, d, D, rng, 4000, deadline)
    if S is None:
        return None
    return [(x, N + (x + g) % N) for x in range(N) for g in S]


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over Z_m x|_r Z_k (one base vertex per side).
# ----------------------------------------------------------------------------

MAX_GROUPS = 12
CLIMB_ITERS = 1500
STALL_LIMIT = 300
ANNEAL_ITERS = 600
N_WINDOW = 8
_BIG = 10 ** 9
_TABLE_CACHE = {}


def _groups(N):
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
    def fresh():
        S = [0] + rng.sample(range(1, N), d - 1)
        return S, _unreached(N, T, invs, S, D)

    S, cur = fresh()
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
        if stall > STALL_LIMIT:
            S, cur = fresh()
            stall = 0
    return S if cur == 0 else None


def _search_bicayley(d, D, N, rng, deadline):
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k2, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            break
        _, _, T, invs = _tables(m, k2, r)
        S = _climb(N, T, invs, d, D, rng, CLIMB_ITERS, deadline)
        if S is not None:
            return T, S
    return None


# ----------------------------------------------------------------------------
# Multi-base voltage lifts over semidirect products, annealed.
# ----------------------------------------------------------------------------

def _right_perm(mul, G, s):
    return [mul(g, s) for g in range(G)]


def _cost(k, G, D, darts, perms):
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

        if rng.random() < 0.7 or k == 1:
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
    budget = max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}, diameter 2
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
        if best[0] >= moore or time.monotonic() > deadline:
            return best

    while best[0] < moore and time.monotonic() < deadline:
        n_best = best[0]
        lo = n_best // 2 + 1
        roll = rng.random()

        if roll < 0.4 and d >= 2:
            # NEW: cyclic bi-Cayley (Haar) lift searched with bitset rotations.
            if lo > moore // 2:
                break
            N = lo + rng.randrange(N_WINDOW)
            edges = _search_cyclic(d, D, N, rng, deadline)
            if edges is not None:
                consider(2 * N, edges)
        elif roll < 0.75:
            # Non-abelian bi-Cayley lift over Z_m x|_r Z_k.
            if lo > moore // 2:
                break
            N = lo + rng.randrange(N_WINDOW)
            res = _search_bicayley(d, D, N, rng, deadline)
            if res is not None:
                T, S = res
                edges = [(x, N + T[x][g]) for x in range(N) for g in S]
                consider(2 * N, edges)
        else:
            # Multi-base lift with k base vertices per side.
            k = rng.choice((2, 3))
            lo_k = n_best // (2 * k) + 1
            if 2 * k * lo_k > moore:
                continue
            G = lo_k + rng.randrange(max(2, lo_k // 10))
            if G < 2:
                continue
            m, k2, r = rng.choice(_groups(G))
            order, mul, _ = lib.semidirect_group(m, k2, r)
            res = _anneal(d, D, k, order, mul, rng, deadline, ANNEAL_ITERS)
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
