import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# D = 3: projective plane incidence graphs (meet the Moore bound when d-1 is a
# prime power; otherwise the largest PG(2, q) with q+1 <= d is used).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# NEW HELPER: vectorised reachability for bi-Cayley lifts.
#
# A bi-Cayley graph has A_x ~ B_{x g} for g in S (group elements, left
# translation is an automorphism). Eccentricities from A_0 and B_0 determine
# the whole diameter. Instead of Python BFS we keep the BFS frontier as boolean
# numpy masks and gather neighbours with fancy indexing over the multiplication
# table Tn (Tn[x, g] = x*g). Each BFS level is a few array operations, which is
# several times faster than the pure-Python loop for orders in the hundreds,
# so the hill-climb can test many more connection sets per second.
# ----------------------------------------------------------------------------

def _cayley_unreached_np(N, Tn, Sarr, Sinv, D):
    """Number of (source, vertex) pairs not within distance D, sources A_0 and B_0."""
    total = 0
    for src in (0, N):
        seen_a = np.zeros(N, dtype=bool)
        seen_b = np.zeros(N, dtype=bool)
        fa = np.zeros(N, dtype=bool)
        fb = np.zeros(N, dtype=bool)
        if src < N:
            fa[src] = True
            seen_a[src] = True
        else:
            fb[src - N] = True
            seen_b[src - N] = True
        for _ in range(D):
            if not (fa.any() or fb.any()):
                break
            nb = np.zeros(N, dtype=bool)
            na = np.zeros(N, dtype=bool)
            if fa.any():
                # A_x -> B_{x g}
                nb[Tn[fa][:, Sarr].ravel()] = True
            if fb.any():
                # B_y -> A_{y h} with h = g^-1
                na[Tn[fb][:, Sinv].ravel()] = True
            nb &= ~seen_b
            na &= ~seen_a
            seen_b |= nb
            seen_a |= na
            fa, fb = na, nb
        total += 2 * N - int(seen_a.sum()) - int(seen_b.sum())
    return total


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over Z_m x|_r Z_k (one base vertex per side).
# ----------------------------------------------------------------------------

MAX_GROUPS = 12
CLIMB_ITERS = 2500
STALL_LIMIT = 400
ANNEAL_ITERS = 600
N_WINDOW = 8
_BIG = 10 ** 9
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
    """Cached (order, T, invs, Tn): T[x][g] = x*g as lists, invs[g] = g^-1, Tn the numpy copy of T."""
    key = (m, k, r)
    hit = _TABLE_CACHE.get(key)
    if hit is not None:
        return hit
    order, mul, inv = lib.semidirect_group(m, k, r)
    T = [[mul(x, g) for g in range(order)] for x in range(order)]
    invs = [inv(g) for g in range(order)]
    Tn = np.array(T, dtype=np.int64)
    val = (order, T, invs, Tn)
    if len(_TABLE_CACHE) >= 48:
        _TABLE_CACHE.clear()
    _TABLE_CACHE[key] = val
    return val


def _climb(N, Tn, invs, d, D, rng, iters, deadline):
    """Hill-climb a connection set S (identity fixed as one dart) to zero unreached pairs."""

    def cost(S):
        Sarr = np.array(S, dtype=np.int64)
        Sinv = np.array([invs[g] for g in S], dtype=np.int64)
        return _cayley_unreached_np(N, Tn, Sarr, Sinv, D)

    def fresh():
        S = [0] + rng.sample(range(1, N), d - 1)
        return S, cost(S)

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
        v = cost(S2)
        if v < cur:
            stall = 0
        else:
            stall += 1
        if v <= cur:
            S, cur = S2, v
        if stall > STALL_LIMIT:
            S, cur = fresh()
            stall = 0
    return S if cur == 0 else None


def _search_bicayley(d, D, N, rng, deadline):
    """Try several groups of order N; return (T, S) for the first valid bi-Cayley lift, else None."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k2, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            break
        _, T, invs, Tn = _tables(m, k2, r)
        S = _climb(N, Tn, invs, d, D, rng, CLIMB_ITERS, deadline)
        if S is not None:
            return T, S
    return None


# ----------------------------------------------------------------------------
# General multi-base voltage lifts over semidirect products, annealed.
# ----------------------------------------------------------------------------

def _right_perm(mul, G, s):
    return [mul(g, s) for g in range(G)]


def _cost(k, G, D, darts, perms):
    """Number of (representative, vertex) pairs not reached within distance D. Zero means valid."""
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
    """Simulated annealing over voltages and per-layer B-assignments."""
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

    # Safe fallback: K_{d,d} has diameter 2.
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
    while best[0] < moore and time.monotonic() < deadline:
        n_best = best[0]
        lo = n_best // 2 + 1

        if rng.random() < 0.75:
            if lo > moore // 2:
                break
            N = lo + rng.randrange(N_WINDOW)
            res = _search_bicayley(d, D, N, rng, deadline)
            if res is not None:
                T, S = res
                edges = [(x, N + T[x][g]) for x in range(N) for g in S]
                consider(2 * N, edges)
        else:
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
