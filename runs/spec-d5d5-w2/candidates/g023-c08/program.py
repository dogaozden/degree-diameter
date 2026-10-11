import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over Z_m x|_r Z_k: annealed connection-set search.
# ----------------------------------------------------------------------------

MAX_GROUPS = 8
CLIMB_ITERS = 800
ANNEAL_ITERS = 600
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
    """Cached (order, mul, T, invs) for Z_m x|_r Z_k."""
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
    """Count vertex pairs (source, target) not within distance D, from A_0 and B_0."""
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
    """Simulated annealing over a connection set S for a Bi-Cayley graph."""
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


def _edges_multi(k, G, darts, perms):
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
        return _edges_multi(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# Bold alternative: annealed double-edge swaps on d-regular bipartite graphs,
# grown one vertex pair at a time while the diameter condition still holds.
# ----------------------------------------------------------------------------

def _adj_from(N, nA):
    adj = [[] for _ in range(2 * N)]
    for a in range(N):
        for b in nA[a]:
            adj[a].append(N + b)
            adj[N + b].append(a)
    return adj


def _bad_pairs(n, adj, D):
    """Ordered count of vertex pairs at distance more than D (zero iff diameter <= D)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            x = reach[v]
            for u in adj[v]:
                x |= reach[u]
            new.append(x)
        reach = new
    return sum(n - r.bit_count() for r in reach)


def _random_regular(N, d, rng):
    """Simple d-regular bipartite graph: Haar graph with d distinct random shifts."""
    shifts = rng.sample(range(N), d)
    nA = [[(a + s) % N for s in shifts] for a in range(N)]
    nB = [[] for _ in range(N)]
    for a in range(N):
        for b in nA[a]:
            nB[b].append(a)
    return nA, nB


def _swap_anneal(d, D, nA, nB, rng, deadline, iters):
    """Annealed double-edge swaps preserving regularity and simplicity. True if diameter <= D."""
    N = len(nA)
    n = 2 * N
    cost = _bad_pairs(n, _adj_from(N, nA), D)
    if cost == 0:
        return True
    T0 = 3.0
    for step in range(iters):
        if time.monotonic() > deadline:
            break
        a1 = rng.randrange(N)
        a2 = rng.randrange(N)
        if a1 == a2:
            continue
        i = rng.randrange(d)
        j = rng.randrange(d)
        b1 = nA[a1][i]
        b2 = nA[a2][j]
        if b1 == b2 or b2 in nA[a1] or b1 in nA[a2]:
            continue
        nA[a1][i] = b2
        nA[a2][j] = b1
        nB[b1][nB[b1].index(a1)] = a2
        nB[b2][nB[b2].index(a2)] = a1
        c2 = _bad_pairs(n, _adj_from(N, nA), D)
        delta = c2 - cost
        temp = T0 * (1.0 - step / max(1, iters)) + 0.2
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            cost = c2
            if cost == 0:
                return True
        else:
            nA[a1][i] = b1
            nA[a2][j] = b2
            nB[b1][nB[b1].index(a2)] = a1
            nB[b2][nB[b2].index(a1)] = a2
    return cost == 0


def _add_pair(d, nA, nB, rng):
    """Add one A-vertex and one B-vertex by subdividing d disjoint edges. False if it fails."""
    N = len(nA)
    for _ in range(200):
        As = rng.sample(range(N), d)
        idx = [rng.randrange(d) for _ in As]
        bs = [nA[a][i] for a, i in zip(As, idx)]
        if len(set(bs)) == d:
            break
    else:
        return False
    x = N  # new A-vertex, adjacent to bs
    y = N  # new B-vertex, adjacent to As
    nA.append(list(bs))
    nB.append(list(As))
    for a, i, b in zip(As, idx, bs):
        nA[a][i] = y
        nB[b][nB[b].index(a)] = x
    return True


def _edges_of(nA):
    N = len(nA)
    return [(a, N + b) for a in range(N) for b in nA[a]]


def _phase_b(d, D, n_best, rng, deadline, consider):
    N = max(d, n_best // 4)
    nA, nB = _random_regular(N, d, rng)
    ok = False
    while not ok and time.monotonic() < deadline:
        ok = _swap_anneal(d, D, nA, nB, rng, deadline, 4000)
    if not ok:
        return
    while time.monotonic() < deadline:
        consider(2 * len(nA), _edges_of(nA))
        snapA = [r[:] for r in nA]
        snapB = [r[:] for r in nB]
        grown = False
        for _ in range(3):
            if time.monotonic() >= deadline:
                break
            nA[:] = [r[:] for r in snapA]
            nB[:] = [r[:] for r in snapB]
            if not _add_pair(d, nA, nB, rng):
                continue
            if _swap_anneal(d, D, nA, nB, rng, deadline, 1500):
                grown = True
                break
        if not grown:
            nA[:] = snapA
            nB[:] = snapB
            break


# ----------------------------------------------------------------------------
# Phase A: Bi-Cayley and multi-base lift search (the parent's main family).
# ----------------------------------------------------------------------------

def _phase_a(d, D, best, rng, deadline, consider, moore):
    ks = (2, 3)
    bicayley_prob = 0.85 if D >= 4 else 0.6
    tried = {}
    while best[0] < moore and time.monotonic() < deadline:
        n_best = best[0]
        if rng.random() < bicayley_prob:
            lo = n_best // 2 + 1
            if lo > moore // 2:
                break
            window = max(2, lo // 10)
            hi = min(lo + window, moore // 2 + 1)
            N = min(range(lo, hi), key=lambda x: (tried.get(x, 0), rng.random()))
            tried[N] = tried.get(N, 0) + 1
            groups = _groups(N)
            rng.shuffle(groups)
            found = None
            for m, k2, r in groups[:MAX_GROUPS]:
                if time.monotonic() > deadline:
                    break
                _, _, T, invs = _tables(m, k2, r)
                S = _climb(N, T, invs, d, D, rng, CLIMB_ITERS, deadline)
                if S is not None:
                    found = (T, S)
                    break
            if found is not None:
                T, S = found
                edges = [(x, N + T[x][g]) for x in range(N) for g in S]
                consider(2 * N, edges)
        else:
            k = rng.choice(ks)
            lo = n_best // (2 * k) + 1
            if 2 * k * lo > moore:
                continue
            G = lo + rng.randrange(max(2, lo // 10))
            if G < 2:
                continue
            m, k2, r = rng.choice(_groups(G))
            order, mul, _ = lib.semidirect_group(m, k2, r)
            res = _anneal(d, D, k, order, mul, rng, deadline, ANNEAL_ITERS)
            if res is not None:
                consider(res[0], res[1])


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

    # Projective plane incidence meets the Moore bound for D = 3.
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)

    if best[0] >= moore:
        return best

    # Phase A: lift search, using the first part of the budget.
    phase_a_deadline = start + 0.4 * budget
    _phase_a(d, D, best, rng, phase_a_deadline, consider, moore)

    # Phase B: direct annealed search on regular bipartite graphs, grown by vertex pairs.
    if best[0] < moore and time.monotonic() < deadline:
        _phase_b(d, D, best[0], rng, deadline, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
