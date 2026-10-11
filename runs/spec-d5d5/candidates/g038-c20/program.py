import math
import random
import time

import lib


MAX_GROUPS = 10        # semidirect groups tried per order before moving on
ANNEAL_ITERS = 1500    # annealing steps per bi-Cayley attempt
MULTI_ITERS = 800      # annealing steps per multi-base attempt
SWEEP_BAND = 30        # restart the order sweep after this many orders
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
    """Cached (order, mul, T, invs): T[x][g] = x*g and invs[g] = g^-1."""
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


def _unreached_bc(N, T, invs, S, D):
    """Pairs not within distance D, counted from A_0 and B_0 of the bi-Cayley graph.

    A_x ~ B_{x g} for g in S. Left translation is an automorphism that is
    transitive on each side, so two sources suffice.
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
    """Simulated annealing over a connection set S (identity fixed, WLOG)."""
    if d < 2 or d > N:
        return None
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _unreached_bc(N, T, invs, S, D)
    t0, t1 = 3.0, 0.2
    for it in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        temp = t0 * (t1 / t0) ** (it / iters)
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _unreached_bc(N, T, invs, S2, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            S, cur = S2, v
    return S if cur == 0 else None


def _multi_cost(k, G, D, darts, perms):
    """Pairs (representative, vertex) not reached within D. Zero is a candidate."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return 10 ** 9
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        ba = i * G
        bb = (k + j) * G
        for g in range(G):
            a = ba + g
            b = bb + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in reps:
        seen = bytearray(N)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - count
    return total


def _anneal_multi(d, D, k, G, T, rng, iters, deadline):
    """Annealed multi-base lift: each layer is a perfect matching of k A-bases to k B-bases."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])

    def perm(s):
        return [T[g][s] for g in range(G)]

    perms = [perm(s) for _, _, s in darts]
    cost = _multi_cost(k, G, D, darts, perms)
    t0, t1 = 3.0, 0.2
    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        temp = t0 * (t1 / t0) ** (it / iters)
        idx = rng.randrange(len(darts))
        old = darts[idx][2]
        new = rng.randrange(G)
        if new == old:
            continue
        oldp = perms[idx]
        darts[idx][2] = new
        perms[idx] = perm(new)
        c2 = _multi_cost(k, G, D, darts, perms)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost = c2
        else:
            darts[idx][2] = old
            perms[idx] = oldp
    if cost != 0:
        return None
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is always valid for D >= 2.
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

    if d >= 2:
        N_next = None
        while best[0] < moore and time.monotonic() < deadline:
            if rng.random() < 0.75:
                # Bi-Cayley lift over a group of order N (2N vertices), sweeping N upward.
                lo = best[0] // 2 + 1
                if lo > moore // 2:
                    break
                if N_next is None or N_next < lo or N_next > lo + SWEEP_BAND:
                    N_next = lo
                N = N_next
                N_next += 1
                if N <= d:
                    continue
                groups = _groups(N)
                rng.shuffle(groups)
                for m, k2, r in groups[:MAX_GROUPS]:
                    if time.monotonic() > deadline:
                        break
                    _, _, T, invs = _tables(m, k2, r)
                    S = _anneal_bc(N, T, invs, d, D, rng, ANNEAL_ITERS, deadline)
                    if S is not None:
                        consider(2 * N, [(x, N + T[x][g]) for x in range(N) for g in S])
                        break
            else:
                # Multi-base lift with k bases per side over a semidirect group of order G.
                k = rng.choice((2, 3))
                lo = best[0] // (2 * k) + 1
                if 2 * k * lo > moore:
                    break
                G = lo + rng.randrange(max(2, lo // 10))
                gs = _groups(G)
                if not gs:
                    continue
                m, k2, r = rng.choice(gs)
                _, _, T, _ = _tables(m, k2, r)
                res = _anneal_multi(d, D, k, G, T, rng, MULTI_ITERS, deadline)
                if res is not None:
                    consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
