import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane baseline (diameter 3 optimum when d-1 is a prime power).
# ----------------------------------------------------------------------------

def _pg_candidate(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d, or None."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Family 1: annealed voltage lifts over Z_m x| Z_k2 (kept from the parent).
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    for _ in range(80):
        k2 = rng.choice([1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12])
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in rng.sample(range(1, m), min(m - 1, 60))
                     if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def _right_perm(mul, G, s):
    return [mul(g, s) for g in range(G)]


def _lift_cost(k, G, D, darts, perms):
    """Number of (representative, vertex) pairs not within distance D. Zero means valid."""
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


def _lift_edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _lift_anneal(d, D, k, G, mul, rng, deadline, iters):
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _lift_cost(k, G, D, darts, perms)

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
            c2 = _lift_cost(k, G, D, darts, perms)
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
            c2 = _lift_cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _lift_edges(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# Family 2 (bold change): simulated annealing over d-regular bipartite graphs
# with degree-preserving switches, minimising the number of vertex pairs at
# distance greater than D. Each switch replaces (a1,b1),(a2,b2) by (a1,b2),(a2,b1).
# Temperature cools with elapsed time.
# ----------------------------------------------------------------------------

def _random_regular_bipartite(N, d, rng, tries=200):
    """Union of d random perfect matchings between A = 0..N-1 and B = 0..N-1, all distinct.
    Returns, for each a, a set of b-indices; None on failure."""
    for _ in range(tries):
        adjA = [set() for _ in range(N)]
        ok = True
        for _layer in range(d):
            done = False
            for _t in range(300):
                perm = list(range(N))
                rng.shuffle(perm)
                if all(perm[a] not in adjA[a] for a in range(N)):
                    for a in range(N):
                        adjA[a].add(perm[a])
                    done = True
                    break
            if not done:
                ok = False
                break
        if ok:
            return adjA
    return None


def _bip_cost(n, adj, D):
    """Sum over vertices of the number of vertices not within distance D (bitmask BFS)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(n - r.bit_count() for r in reach)


def _switch_anneal(N, d, D, rng, deadline):
    """Anneal a d-regular bipartite graph on 2N vertices to diameter <= D. Returns (n, edges) or None."""
    adjA = _random_regular_bipartite(N, d, rng)
    if adjA is None:
        return None
    n = 2 * N
    adj = [[] for _ in range(n)]
    E = []
    S = set()
    for a in range(N):
        for b in adjA[a]:
            y = N + b
            adj[a].append(y)
            adj[y].append(a)
            E.append([a, y])
            S.add((a, y))
    cost = _bip_cost(n, adj, D)
    M = len(E)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    T0, T1 = 2.0, 0.05
    it = 0
    while cost > 0:
        it += 1
        if (it & 15) == 0 and time.monotonic() >= deadline:
            break
        i = rng.randrange(M)
        j = rng.randrange(M)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        if (a1, b2) in S or (a2, b1) in S:
            continue
        adj[a1].remove(b1)
        adj[b1].remove(a1)
        adj[a2].remove(b2)
        adj[b2].remove(a2)
        adj[a1].append(b2)
        adj[b2].append(a1)
        adj[a2].append(b1)
        adj[b1].append(a2)
        c2 = _bip_cost(n, adj, D)
        delta = c2 - cost
        frac = min(1.0, (time.monotonic() - t0) / span)
        T = T0 * (T1 / T0) ** frac
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
            E[i] = [a1, b2]
            E[j] = [a2, b1]
            S.discard((a1, b1))
            S.discard((a2, b2))
            S.add((a1, b2))
            S.add((a2, b1))
        else:
            adj[a1].remove(b2)
            adj[b2].remove(a1)
            adj[a2].remove(b1)
            adj[b1].remove(a2)
            adj[a1].append(b1)
            adj[b1].append(a1)
            adj[a2].append(b2)
            adj[b2].append(a2)
    if cost == 0:
        return n, [(a, b) for a, b in E]
    return None


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _pg_candidate(d)
        if pg is not None:
            consider(pg[0], pg[1])
            # Optimal for D = 3 when d - 1 is a prime power: return immediately.
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    total_deadline = start + 0.85 * time_limit

    # Phase 1: voltage-lift search (the parent's record-holding family for D >= 5).
    if D >= 5:
        lift_deadline = start + 0.3 * time_limit
        ks = [1, 1, 2, 2, 3, 4]
        while time.monotonic() < lift_deadline:
            k = rng.choice(ks)
            base = best_n // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, 3))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _lift_anneal(d, D, k, order, mul, rng, lift_deadline, 1500)
            if res is not None:
                consider(res[0], res[1])

    # Phase 2: annealed regular bipartite graphs, aiming just above the current best order.
    N = max(d, best_n // 2 + 1)
    while time.monotonic() < total_deadline - 0.5:
        res = _switch_anneal(N, d, D, rng, total_deadline)
        if res is None:
            break
        consider(res[0], res[1])
        N = res[0] // 2 + 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
