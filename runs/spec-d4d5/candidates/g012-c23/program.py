import math
import random
import time

import lib


_BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Stage 1: annealed group voltage lifts (Z_m x| Z_k2), the proven fallback.
#
# Vertices: A_i,g = i*G + g  and  B_j,h = (k+j)*G + h.
# Dart (i, j, s) joins A_i,g to B_j,mul(g,s) for every g in the group.
# ----------------------------------------------------------------------------

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
    """Permutation g -> mul(g, s) of the group."""
    return [mul(g, s) for g in range(G)]


def _lift_cost(k, G, D, darts, perms):
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


def _lift_edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal_lift(d, D, k, G, mul, rng, deadline, iters):
    """Simulated annealing over voltages and per-layer B-assignments."""
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
# Stage 2 (bold, different family): degree-preserving edge-switch annealing
# on bipartite graphs with parts of size m, starting from a Haar graph and
# minimising the number of pairs at distance greater than D.
# No group structure is imposed, so the search is not limited to lifts.
# ----------------------------------------------------------------------------

def _bip_cost(m, adj, D):
    """Number of unordered vertex pairs at distance > D (bitset balls)."""
    n = 2 * m
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _anneal_bip(m, d, D, rng, deadline):
    """Anneal a d-regular bipartite graph with parts of size m to diameter <= D. Returns (n, edges) or None."""
    n = 2 * m
    S = rng.sample(range(m), d)
    adj = [set() for _ in range(n)]
    E = []
    for i in range(m):
        for s in S:
            b = m + (i + s) % m
            adj[i].add(b)
            adj[b].add(i)
            E.append([i, b])
    cost = _bip_cost(m, adj, D)
    if cost == 0:
        return n, [(a, b) for a, b in E]

    ne = len(E)
    T0, T1 = 1.5, 0.08
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    T = T0
    it = 0
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        if it % 16 == 0:
            frac = min(1.0, (now - t0) / span)
            T = T0 * (T1 / T0) ** frac
        it += 1

        i = rng.randrange(ne)
        j = rng.randrange(ne)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if b2 in adj[a1] or b1 in adj[a2]:
            continue

        adj[a1].discard(b1); adj[b1].discard(a1)
        adj[a2].discard(b2); adj[b2].discard(a2)
        adj[a1].add(b2); adj[b2].add(a1)
        adj[a2].add(b1); adj[b1].add(a2)

        c2 = _bip_cost(m, adj, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
            E[i] = [a1, b2]
            E[j] = [a2, b1]
        else:
            adj[a1].discard(b2); adj[b2].discard(a1)
            adj[a2].discard(b1); adj[b1].discard(a2)
            adj[a1].add(b1); adj[b1].add(a1)
            adj[a2].add(b2); adj[b2].add(a2)

    if cost == 0:
        return n, [(a, b) for a, b in E]
    return None


# ----------------------------------------------------------------------------
# Structured seeds: projective planes (D >= 3).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
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
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Stage 1 (about 40% of the budget): annealed group lifts. Reliable baseline.
    stage1_deadline = start + 0.4 * time_limit
    ks = [1, 1, 2, 2, 3, 4]
    while time.monotonic() < stage1_deadline:
        k = rng.choice(ks)
        base = best_n // (2 * k)
        G = max(2, base + 1 + rng.randrange(0, 3))
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        res = _anneal_lift(d, D, k, order, mul, rng, stage1_deadline, iters=1500)
        if res is not None:
            consider(res[0], res[1])

    # Stage 2 (remaining budget): bold edge-switch annealing on bipartite graphs.
    # Target the smallest part size m with 2m > best_n, and move up on success.
    if D >= 3:
        m_target = best_n // 2 + 1
        while time.monotonic() < deadline:
            now = time.monotonic()
            slice_end = now + max(2.0, 0.5 * (deadline - now))
            slice_end = min(slice_end, deadline)
            res = _anneal_bip(m_target, d, D, rng, slice_end)
            if res is not None:
                n_new, e_new = res
                if lib.is_valid(n_new, e_new, d, D):
                    consider(n_new, e_new)
                    m_target = n_new // 2 + 1
                    continue
            # On failure, retry the same target from a new random start.

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
