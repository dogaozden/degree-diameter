import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Safe fallbacks: K_{d,d} (diameter 2) and the projective plane incidence graph.
# ----------------------------------------------------------------------------

def _pg_fallback(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _moore_cap(d, D):
    """Bipartite Moore bound for max degree d >= 3 and diameter D; None if not applicable."""
    if d <= 2:
        return None
    return 2 * sum((d - 1) ** i for i in range(D))


# ----------------------------------------------------------------------------
# NEW family: simulated annealing over general d-regular-ish bipartite graphs.
#
# State: a bipartite graph on sides A = {0..h-1} and B = {h..2h-1} with max
# degree d. Move: 2-switch of two edges (a1,v1),(a2,v2) -> (a1,v2),(a2,v1),
# which preserves all degrees and bipartiteness. Objective: number of vertex
# pairs at distance > D. Zero means the graph is valid.
# ----------------------------------------------------------------------------

def _bad_adj(n, adj, D):
    """Number of unordered vertex pairs at distance > D (unreachable pairs count)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        nxt = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            nxt.append(r)
        reach = nxt
    return sum(n - r.bit_count() for r in reach) // 2


def _random_bip(h, d, rng):
    """Random bipartite graph with max degree d: d layers of random matchings, conflicts skipped."""
    n = 2 * h
    adj = [[] for _ in range(n)]
    present = set()
    edges = []
    for _ in range(d):
        perm = list(range(h))
        rng.shuffle(perm)
        for a in range(h):
            v = h + perm[a]
            if (a, v) not in present:
                present.add((a, v))
                adj[a].append(v)
                adj[v].append(a)
                edges.append((a, v))
    return adj, present, edges


def _anneal_sa(h, d, D, rng, t_end):
    """Anneal a bipartite graph on 2h vertices until every pair is within distance D."""
    n = 2 * h
    adj, present, edges = _random_bip(h, d, rng)
    m = len(edges)
    if m < 2:
        return None
    cost = _bad_adj(n, adj, D)
    t0 = time.monotonic()
    span = max(1e-3, t_end - t0)
    T0 = max(1.0, 0.05 * cost)
    T1 = 0.15
    T = T0
    it = 0
    while cost > 0:
        it += 1
        if (it & 31) == 0:
            now = time.monotonic()
            if now >= t_end:
                break
            frac = min(1.0, (now - t0) / span)
            T = T0 * (T1 / T0) ** frac
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, v1 = edges[i]
        a2, v2 = edges[j]
        if a1 == a2 or v1 == v2:
            continue
        if (a1, v2) in present or (a2, v1) in present:
            continue
        # Apply the switch.
        adj[a1].remove(v1)
        adj[v1].remove(a1)
        adj[a2].remove(v2)
        adj[v2].remove(a2)
        adj[a1].append(v2)
        adj[v2].append(a1)
        adj[a2].append(v1)
        adj[v1].append(a2)
        new_cost = _bad_adj(n, adj, D)
        delta = new_cost - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = new_cost
            present.discard((a1, v1))
            present.discard((a2, v2))
            present.add((a1, v2))
            present.add((a2, v1))
            edges[i] = (a1, v2)
            edges[j] = (a2, v1)
        else:
            # Revert the switch.
            adj[a1].remove(v2)
            adj[v2].remove(a1)
            adj[a2].remove(v1)
            adj[v1].remove(a2)
            adj[a1].append(v1)
            adj[v1].append(a1)
            adj[a2].append(v2)
            adj[v2].append(a2)
    if cost == 0:
        return n, list(edges)
    return None


def _sa_search(d, D, best_n, rng, t_end, hmax):
    """Climb the side size h: each success moves to h+1; failures get a doubled time budget."""
    h = max(d, best_n // 2 + 1)
    best = None
    budget = 2.0
    while time.monotonic() < t_end and h <= hmax:
        now = time.monotonic()
        res = _anneal_sa(h, d, D, rng, min(t_end, now + budget))
        if res is not None:
            best = res
            h += 1
            budget = 2.0
        else:
            budget *= 2.0
    return best


# ----------------------------------------------------------------------------
# Parent family (kept as a second, independent search for D >= 5):
# annealed voltage lifts over semidirect products Z_m x| Z_k.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k of order G, or None."""
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


def _cost_group(k, G, D, darts, perms):
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


def _edges_group(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal_group(d, D, k, G, mul, rng, deadline, iters):
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost_group(k, G, D, darts, perms)

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
            c2 = _cost_group(k, G, D, darts, perms)
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
            c2 = _cost_group(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _edges_group(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# Driver
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallbacks, each validated before use.
    best = None
    cands = []
    if D >= 2:
        cands.append(lib.haar_graph(d, range(d)))  # K_{d,d}, diameter 2
    if D >= 3:
        pg = _pg_fallback(d)
        if pg is not None:
            cands.append(pg)
    for n, e in cands:
        if lib.is_valid(n, e, d, D) and (best is None or n > best[0]):
            best = (n, e)
    if best is None:
        return 1, []

    budget = min(0.85 * time_limit, time_limit - 3.0)
    if budget <= 1.0 or d < 3 or D < 3:
        return best

    t_end = start + budget
    rng = random.Random(seed)
    cap = _moore_cap(d, D)
    hmax = cap // 2 if cap is not None else 10 ** 6

    # Phase 1: bold new family (bipartite annealing). Gets half the budget when
    # the parent family also runs, otherwise the whole budget.
    t_sa = start + 0.5 * budget if D >= 5 else t_end
    res = _sa_search(d, D, best[0], rng, t_sa, hmax)
    if res is not None and res[0] > best[0] and lib.is_valid(res[0], res[1], d, D):
        best = res

    # Phase 2: parent family, annealed group voltage lifts, for D >= 5.
    if D >= 5:
        rng2 = random.Random(seed * 7919 + d)
        ks = [1, 1, 2, 2, 3, 4]
        while time.monotonic() < t_end - 0.2:
            k = rng2.choice(ks)
            base = best[0] // (2 * k)
            G = max(2, base + 1 + rng2.randrange(0, 3))
            g = _sample_group(G, rng2)
            if g is None:
                continue
            order, mul = g
            r = _anneal_group(d, D, k, order, mul, rng2, t_end, 1500)
            if r is not None and r[0] > best[0] and lib.is_valid(r[0], r[1], d, D):
                best = r

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
