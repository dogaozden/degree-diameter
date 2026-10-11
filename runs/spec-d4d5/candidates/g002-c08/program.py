import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective plane base (diameter 3).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# NEW: bitset 2-switch annealing on d-regular bipartite graphs.
#
# Start from a random d-regular bipartite graph on parts of size m (union of d
# random perfect matchings). Moves are 2-switches (a1,b1),(a2,b2) -> (a1,b2),(a2,b1),
# which keep every degree and the bipartition. The cost is the number of unordered
# pairs at distance > D, computed by bitmask reachability over D rounds.
# ----------------------------------------------------------------------------

def _bitcost(n, adj, D):
    """Number of unordered vertex pairs at distance > D (0 means diameter <= D and connected)."""
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


def _random_biregular(m, d, rng):
    """Edge list of a d-regular bipartite graph on parts {0..m-1} and {m..2m-1}, or None."""
    edges = set()
    for _ in range(d):
        ok = False
        for _attempt in range(60):
            p = list(range(m))
            rng.shuffle(p)
            new = [(a, m + p[a]) for a in range(m)]
            if all(e not in edges for e in new):
                ok = True
                break
        if not ok:
            return None
        edges.update(new)
    return list(edges)


def _switch_anneal(m, d, D, rng, deadline):
    """Anneal a random d-regular bipartite graph on 2m vertices to diameter <= D.

    Returns (n, edges) with zero bad pairs, or None if the deadline passes first.
    """
    n = 2 * m
    E = _random_biregular(m, d, rng)
    if E is None:
        return None
    eset = set(E)
    adj = [[] for _ in range(n)]
    for a, b in E:
        adj[a].append(b)
        adj[b].append(a)
    cost = _bitcost(n, adj, D)
    if cost == 0:
        return n, E

    t0 = time.monotonic()
    span = max(1e-6, deadline - t0)
    T = 1.0
    it = 0
    while cost > 0:
        it += 1
        if (it & 31) == 0:
            now = time.monotonic()
            if now >= deadline:
                break
            frac = (now - t0) / span
            T = max(0.05, 1.5 * (0.03 ** frac))

        i = rng.randrange(len(E))
        j = rng.randrange(len(E))
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        n1 = (a1, b2)
        n2 = (a2, b1)
        if n1 in eset or n2 in eset:
            continue

        # Apply the switch to adjacency lists.
        adj[a1].remove(b1); adj[b1].remove(a1)
        adj[a2].remove(b2); adj[b2].remove(a2)
        adj[a1].append(b2); adj[b2].append(a1)
        adj[a2].append(b1); adj[b1].append(a2)

        c2 = _bitcost(n, adj, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
            eset.discard((a1, b1))
            eset.discard((a2, b2))
            eset.add(n1)
            eset.add(n2)
            E[i] = n1
            E[j] = n2
        else:
            adj[a1].remove(b2); adj[b2].remove(a1)
            adj[a2].remove(b1); adj[b1].remove(a2)
            adj[a1].append(b1); adj[b1].append(a1)
            adj[a2].append(b2); adj[b2].append(a2)

    if cost == 0:
        return n, list(E)
    return None


# ----------------------------------------------------------------------------
# Annealed group voltage lifts over Z_m x| Z_k2 (from the parent).
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


def _vcost(k, G, D, darts, perms):
    """Number of (representative, vertex) pairs not reached within distance D."""
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


def _vedges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _vanneal(d, D, k, G, mul, rng, deadline, iters):
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _vcost(k, G, D, darts, perms)

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
            c2 = _vcost(k, G, D, darts, perms)
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
            c2 = _vcost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _vedges(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# Main driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = 0.85 * time_limit
    deadline = start + total
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    moore = lib._moore_bound(d, D)

    # Phase 1: projective plane base for D >= 3.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Phase 2: voltage lifts until 45% of the budget.
    t_volt = start + 0.45 * total
    ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
    while time.monotonic() < t_volt and best_n < moore:
        k = rng.choice(ks)
        base = best_n // (2 * k)
        G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        res = _vanneal(d, D, k, order, mul, rng, t_volt, iters=400)
        if res is not None:
            consider(res[0], res[1])

    # Phase 3: switch annealing, aiming one half-size above the current best.
    if D >= 3 and d >= 3 and best_n < moore:
        while time.monotonic() < deadline and best_n < moore:
            m = best_n // 2 + 1
            if 2 * m > moore:
                break
            remaining = deadline - time.monotonic()
            slice_end = time.monotonic() + max(1.0, remaining / 3.0)
            res = _switch_anneal(m, d, D, rng, min(slice_end, deadline))
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = lib.haar_graph(d, range(d))
    return best_n, best_e
