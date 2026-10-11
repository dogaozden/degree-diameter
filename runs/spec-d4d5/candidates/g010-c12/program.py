import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Family 1 (bold, new): simulated annealing on bipartite edge switches.
#
# Start from a circulant bipartite graph (a Haar graph with a random shift set,
# always valid and d-regular), then apply degree-preserving double edge swaps
# (a1,b1),(a2,b2) -> (a1,b2),(a2,b1). The cost is the number of vertex pairs at
# distance > D, counted with bitmask balls. Cost 0 means diameter <= D.
# ----------------------------------------------------------------------------

def _bad(n, adj, D):
    """Number of unordered pairs at distance > D (unreachable pairs included)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        if new == reach:
            break
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _set_edges(adj, m, rem, add):
    """Remove and add bipartite edges (a, b) with a in A (0..m-1) and b in B (stored as m+b)."""
    for a, b in rem:
        adj[a].remove(m + b)
        adj[m + b].remove(a)
    for a, b in add:
        adj[a].append(m + b)
        adj[m + b].append(a)


def _bold_sa(d, D, m, rng, deadline):
    """Anneal a d-regular bipartite graph on m+m vertices toward diameter <= D. Returns (n, edges) or None."""
    if m < d:
        return None
    shifts = rng.sample(range(m), d)
    E = [(i, (i + s) % m) for i in range(m) for s in shifts]
    Eset = set(E)
    adj = [[] for _ in range(2 * m)]
    for a, b in E:
        adj[a].append(m + b)
        adj[m + b].append(a)
    cost = _bad(2 * m, adj, D)
    t_start = time.monotonic()
    span = max(1e-6, deadline - t_start)
    T0, T1 = 2.0, 0.2
    L = len(E)
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        frac = min(1.0, (now - t_start) / span)
        T = T0 * (T1 / T0) ** frac
        i = rng.randrange(L)
        j = rng.randrange(L)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        new1, new2 = (a1, b2), (a2, b1)
        if new1 in Eset or new2 in Eset:
            continue
        old1, old2 = (a1, b1), (a2, b2)
        # Apply the switch.
        Eset.difference_update((old1, old2))
        Eset.update((new1, new2))
        E[i], E[j] = new1, new2
        _set_edges(adj, m, [old1, old2], [new1, new2])
        c2 = _bad(2 * m, adj, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
        else:
            # Revert the switch.
            Eset.difference_update((new1, new2))
            Eset.update((old1, old2))
            E[i], E[j] = old1, old2
            _set_edges(adj, m, [new1, new2], [old1, old2])
    if cost == 0:
        return 2 * m, [(a, m + b) for a, b in E]
    return None


# ----------------------------------------------------------------------------
# Family 2 (from parent): annealed bi-Cayley voltage lifts over semidirect products.
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


def _cost_lift(k, G, D, darts, perms):
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


def _edges_lift(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal_lift(d, D, k, G, mul, rng, deadline, iters):
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost_lift(k, G, D, darts, perms)

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
            c2 = _cost_lift(k, G, D, darts, perms)
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
            c2 = _cost_lift(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _edges_lift(k, G, darts, perms)
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

    # Keep a generous margin under the per-case limit.
    budget = max(1.0, min(0.85 * time_limit, time_limit - 5.0))
    deadline = start + budget

    # Safe fallback: K_{d,d} has diameter 2, valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

    # Projective plane incidence when d-1 is a prime power (diameter 3).
    if D >= 3 and lib.is_prime_power(d - 1):
        n0, e0 = lib.projective_plane_incidence(d - 1)
        consider(n0, e0)

    # Phase A: group voltage lifts (parent family, the safe source of records).
    group_end = start + (0.4 if D >= 5 else 0.3) * budget
    if D >= 5:
        ks = [1, 1, 2, 2, 3, 4]
        anneal_iters = 1500
    else:
        ks = [1, 1, 2, 3]
        anneal_iters = 400
    while time.monotonic() < group_end:
        k = rng.choice(ks)
        base = best_n // (2 * k)
        if D >= 5:
            G = max(2, base + 1 + rng.randrange(0, 3))
        else:
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        res = _anneal_lift(d, D, k, order, mul, rng, group_end, iters=anneal_iters)
        if res is not None:
            consider(res[0], res[1])

    # Phase B: bold edge-switch annealing on bipartite graphs just larger than the best so far.
    while time.monotonic() < deadline:
        remaining = deadline - time.monotonic()
        m = best_n // 2 + 1
        if m < d:
            m = d
        attempt_end = min(deadline, time.monotonic() + max(2.0, 0.5 * remaining))
        res = _bold_sa(d, D, m, rng, attempt_end)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
