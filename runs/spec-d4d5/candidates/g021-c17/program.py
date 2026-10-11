import math
import random
import time

import lib

_BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Projective plane base (diameter 3), used as a safe starting point.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Family 1: annealed bi-Cayley voltage lifts over Z_m x| Z_k2 (seed generator).
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


def _anneal(d, D, k, G, mul, rng, deadline, iters):
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
# Family 2 (new): grow a d-regular bipartite graph one vertex pair at a time,
# then repair it by simulated annealing over double-edge switches.
# ----------------------------------------------------------------------------

def _bad_pairs(N, adj, D):
    """Number of unordered vertex pairs at distance more than D."""
    reach = [1 << v for v in range(N)]
    for _ in range(D):
        new = []
        for v in range(N):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(N - r.bit_count() for r in reach) // 2


def _regular_halves(n, edges, d):
    """If the graph is bipartite, d-regular and balanced, return (k, local edges (a, b)); else None."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    if any(len(a) != d for a in adj):
        return None
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
                elif color[v] == color[u]:
                    return None
    A = [v for v in range(n) if color[v] == 0]
    B = [v for v in range(n) if color[v] == 1]
    if not A or len(A) != len(B):
        return None
    idx = [0] * n
    for i, v in enumerate(A):
        idx[v] = i
    for i, v in enumerate(B):
        idx[v] = i
    E = []
    for u, v in edges:
        if color[u] == 0:
            E.append((idx[u], idx[v]))
        else:
            E.append((idx[v], idx[u]))
    if len(set(E)) != len(E):
        return None
    return len(A), E


def _grow_pair(K, E, d, rng):
    """Add one A-vertex and one B-vertex, keeping all degrees at d.

    Remove a random d-matching (x_i, y_i); join new A to every y_i and new B to every x_i.
    """
    for _ in range(20):
        order = list(range(len(E)))
        rng.shuffle(order)
        usedA, usedB, pick = set(), set(), []
        for i in order:
            a, b = E[i]
            if a in usedA or b in usedB:
                continue
            pick.append(i)
            usedA.add(a)
            usedB.add(b)
            if len(pick) == d:
                break
        if len(pick) == d:
            removed = set(pick)
            newE = [e for i, e in enumerate(E) if i not in removed]
            for i in pick:
                a, b = E[i]
                newE.append((K, b))   # new A vertex K takes over b
                newE.append((a, K))   # new B vertex K takes over a
            return K + 1, newE
    return None


def _repair(K, E, d, D, rng, deadline, iters):
    """Anneal double-edge switches (bipartite, degree-preserving) until the graph has diameter <= D."""
    E = list(E)
    es = set(E)
    N = 2 * K

    def cost_of(EE):
        adj = [[] for _ in range(N)]
        for a, b in EE:
            adj[a].append(K + b)
            adj[K + b].append(a)
        return _bad_pairs(N, adj, D)

    if len(E) < 2:
        return E, False
    cost = cost_of(E)
    T0 = max(1.0, 0.02 * cost)
    T_end = 0.3
    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = T0 * (T_end / T0) ** (it / max(1, iters))
        i = rng.randrange(len(E))
        j = rng.randrange(len(E))
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        if (a1, b2) in es or (a2, b1) in es:
            continue
        E[i] = (a1, b2)
        E[j] = (a2, b1)
        c2 = cost_of(E)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            es.discard((a1, b1))
            es.discard((a2, b2))
            es.add((a1, b2))
            es.add((a2, b1))
            cost = c2
        else:
            E[i] = (a1, b1)
            E[j] = (a2, b2)
    return E, cost == 0


def _repair_grow(d, D, K, E, rng, deadline, consider):
    """Repeatedly grow by one vertex pair and repair; every success is offered to consider()."""
    while time.monotonic() < deadline:
        grown = _grow_pair(K, E, d, rng)
        if grown is None:
            return
        K2, E2 = grown
        E3, ok = _repair(K2, E2, d, D, rng, deadline, 2500)
        if ok:
            K, E = K2, E3
            consider(2 * K, [(a, K + b) for a, b in E])


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

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
            best = (n, list(e))
            best_n = n

    try:
        if D >= 3:
            pg = _best_pg(d)
            if pg is not None:
                consider(pg[0], pg[1])

        moore = lib._moore_bound(d, D)

        # Phase 1: annealed group lifts, to obtain a strong seed.
        lift_deadline = start + 0.4 * time_limit
        if best_n < moore:
            ks = [1, 1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
            iters = 1500 if D >= 5 else 400
            while time.monotonic() < lift_deadline and best_n < moore:
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
                res = _anneal(d, D, k, order, mul, rng, lift_deadline, iters)
                if res is not None:
                    consider(res[0], res[1])

        # Phase 2 (new): grow the best d-regular balanced bipartite graph and repair it.
        if best_n < moore and time.monotonic() < deadline:
            reg = _regular_halves(best_n, best[1], d)
            if reg is not None:
                K, E = reg
                _repair_grow(d, D, K, E, rng, deadline, consider)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
