import math
import random
import time

import lib

_BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Baseline: projective plane and annealed bi-Cayley voltage lifts.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


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
    """Number of (representative, vertex) pairs at distance > D. Zero means valid."""
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
# New construction: grow-and-repair annealing on bipartite graphs.
#
# Keep a valid bipartite graph with sides A (size NA) and B (size NB) and max
# degree d. Add one vertex to each side (isolated, so the diameter is violated),
# then anneal over edge moves (2-switch, endpoint rewire, add, remove) that
# minimise the number of vertex pairs at distance > D. Success gives a valid
# graph two vertices larger. Repeat until time runs out.
# ----------------------------------------------------------------------------

def _to_sides(n, edges):
    """Return (NA, NB, adjA, adjB) for a bipartite graph, or None if not bipartite."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
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
    ia = {v: i for i, v in enumerate(A)}
    ib = {v: i for i, v in enumerate(B)}
    adjA = [set() for _ in A]
    adjB = [set() for _ in B]
    for u, v in edges:
        if color[u] == 1:
            u, v = v, u
        adjA[ia[u]].add(ib[v])
        adjB[ib[v]].add(ia[u])
    return len(A), len(B), adjA, adjB


def _from_sides(NA, NB, adjA, adjB):
    n = NA + NB
    edges = [(a, NA + b) for a in range(NA) for b in adjA[a]]
    return n, edges


def _bad_ab(NA, NB, adjA, adjB, D):
    """Number of unordered vertex pairs at distance > D (unreachable pairs included)."""
    n = NA + NB
    adj = [None] * n
    for a in range(NA):
        adj[a] = [NA + b for b in adjA[a]]
    for b in range(NB):
        adj[NA + b] = list(adjB[b])
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


def _apply(adjA, adjB, op, a, b):
    if op == 0:
        adjA[a].discard(b)
        adjB[b].discard(a)
    else:
        adjA[a].add(b)
        adjB[b].add(a)


def _repair(d, D, NA, NB, adjA, adjB, rng, deadline, max_iters):
    """Anneal edge moves until the graph has diameter <= D. Modifies adjA/adjB in place."""
    c = _bad_ab(NA, NB, adjA, adjB, D)
    T = 0.6
    for it in range(max_iters):
        if c == 0:
            return True
        if (it & 31) == 0 and time.monotonic() >= deadline:
            return False
        r = rng.random()
        if r < 0.6:
            # 2-switch: keeps all degrees.
            a1 = rng.randrange(NA)
            if not adjA[a1]:
                continue
            b1 = rng.choice(tuple(adjA[a1]))
            a2 = rng.randrange(NA)
            if not adjA[a2]:
                continue
            b2 = rng.choice(tuple(adjA[a2]))
            if a1 == a2 or b1 == b2 or b2 in adjA[a1] or b1 in adjA[a2]:
                continue
            ops = [(0, a1, b1), (0, a2, b2), (1, a1, b2), (1, a2, b1)]
        elif r < 0.85:
            # Rewire one endpoint of an edge to a B vertex with spare degree.
            a1 = rng.randrange(NA)
            if not adjA[a1]:
                continue
            b1 = rng.choice(tuple(adjA[a1]))
            cand = [b for b in range(NB) if len(adjB[b]) < d and b not in adjA[a1]]
            if not cand:
                continue
            ops = [(0, a1, b1), (1, a1, rng.choice(cand))]
        else:
            # Add an edge between deficient vertices (never increases the cost).
            defA = [a for a in range(NA) if len(adjA[a]) < d]
            defB = [b for b in range(NB) if len(adjB[b]) < d]
            if not defA or not defB:
                continue
            a = rng.choice(defA)
            b = rng.choice(defB)
            if b in adjA[a]:
                continue
            ops = [(1, a, b)]

        for op, a, b in ops:
            _apply(adjA, adjB, op, a, b)
        c2 = _bad_ab(NA, NB, adjA, adjB, D)
        delta = c2 - c
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            c = c2
        else:
            for op, a, b in reversed(ops):
                _apply(adjA, adjB, 1 - op, a, b)
        T = max(0.12, T * 0.9997)
    return c == 0


def _grow_repair(d, D, state, rng, deadline):
    """Repeatedly add one vertex per side and repair. Returns the largest valid state found."""
    best = state
    while time.monotonic() < deadline:
        bNA, bNB, bA, bB = best
        A = [set(s) for s in bA]
        B = [set(s) for s in bB]
        A.append(set())
        B.append(set())
        if _repair(d, D, bNA + 1, bNB + 1, A, B, rng, deadline, 4000):
            best = (bNA + 1, bNB + 1, A, B)
    return best


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
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

        # Baseline: annealed voltage lifts over semidirect products.
        lift_end = start + (0.4 if D >= 5 else 0.5) * time_limit
        if D >= 5:
            ks = [1, 1, 2, 2, 3, 4]
            anneal_iters = 1500
        else:
            ks = [1, 1, 2, 3]
            anneal_iters = 400
        while time.monotonic() < lift_end:
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
            res = _anneal_lift(d, D, k, order, mul, rng, lift_end, anneal_iters)
            if res is not None:
                consider(res[0], res[1])

        # New family: grow-and-repair annealing from the best valid graph so far.
        grow_end = start + 0.85 * time_limit
        st = _to_sides(best[0], best[1])
        if st is not None:
            NA, NB, adjA, adjB = st
            res_state = _grow_repair(d, D, (NA, NB, adjA, adjB), rng, grow_end)
            n2, e2 = _from_sides(*res_state)
            consider(n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
