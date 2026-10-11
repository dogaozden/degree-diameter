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
# Bi-Cayley voltage lifts over semidirect products Z_m x| Z_k, annealed.
#
# Vertices: A_i,g = i*G + g  and  B_j,h = (k+j)*G + h.
# Dart (i, j, s) joins A_i,g to B_j,mul(g,s) for every g in the group.
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
    """Permutation g -> mul(g, s) of the group."""
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
# NEW: split-insertion growth followed by 2-switch annealing on bad pairs.
#
# Insertion: pick d edges (a_i, b_i) with distinct endpoints, delete them,
# add a new A-vertex x joined to every b_i and a new B-vertex y joined to every a_i.
# Every degree stays at most d, the graph stays bipartite, and the order grows by 2.
#
# Repair: 2-switches (a1,b1),(a2,b2) -> (a1,b2),(a2,b1) keep every degree and the
# bipartition, so annealing on lib.bad_pairs can repair the diameter without
# breaking the degree bound.
# ----------------------------------------------------------------------------

def _bipartition(n, adj):
    """Two-colouring of a bipartite graph given by adjacency lists."""
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
    return color


def _split_insert(n, edges, d, rng):
    """Return (n+2, oriented edge list (a, b) with a on side 0) after split insertion, or None."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    color = _bipartition(n, adj)
    E = [(u, v) if color[u] == 0 else (v, u) for u, v in edges]
    order = list(range(len(E)))
    rng.shuffle(order)
    picked = []
    As, Bs = set(), set()
    for i in order:
        a, b = E[i]
        if a in As or b in Bs:
            continue
        picked.append(i)
        As.add(a)
        Bs.add(b)
        if len(picked) == d:
            break
    if len(picked) < d:
        return None
    x, y = n, n + 1
    ps = set(picked)
    out = [e for i, e in enumerate(E) if i not in ps]
    for i in picked:
        a, b = E[i]
        out.append((x, b))
        out.append((a, y))
    return n + 2, out


def _switch_anneal(n, E, D, rng, deadline, T0, T1):
    """Anneal 2-switches on an oriented bipartite edge list until bad_pairs == 0; None on timeout."""
    E = list(E)
    S = set(E)
    M = len(E)
    cost = lib.bad_pairs(n, E, D)
    t0 = time.monotonic()
    span = max(1e-6, deadline - t0)
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        T = T0 * (T1 / T0) ** min(1.0, (now - t0) / span)
        i = rng.randrange(M)
        j = rng.randrange(M)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        n1 = (a1, b2)
        n2 = (a2, b1)
        if n1 in S or n2 in S:
            continue
        E[i] = n1
        E[j] = n2
        c2 = lib.bad_pairs(n, E, D)
        if c2 <= cost or rng.random() < math.exp((cost - c2) / T):
            S.discard((a1, b1))
            S.discard((a2, b2))
            S.add(n1)
            S.add(n2)
            cost = c2
        else:
            E[i] = (a1, b1)
            E[j] = (a2, b2)
    return E if cost == 0 else None


def _grow_by_switch(n, edges, d, D, rng, deadline, chunk):
    """Repeatedly insert a vertex pair and repair by switching; returns the largest valid graph reached."""
    cur_n, cur_e = n, list(edges)
    while time.monotonic() < deadline:
        ins = _split_insert(cur_n, cur_e, d, rng)
        if ins is None:
            break
        N2, E2 = ins
        end = min(deadline, time.monotonic() + chunk)
        res = _switch_anneal(N2, E2, D, rng, end, 1.0, 0.1)
        if res is not None:
            cur_n, cur_e = N2, res
    return cur_n, cur_e


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d}: diameter 2, optimal for D = 2 and a safe fallback.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

    pg = _best_pg(d) if D >= 3 else None
    if pg is not None:
        consider(pg[0], pg[1])
    if D == 3 and lib.is_prime_power(d - 1):
        # PG(2, d-1) meets the Moore bound: nothing better exists.
        return best

    # Phase A: annealed group voltage lifts.
    ks = [1, 1, 2, 2, 3, 4]
    phase_a_end = start + 0.4 * time_limit
    while time.monotonic() < phase_a_end:
        k = rng.choice(ks)
        base = best_n // (2 * k)
        G = max(2, base + 1 + rng.randrange(0, 3))
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        res = _anneal(d, D, k, order, mul, rng, phase_a_end, iters=1500)
        if res is not None:
            consider(res[0], res[1])

    # Phase B: split-insertion growth with switch repair, starting from the best graph.
    if D >= 4 and best_n > 0:
        chunk = max(2.0, 0.06 * time_limit)
        n2, e2 = _grow_by_switch(best[0], best[1], d, D, rng, deadline, chunk)
        consider(n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
