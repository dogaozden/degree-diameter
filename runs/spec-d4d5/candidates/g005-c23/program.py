import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective plane base (diameter 3).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Return (q, (n, edges)) for the incidence graph of PG(2, q), q the largest prime power with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return q, lib.projective_plane_incidence(q)
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
# NEW: splice-and-switch growth for d-regular bipartite graphs.
#
# Splice: pick d pairwise disjoint A-B edges (x_i, y_i), delete them, and add a
# new A-vertex a adjacent to all y_i and a new B-vertex b adjacent to all x_i.
# Every old vertex keeps its degree and the graph stays d-regular and bipartite,
# but distances change. Repair by degree-preserving double-edge switches
# (a1,b1),(a2,b2) -> (a1,b2),(a2,b1), annealing the bad-pair count. Bad pairs
# are counted with bitmask balls, which is cheap at these sizes.
# ----------------------------------------------------------------------------

def _bipartition(n, adj):
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


def _bad_pairs_adj(n, adj, D):
    """Number of unordered pairs at distance > D, from adjacency lists (bitmask balls)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _splice(n, E, color, d, rng):
    """Add one A-vertex and one B-vertex of degree d by splicing d disjoint A-B edges."""
    order = list(range(len(E)))
    rng.shuffle(order)
    usedA, usedB, chosen = set(), set(), []
    for idx in order:
        x, y = E[idx]
        if x in usedA or y in usedB:
            continue
        usedA.add(x)
        usedB.add(y)
        chosen.append(idx)
        if len(chosen) == d:
            break
    if len(chosen) < d:
        return None
    cs = set(chosen)
    a_new, b_new = n, n + 1
    newE = [E[i] for i in range(len(E)) if i not in cs]
    for idx in chosen:
        x, y = E[idx]
        newE.append((a_new, y))
        newE.append((x, b_new))
    return n + 2, newE, color + [0, 1]


def _switch_anneal(n, E, D, rng, deadline, T0=1.5, T1=0.05):
    """Anneal degree-preserving bipartite switches to drive the bad-pair count to zero.

    E is a list of [a, b] pairs with a on side A. Returns (E, cost).
    """
    E = [list(e) for e in E]
    adj = [[] for _ in range(n)]
    keys = set()
    for a, b in E:
        adj[a].append(b)
        adj[b].append(a)
        keys.add((a, b))
    cost = _bad_pairs_adj(n, adj, D)
    m = len(E)
    start = time.monotonic()
    span = max(1e-3, deadline - start)
    while cost > 0 and m >= 2:
        now = time.monotonic()
        if now >= deadline:
            break
        T = T0 * (T1 / T0) ** min(1.0, (now - start) / span)
        i = rng.randrange(m)
        j = rng.randrange(m)
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        if (a1, b2) in keys or (a2, b1) in keys:
            continue
        adj[a1].remove(b1)
        adj[b1].remove(a1)
        adj[a2].remove(b2)
        adj[b2].remove(a2)
        adj[a1].append(b2)
        adj[b2].append(a1)
        adj[a2].append(b1)
        adj[b1].append(a2)
        new = _bad_pairs_adj(n, adj, D)
        delta = new - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            keys.discard((a1, b1))
            keys.discard((a2, b2))
            keys.add((a1, b2))
            keys.add((a2, b1))
            E[i] = [a1, b2]
            E[j] = [a2, b1]
            cost = new
        else:
            adj[a1].remove(b2)
            adj[b2].remove(a1)
            adj[a2].remove(b1)
            adj[b1].remove(a2)
            adj[a1].append(b1)
            adj[b1].append(a1)
            adj[a2].append(b2)
            adj[b2].append(a2)
    return E, cost


def _splice_grow(n, edges, d, D, deadline, rng):
    """Repeatedly splice-and-repair a d-regular bipartite graph; return the largest (n, edges) reached."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    if any(len(a) != d for a in adj):
        return n, edges
    color = _bipartition(n, adj)
    E = [(u, v) if color[u] == 0 else (v, u) for u, v in edges]
    cur_n, cur_E, cur_c = n, E, color
    while time.monotonic() < deadline:
        spl = _splice(cur_n, cur_E, cur_c, d, rng)
        if spl is None:
            break
        n1, E1, c1 = spl
        remaining = deadline - time.monotonic()
        budget = max(1.0, min(6.0, remaining))
        E2, cost = _switch_anneal(n1, E1, D, rng, time.monotonic() + budget)
        if cost == 0:
            cur_n, cur_E, cur_c = n1, [(a, b) for a, b in E2], c1
    return cur_n, [(int(a), int(b)) for a, b in cur_E]


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))
    if D == 2:
        return best_n, best_e

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    # Projective plane base (diameter 3). Calibration case returns immediately.
    pg = _best_pg(d)
    if pg is not None:
        q, (n_pg, e_pg) = pg
        consider(n_pg, e_pg)
        if D == 3 and q + 1 == d:
            return best_n, best_e

    # Phase 1: annealed bi-Cayley lifts to get a strong d-regular base.
    lift_deadline = start + 0.4 * (deadline - start)
    ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
    while time.monotonic() < lift_deadline:
        k = rng.choice(ks)
        base = best_n // (2 * k)
        G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        res = _anneal(d, D, k, order, mul, rng, lift_deadline, iters=400)
        if res is not None:
            consider(res[0], res[1])

    # Phase 2 (new): splice-and-switch growth from the best d-regular graph.
    if time.monotonic() < deadline:
        n2, e2 = _splice_grow(best_n, best_e, d, D, deadline, rng)
        consider(n2, e2)

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, best_e
