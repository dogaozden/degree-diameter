import math
import random
import time

import lib


_BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Base graphs.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo & Lopez record graph for degree d when q = d-2 is a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


def _bipartition(n, adj):
    """Two-colouring of a bipartite graph given by adjacency collections."""
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


# ----------------------------------------------------------------------------
# Bi-Cayley voltage lifts over semidirect products Z_m x| Z_k2 (annealed).
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
            if delta <= 0 or rng.random() < math.exp(-min(50.0, delta / T)):
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
            if delta <= 0 or rng.random() < math.exp(-min(50.0, delta / T)):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _edges(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# NEW: matching-split expansion followed by degree-preserving edge-switch annealing.
#
# Expansion: pick a matching M of size d in the current graph and delete it.
# Add two vertices x (side A) and y (side B). Join x to the B-ends of M and y to
# the A-ends of M. Every degree is unchanged, so the result is still max degree d
# and bipartite, with two more vertices. Diameter is usually broken, so the new
# graph is repaired by switches: take edges (a,b),(c,e) with a,c in A and b,e in B
# and replace them by (a,e),(c,b). Switches keep all degrees and bipartiteness,
# and the cost is the number of vertex pairs at distance > D.
# ----------------------------------------------------------------------------

def _bad_count(n, adj, D):
    """Number of unordered vertex pairs at distance > D (unreachable pairs count)."""
    ball = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new.append(x)
        ball = new
    return sum(n - b.bit_count() for b in ball) // 2


def _expand_pair(n, edges, d, rng):
    """Matching-split expansion by two vertices; returns (n2, E, adj) or None."""
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    color = _bipartition(n, adj)
    E = [((u, v) if color[u] == 0 else (v, u)) for u, v in edges]
    order = list(range(len(E)))
    rng.shuffle(order)
    used = set()
    match = []
    for idx in order:
        a, b = E[idx]
        if a in used or b in used:
            continue
        used.add(a)
        used.add(b)
        match.append(idx)
        if len(match) == d:
            break
    if len(match) < d:
        return None
    mset = set(match)
    E2 = [E[i] for i in range(len(E)) if i not in mset]
    adj.append(set())
    adj.append(set())
    x, y = n, n + 1
    for idx in match:
        a, b = E[idx]
        adj[a].discard(b)
        adj[b].discard(a)
        E2.append((a, y))
        adj[a].add(y)
        adj[y].add(a)
        E2.append((x, b))
        adj[x].add(b)
        adj[b].add(x)
    return n + 2, E2, adj


def _switch_anneal(n, E, adj, D, rng, deadline, iters):
    """Repair an expanded graph by degree-preserving switches; returns edge list or None."""
    E = [[a, b] for a, b in E]
    S = set((a, b) for a, b in E)
    m = len(E)
    cost = _bad_count(n, adj, D)
    if cost == 0:
        return [tuple(e) for e in E]
    T0 = max(1.0, 0.1 * cost)
    T_end = 0.05
    iters = max(1, iters)
    decay = (T_end / T0) ** (1.0 / iters) if T0 > T_end else 1.0
    T = T0
    for it in range(iters):
        if cost == 0:
            break
        if (it & 31) == 0 and time.monotonic() > deadline:
            break
        T = max(T_end, T * decay)
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a, b = E[i]
        c, e = E[j]
        if a == c or b == e or (a, e) in S or (c, b) in S:
            continue
        adj[a].discard(b)
        adj[b].discard(a)
        adj[c].discard(e)
        adj[e].discard(c)
        adj[a].add(e)
        adj[e].add(a)
        adj[c].add(b)
        adj[b].add(c)
        c2 = _bad_count(n, adj, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-min(50.0, delta / T)):
            cost = c2
            S.discard((a, b))
            S.discard((c, e))
            S.add((a, e))
            S.add((c, b))
            E[i] = [a, e]
            E[j] = [c, b]
        else:
            adj[a].discard(e)
            adj[e].discard(a)
            adj[c].discard(b)
            adj[b].discard(c)
            adj[a].add(b)
            adj[b].add(a)
            adj[c].add(e)
            adj[e].add(c)
    if cost == 0:
        return [tuple(e) for e in E]
    return None


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    moore = lib._moore_bound(d, D)

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
            ap = _araujo(d)
            if ap is not None:
                consider(ap[0], ap[1])

        if D >= 3 and best_n < moore:
            # Phase A: annealed bi-Cayley lifts, group order targeted just above best_n.
            phase_a_end = start + 0.5 * time_limit
            ks = [1, 1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
            while time.monotonic() < phase_a_end and best_n < moore:
                k = rng.choice(ks)
                base = best_n // (2 * k)
                G = max(2, base + 1 + rng.randrange(0, 3))
                g = _sample_group(G, rng)
                if g is None:
                    continue
                order, mul = g
                res = _anneal(d, D, k, order, mul, rng, phase_a_end, 1500)
                if res is not None:
                    consider(res[0], res[1])

            # Phase B: repeated matching-split expansion + switch repair from the best graph.
            fails = 0
            while time.monotonic() < deadline and best_n < moore and fails < 200:
                cand = _expand_pair(best_n, best[1], d, rng)
                if cand is None:
                    fails += 1
                    continue
                n2, E2, adj2 = cand
                res = _switch_anneal(n2, E2, adj2, D, rng, deadline, 4000)
                if res is not None:
                    before = best_n
                    consider(n2, res)
                    if best_n > before:
                        fails = 0
                        continue
                fails += 1
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
