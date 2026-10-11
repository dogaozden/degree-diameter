import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base family: incidence graph of PG(2, q), q the largest prime power with q+1 <= d.
# ----------------------------------------------------------------------------

def _best_pg(d):
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _color(n, adj):
    """Two-colouring by BFS; adj is a list of neighbour lists or sets."""
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
# Family A: annealed bi-Cayley voltage lifts over Z_m x| Z_k2.
# Vertices: A_i,g = i*G + g and B_j,h = (k+j)*G + h.
# Dart (i, j, s) joins A_i,g to B_j,mul(g,s) for every g.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _sample_group(G, rng):
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
# Family B (new, high-risk): unstructured repair annealing.
# Start from a valid graph, add one A and one B vertex, then anneal over
# bipartite edge moves (add, remove, switch, rewire), minimising the number of
# vertex pairs at distance > D. Degree stays <= d throughout. Any zero-cost
# state is a valid graph strictly larger than the start.
# ----------------------------------------------------------------------------

def _bad_pairs_sets(N, adj, D):
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


def _repair(n, edges, d, D, rng, deadline, iters):
    base_adj = [[] for _ in range(n)]
    for u, v in edges:
        base_adj[u].append(v)
        base_adj[v].append(u)
    col = _color(n, base_adj) + [0, 1]
    N = n + 2

    adj = [set() for _ in range(N)]
    el = []
    pos = {}

    def _rm(e):
        i = pos.pop(e)
        last = el.pop()
        if last != e:
            el[i] = last
            pos[last] = i
        adj[e[0]].discard(e[1])
        adj[e[1]].discard(e[0])

    def _add(e):
        pos[e] = len(el)
        el.append(e)
        adj[e[0]].add(e[1])
        adj[e[1]].add(e[0])

    for u, v in edges:
        a, b = (u, v) if col[u] == 0 else (v, u)
        _add((a, b))

    sideA = [v for v in range(N) if col[v] == 0]
    sideB = [v for v in range(N) if col[v] == 1]

    def _apply(rem, addl):
        for e in rem:
            if e not in pos:
                return False
        for e in rem:
            _rm(e)
        inc = {}
        seen = set()
        ok = True
        for a, b in addl:
            if a == b or (a, b) in pos or (a, b) in seen:
                ok = False
                break
            seen.add((a, b))
            inc[a] = inc.get(a, 0) + 1
            inc[b] = inc.get(b, 0) + 1
        if ok:
            for v, c in inc.items():
                if len(adj[v]) + c > d:
                    ok = False
                    break
        if not ok:
            for e in rem:
                _add(e)
            return False
        for e in addl:
            _add(e)
        return True

    cost = _bad_pairs_sets(N, adj, D)
    T = 3.0
    T_end = 0.3
    decay = (T_end / T) ** (1.0 / max(1, iters))

    for it in range(iters):
        if cost == 0:
            break
        if (it & 31) == 0 and time.monotonic() > deadline:
            break
        T = max(T_end, T * decay)
        r = rng.random()
        rem, addl = [], []
        if r < 0.3 and len(el) >= 2:
            e1 = el[rng.randrange(len(el))]
            e2 = el[rng.randrange(len(el))]
            if e1 == e2 or e1[0] == e2[0] or e1[1] == e2[1]:
                continue
            rem = [e1, e2]
            addl = [(e1[0], e2[1]), (e2[0], e1[1])]
        elif r < 0.5:
            addl = [(rng.choice(sideA), rng.choice(sideB))]
        elif r < 0.65:
            if not el:
                continue
            rem = [el[rng.randrange(len(el))]]
        else:
            if not el:
                continue
            e = el[rng.randrange(len(el))]
            b2 = rng.choice(sideB)
            rem = [e]
            addl = [(e[0], b2)]

        if not _apply(rem, addl):
            continue
        c2 = _bad_pairs_sets(N, adj, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
        else:
            _apply(addl, rem)

    if cost == 0:
        return N, [(int(a), int(b)) for a, b in el]
    return None


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
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

    # Early exit when the Moore bound is already met.
    if best_n >= lib._moore_bound(d, D):
        return best

    final_end = start + 0.85 * time_limit
    if D >= 5:
        lift_end = start + 0.5 * time_limit
    else:
        lift_end = start + 0.6 * time_limit

    # Phase 1: annealed group voltage lifts.
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
        res = _anneal_lift(d, D, k, order, mul, rng, lift_end, iters=anneal_iters)
        if res is not None:
            consider(res[0], res[1])

    # Phase 2: unstructured repair annealing, growing from the current best.
    while time.monotonic() < final_end:
        res = _repair(best_n, best[1], d, D, rng, final_end, iters=6000)
        if res is not None:
            consider(res[0], res[1])
        else:
            if time.monotonic() >= final_end:
                break

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
