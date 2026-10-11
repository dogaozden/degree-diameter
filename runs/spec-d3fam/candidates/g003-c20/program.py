import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Helpers shared by all paths.
# ----------------------------------------------------------------------------

def _colour(n, E):
    """Two-colouring of the graph given by edge list E (bipartite input assumed)."""
    adj = [[] for _ in range(n)]
    for u, v in E:
        adj[u].append(v)
        adj[v].append(u)
    col = [-1] * n
    for s in range(n):
        if col[s] != -1:
            continue
        col[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if col[v] == -1:
                    col[v] = 1 - col[u]
                    stack.append(v)
    return col


def _bad(n, E):
    """Number of ordered (vertex, vertex) pairs at distance > 3 (zero means diameter <= 3)."""
    adj = [[] for _ in range(n)]
    for a, b in E:
        adj[a].append(b)
        adj[b].append(a)
    r = [1 << v for v in range(n)]
    for _ in range(3):
        nr = []
        for v in range(n):
            x = r[v]
            for u in adj[v]:
                x |= r[u]
            nr.append(x)
        r = nr
    return sum(n - x.bit_count() for x in r)


# ----------------------------------------------------------------------------
# NEW: bipartite "pair insertion + 2-switch annealing" growth for D = 3.
#
# Given a valid graph, pick a matching M of d-1 edges (a_i, b_i), delete it,
# and add two new vertices x (side 0) and y (side 1) with x ~ b_i for all i,
# y ~ a_i for all i, and x ~ y. Degrees stay <= d and the graph grows by 2.
# The diameter is then repaired by annealing over degree-preserving 2-switches
# (a1,b1),(a2,b2) -> (a1,b2),(a2,b1), minimizing the number of far pairs.
# ----------------------------------------------------------------------------

def _try_add_pair(n, E, d, deadline, rng):
    col = _colour(n, E)
    E2 = [(u, v) if col[u] == 0 else (v, u) for u, v in E]
    order = list(range(len(E2)))
    rng.shuffle(order)
    usedA, usedB, M = set(), set(), []
    for i in order:
        a, b = E2[i]
        if a in usedA or b in usedB:
            continue
        usedA.add(a)
        usedB.add(b)
        M.append(i)
        if len(M) == d - 1:
            break
    if len(M) < d - 1:
        return None

    x, y = n, n + 1
    Mset = set(M)
    E_list = [E2[i] for i in range(len(E2)) if i not in Mset]
    for i in M:
        a, b = E2[i]
        E_list.append((x, b))
        E_list.append((a, y))
    E_list.append((x, y))
    N = n + 2

    pset = set(E_list)
    cost = _bad(N, E_list)
    if cost == 0:
        return N, E_list

    L = len(E_list)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    T0 = max(1.0, 0.03 * cost)
    T1 = 0.15
    while cost > 0 and time.monotonic() < deadline:
        frac = (time.monotonic() - t0) / span
        T = T0 * (T1 / T0) ** frac
        i = rng.randrange(L)
        j = rng.randrange(L)
        if i == j:
            continue
        a1, b1 = E_list[i]
        a2, b2 = E_list[j]
        if a1 == a2 or b1 == b2:
            continue
        if (a1, b2) in pset or (a2, b1) in pset:
            continue
        E_list[i] = (a1, b2)
        E_list[j] = (a2, b1)
        c2 = _bad(N, E_list)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            pset.discard((a1, b1))
            pset.discard((a2, b2))
            pset.add((a1, b2))
            pset.add((a2, b1))
            cost = c2
        else:
            E_list[i] = (a1, b1)
            E_list[j] = (a2, b2)
    if cost == 0:
        return N, E_list
    return None


def _grow_d3(n, E, d, deadline, rng):
    """Repeatedly insert vertex pairs while the annealing succeeds."""
    best = (n, E)
    while time.monotonic() < deadline - 1.0:
        rd = min(deadline, time.monotonic() + 12.0)
        res = _try_add_pair(best[0], best[1], d, rd, rng)
        if res is not None and lib.is_valid(res[0], res[1], d, 3):
            best = res
    return best


def _base_d3(d):
    """Moore-optimal or record-like diameter-3 base graph for degree d."""
    if d - 1 >= 2 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)
    if d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            return lib.araujo_lopez_graph(d - 2)
        except ValueError:
            pass
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley voltage lifts over semidirect products (non-D=3 cases).
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


def _cost(k, G, D, darts, perms):
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
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d} has diameter 2 and is valid for every D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(res):
        nonlocal best
        if res is not None and res[0] > best[0] and lib.is_valid(res[0], res[1], d, D):
            best = res

    if D == 2:
        return best

    if D == 3:
        base = _base_d3(d)
        if base is None:
            return best
        consider(base)
        # Moore-optimal case: no growth is possible beyond PG(2, d-1).
        if d - 1 >= 2 and lib.is_prime_power(d - 1):
            return best
        grown = _grow_d3(best[0], best[1], d, deadline, rng)
        consider(grown)
        return best

    # D >= 4: annealed group voltage lifts.
    ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
    while time.monotonic() < deadline:
        k = rng.choice(ks)
        base_n = best[0] // (2 * k)
        G = max(2, base_n + 1 + rng.randrange(0, max(3, base_n // 8 + 1)))
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        res = _anneal(d, D, k, order, mul, rng, deadline, iters=400)
        if res is not None:
            consider(res)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
