import itertools
import math
import random
import time

import lib

_BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Bases: generalized quadrangle W(q) (diameter 4), built from PG(3, q).
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and totally isotropic lines of W(q); 4-regular for q = 3."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))
    edges = [(p, P + j) for j, L in enumerate(lines) for p in L]
    return 2 * P, edges


# ----------------------------------------------------------------------------
# Repair-growth family: keep a valid bipartite graph of max degree d, add two
# new vertices by a degree-preserving rewiring, then anneal the number of
# vertex pairs at distance > D down to zero with degree-preserving double swaps.
# ----------------------------------------------------------------------------

def _bip_color(n, edges):
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
    return color


def _orient(col, edges):
    """Orient every edge as (A-side, B-side) according to the 2-colouring."""
    return [(u, v) if col[u] == 0 else (v, u) for u, v in edges]


def _bad(n, E, D):
    """Number of unordered vertex pairs at distance > D (bitset BFS)."""
    adj = [[] for _ in range(n)]
    for a, b in E:
        adj[a].append(b)
        adj[b].append(a)
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


def _repair(n, E, D, deadline, rng, iters):
    """Annealed degree-preserving double swaps; returns a valid edge list or None."""
    E = list(E)
    eset = set(E)
    cost = _bad(n, E, D)
    for it in range(iters):
        if cost == 0:
            break
        if (it & 31) == 0 and time.monotonic() > deadline:
            break
        T = 0.6 * (1.0 - it / iters) + 0.05
        i = rng.randrange(len(E))
        j = rng.randrange(len(E))
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        if (a1, b2) in eset or (a2, b1) in eset:
            continue
        E[i] = (a1, b2)
        E[j] = (a2, b1)
        eset.discard((a1, b1))
        eset.discard((a2, b2))
        eset.add((a1, b2))
        eset.add((a2, b1))
        c2 = _bad(n, E, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
        else:
            E[i] = (a1, b1)
            E[j] = (a2, b2)
            eset.discard((a1, b2))
            eset.discard((a2, b1))
            eset.add((a1, b1))
            eset.add((a2, b2))
    return list(E) if cost == 0 else None


def _grow_once(n, E, d, col, rng):
    """Add two vertices a (side A) and b (side B), each of degree d, by rewiring d-1 edges."""
    m = len(E)
    if d < 2 or m < d - 1:
        return None
    idx, xs, ys = None, None, None
    for _ in range(200):
        idx = rng.sample(range(m), d - 1)
        xs = [E[i][0] for i in idx]
        ys = [E[i][1] for i in idx]
        if len(set(xs)) == d - 1 and len(set(ys)) == d - 1:
            break
    else:
        return None
    rem = set(idx)
    a, b = n, n + 1
    newE = [E[i] for i in range(m) if i not in rem]
    newE.extend((a, y) for y in ys)
    newE.extend((x, b) for x in xs)
    newE.append((a, b))
    return n + 2, newE, col + [0, 1]


# ----------------------------------------------------------------------------
# Bi-Cayley voltage lifts over Z_m x| Z_k2 (annealed), as a second family.
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    for _ in range(80):
        k2 = rng.choice([1, 1, 2, 3, 4, 5, 6])
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


def _lift_cost(k, G, D, darts, perms):
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            a = i * G + g
            b = (k + j) * G + pm[g]
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


def _lift_anneal(d, D, k, G, mul, rng, deadline, iters):
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [[mul(g, s) for g in range(G)] for _, _, s in darts]
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
            old_p = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = [mul(g, new_s) for g in range(G)]
            c2 = _lift_cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_p
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

def build(d, D, seed, time_limit):
    start = time.monotonic()
    end = start + 0.85 * time_limit
    phase1_end = start + 0.3 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and degree d.
    best_n, best_e = lib.haar_graph(d, range(d))
    if D <= 2:
        return best_n, best_e

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    try:
        # Phase 1a: fixed constructions.
        q = d - 1
        if q >= 2 and lib.is_prime_power(q):
            consider(*lib.projective_plane_incidence(q))
            if q <= 5:
                consider(*_gq_w(q))
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(*lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass

        # Phase 1b: annealed group lifts.
        ks = [1, 1, 2, 2, 3]
        while time.monotonic() < phase1_end:
            k = rng.choice(ks)
            base = best_n // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, 3))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _lift_anneal(d, D, k, order, mul, rng, phase1_end, 1500)
            if res is not None:
                consider(res[0], res[1])

        # Phase 2: repair-growth from the best valid graph found so far.
        cur_n, cur_e = best_n, list(best_e)
        col = _bip_color(cur_n, cur_e)
        E = _orient(col, cur_e)
        while time.monotonic() < end:
            g = _grow_once(cur_n, E, d, col, rng)
            if g is None:
                break
            n2, E2, col2 = g
            res = _repair(n2, E2, D, end, rng, 3000)
            if res is not None:
                cur_n, E, col = n2, res, col2
                consider(n2, res)
    except Exception:
        pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, best_e
