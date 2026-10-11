import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Finite groups given by multiplication tables (non-abelian, not semidirect
# products of cyclic groups, so they are a different family from the parent).
# ----------------------------------------------------------------------------

def _perm_group_table(n, even_only):
    """Multiplication table of S_n (or A_n) acting on range(n)."""
    elems = list(itertools.permutations(range(n)))
    if even_only:
        def parity(p):
            inv = sum(1 for i in range(n) for j in range(i + 1, n) if p[i] > p[j])
            return inv & 1
        elems = [p for p in elems if parity(p) == 0]
    index = {p: i for i, p in enumerate(elems)}
    return [[index[tuple(a[b[x]] for x in range(n))] for b in elems] for a in elems]


def _matrix_group_table(p, special):
    """Multiplication table of SL(2,p) (special=True) or GL(2,p) for prime p."""
    elems = []
    for a, b, c, d in itertools.product(range(p), repeat=4):
        det = (a * d - b * c) % p
        if (special and det == 1) or (not special and det != 0):
            elems.append((a, b, c, d))
    index = {e: i for i, e in enumerate(elems)}

    def mul(x, y):
        a, b, c, d = x
        e, f, g, h = y
        return ((a * e + b * g) % p, (a * f + b * h) % p,
                (c * e + d * g) % p, (c * f + d * h) % p)

    return [[index[mul(x, y)] for y in elems] for x in elems]


def _affine_group_table(q):
    """Multiplication table of AGL(1,q) = {x -> a x + b}, q prime."""
    elems = [(a, b) for a in range(1, q) for b in range(q)]
    index = {e: i for i, e in enumerate(elems)}
    # (a,b)*(c,e): x -> a(cx+e)+b = (ac) x + (ae+b)
    return [[index[((a * c) % q, (a * e + b) % q)] for (c, e) in elems]
            for (a, b) in elems]


def _group_library():
    """Tables for a handful of non-abelian groups with order in [20, 400]."""
    specs = [
        lambda: _perm_group_table(5, False),   # S5, 120
        lambda: _perm_group_table(5, True),    # A5, 60
        lambda: _perm_group_table(4, False),   # S4, 24
        lambda: _matrix_group_table(3, True),  # SL(2,3), 24
        lambda: _matrix_group_table(3, False), # GL(2,3), 48
        lambda: _matrix_group_table(5, True),  # SL(2,5), 120
        lambda: _matrix_group_table(7, True),  # SL(2,7), 336
    ]
    specs += [lambda q=q: _affine_group_table(q) for q in (7, 11, 13, 17)]
    out = []
    for f in specs:
        table = f()
        if 20 <= len(table) <= 400:
            out.append(table)
    return out


# ----------------------------------------------------------------------------
# Bipartite group lifts: base multigraph with k left and k right vertices,
# d darts per base vertex (d layers, each a permutation of range(k)).
# Dart (i, j, s): A_{i,g} ~ B_{j, g*s} for all g in G.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _cost(k, G, D, darts, perms, limit=float("inf")):
    """Number of (representative, vertex) pairs at distance > D. Zero means valid."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        ba = i * G
        bb = (k + j) * G
        for g in range(G):
            a = ba + g
            b = bb + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    # G acts transitively on each class by left multiplication (automorphisms),
    # so one representative per class suffices.
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
        if total > limit:
            return total
    return total


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    """Threshold-accepting annealing over voltages and layer permutations."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [[mul[g][s] for g in range(G)] for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = 1.0 * (0.05 ** (it / iters))
        limit = cost - T * math.log(1.0 - rng.random())

        if rng.random() < 0.7 or k == 1:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_pm = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = [mul[g][new_s] for g in range(G)]
            c2 = _cost(k, G, D, darts, perms, limit)
            if c2 <= limit:
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_pm
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, perms, limit)
            if c2 <= limit:
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _edges(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# D = 3 base: projective plane incidence graph of PG(2, q), q + 1 <= d.
# ----------------------------------------------------------------------------

def _best_pg(d):
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


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
            best = (n, e)
            best_n = n

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    groups = _group_library()
    if not groups:
        return best

    ks = [1, 1, 2, 2, 3, 4]
    while time.monotonic() < deadline:
        k = rng.choice(ks)
        cands = [mul for mul in groups if 2 * k * len(mul) > best_n]
        if not cands:
            # No group at this k can beat the current best; try other k values.
            if all(not [m for m in groups if 2 * kk * len(m) > best_n] for kk in ks):
                break
            continue
        mul = rng.choice(cands)
        G = len(mul)
        res = _anneal(d, D, k, G, mul, rng, deadline, iters=3000)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
