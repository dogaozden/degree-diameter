import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q). Every old vertex has degree q+1,
# so with d >= q+1 it has spare capacity s = d - q - 1. Pick a point set S with
# every line holding <= s points of S and every point on <= s lines indexed by
# S. For each P in S add an A-vertex joined to the lines through P; for each j
# in S add a B-vertex joined to the points on line j.
#
# Sides: points and A-vertices are side 0; lines and B-vertices are side 1.
# ----------------------------------------------------------------------------

def _pg_data(q):
    """Return (m, edges, pl, lp): PG(2,q) incidence with pl[P] = lines through P, lp[L] = points on L."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    pl = [[] for _ in range(m)]
    lp = [[] for _ in range(m)]
    for u, v in edges:
        pl[u].append(v - m)
        lp[v - m].append(u)
    return m, edges, pl, lp


def _loads_ok(S, s, m, pl, lp):
    """True if every line holds <= s points of S and every point lies on <= s lines indexed by S."""
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in pl[P]:
            cl[L] += 1
        for Q in lp[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, pl, lp, rng, trials, deadline):
    """Randomized greedy choice of S with all loads <= s; returns the largest found."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        cl = [0] * m
        cp = [0] * m
        S = []
        for P in order:
            if all(cl[L] < s for L in pl[P]) and all(cp[Q] < s for Q in lp[P]):
                S.append(P)
                for L in pl[P]:
                    cl[L] += 1
                for Q in lp[P]:
                    cp[Q] += 1
        if len(S) > len(best):
            best = S
    return best


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q): an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, S, pl, lp):
    """Return (n, edges, side) for the arc-extended graph."""
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in pl[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in lp[j]:
            E.append((Q, b))
    side = [0] * m + [1] * m + [0] * k + [1] * k
    return n, E, side


def _arc_candidates(d, deadline, rng):
    """Return a list of (n, edges, side) arc-graphs, largest first."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, pl, lp = _pg_data(q)
        sets = []
        if s >= 1:
            sets.append(_greedy_arc(m, s, pl, lp, rng, 40, deadline))
        if s >= 2:
            index = {p: i for i, p in enumerate(lib.projective_points(q))}
            cs = _conic_set(q, index, lib.GF(q))
            if _loads_ok(cs, s, m, pl, lp):
                sets.append(cs)
        S = max(sets, key=len, default=[])
        if not _loads_ok(S, s, m, pl, lp):
            continue
        out.append(_arc_graph(m, edges, S, pl, lp))
    out.sort(key=lambda t: -t[0])
    return out


# ----------------------------------------------------------------------------
# NEW: cover augmentation (diameter 3, bipartite).
#
# Claim: let x be a new vertex on side s with neighbour set N (all on side
# 1-s, each with spare degree). If every alive side-s vertex has a neighbour
# in N, then every vertex is within distance 3 of x, and the diameter of the
# existing graph is unchanged (edges are only added). So the step is valid.
#
# Finding N is a set-cover problem: cover all side-s vertices by at most d
# spare opposite-side neighbourhoods. Randomized greedy with restarts does it
# with bitmasks. Each accepted addition is also checked with lib.is_valid.
# A swap move (remove a random added vertex, then try to add two or more)
# lets the search escape the greedy stall.
# ----------------------------------------------------------------------------

def _cover(adj, side, s, d, rng, restarts):
    """Return a list of opposite-side vertices covering all alive side-s vertices, or None."""
    elems = [v for v in range(len(adj)) if side[v] == s]
    if not elems:
        return None
    idx = {v: i for i, v in enumerate(elems)}
    full = (1 << len(elems)) - 1
    cands = []
    for b in range(len(adj)):
        if side[b] != 1 - s or len(adj[b]) >= d:
            continue
        mk = 0
        for a in adj[b]:
            if side[a] == s:
                mk |= 1 << idx[a]
        if mk:
            cands.append((b, mk))
    union = 0
    for _, mk in cands:
        union |= mk
    if union != full:
        return None
    for r in range(restarts):
        rng.shuffle(cands)
        covered = 0
        chosen = []
        while covered != full and len(chosen) < d:
            bg = 0
            scored = []
            for b, mk in cands:
                g = (mk & ~covered).bit_count()
                if g:
                    scored.append((g, b, mk))
                    if g > bg:
                        bg = g
            if not scored:
                break
            if r == 0 or rng.random() < 0.6:
                top = [t for t in scored if t[0] == bg]
            else:
                top = [t for t in scored if t[0] >= bg - 1]
            g, b, mk = rng.choice(top)
            chosen.append(b)
            covered |= mk
        if covered == full and chosen:
            return chosen
    return None


def _try_add(adj, side, d, rng):
    """Try to add one new vertex. Return its id, or None if no cover was found."""
    order = [0, 1]
    rng.shuffle(order)
    for s in order:
        nb = _cover(adj, side, s, d, rng, 6)
        if nb:
            x = len(adj)
            adj.append(set(nb))
            side.append(s)
            for b in nb:
                adj[b].add(x)
            return x
    return None


def _remove(adj, side, x):
    for b in adj[x]:
        adj[b].discard(x)
    adj[x] = set()
    side[x] = -1


def _export(adj, side):
    E = [(u, v) for u in range(len(adj)) if side[u] >= 0 for v in adj[u] if u < v]
    return lib.relabel(E)


def _valid(adj, side, d, D):
    n, E = _export(adj, side)
    return bool(E) and lib.is_valid(n, E, d, D)


def _snap(adj, side):
    return [set(a) for a in adj], list(side)


def _restore(adj, side, mark):
    adj[:] = [set(a) for a in mark[0]]
    side[:] = list(mark[1])


def _augment(adj, side, base_n, d, D, deadline, rng):
    """Greedy cover additions plus swap moves; every accepted state is validated."""
    cur = sum(1 for s in side if s >= 0)
    while time.monotonic() < deadline:
        x = _try_add(adj, side, d, rng)
        if x is not None:
            if _valid(adj, side, d, D):
                cur += 1
                continue
            _remove(adj, side, x)
        added = [v for v in range(base_n, len(side)) if side[v] >= 0]
        if not added:
            break
        mark = _snap(adj, side)
        _remove(adj, side, rng.choice(added))
        gained = 0
        for _ in range(3):
            if _try_add(adj, side, d, rng) is None:
                break
            gained += 1
        if gained >= 2 and _valid(adj, side, d, D):
            cur = cur - 1 + gained
        else:
            _restore(adj, side, mark)
    return cur


def _augment_run(n0, E0, side0, d, D, deadline, rng):
    adj = [set() for _ in range(n0)]
    for u, v in E0:
        adj[u].add(v)
        adj[v].add(u)
    side = list(side0)
    _augment(adj, side, n0, d, D, deadline, rng)
    n, E = _export(adj, side)
    if E and lib.is_valid(n, E, d, D):
        return n, E
    return None


# ----------------------------------------------------------------------------
# Generalized quadrangle baseline (D = 4).
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
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

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _best_gq(d):
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Simulated annealing over bi-Cayley voltage lifts (for D >= 4 cases).
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

    T = 1.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.997)

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

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and e and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        cands = _arc_candidates(d, start + 0.15 * time_limit, random.Random(seed * 7919 + d))
        for n_c, E_c, _side in cands:
            consider(n_c, E_c)

        if D == 3:
            use = cands[:3]
            for i, (n_c, E_c, side_c) in enumerate(use):
                now = time.monotonic()
                if now >= deadline:
                    break
                share = (deadline - now) / (len(use) - i)
                res = _augment_run(n_c, E_c, side_c, d, D, now + share,
                                   random.Random(seed * 131 + i))
                if res is not None:
                    consider(res[0], res[1])
            if not lib.is_valid(best[0], best[1], d, D):
                best = lib.haar_graph(d, range(d))
            return best

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
    while time.monotonic() < deadline:
        k = rng.choice(ks)
        base = best_n // (2 * k)
        G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        res = _anneal(d, D, k, order, mul, rng, deadline, iters=400)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
