import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Time fractions (of time_limit). The group-lift search ends at FRAC_LIFT_END;
# the remaining time goes to an unstructured edge-switch search that grows the
# best regular bipartite graph one vertex pair at a time. Everything ends by
# FRAC_TOTAL.
# ----------------------------------------------------------------------------
FRAC_LIFT_END = 0.50
FRAC_TOTAL = 0.86
GQ_Q_MAX = 5
_BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Algebraic seeds: projective plane (D >= 3) and generalized quadrangle (D >= 4).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


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
    """W(q) for the largest prime power q <= min(d - 1, GQ_Q_MAX)."""
    for q in range(min(d - 1, GQ_Q_MAX), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Group voltage lifts over Z_m x| Z_k2 (annealed over voltages and layer maps).
#
# Vertices: A_i,g = i*G + g  and  B_j,h = (k+j)*G + h.
# Dart (i, j, s) joins A_i,g to B_j,mul(g,s) for every g in the group.
# Every vertex has degree d, and the two sides have equal size k*G.
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


def _lift_anneal(d, D, k, G, mul, rng, deadline, iters):
    """Simulated annealing over voltages and per-layer B-assignments. Returns (n, edges) or None."""
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
# Unstructured search: edge switches on d-regular bipartite graphs, with
# simulated annealing on the number of bad pairs. Growth adds one vertex per
# side, keeping regularity, and the annealing then repairs the diameter.
#
# Representation: A-vertices 0..N-1, B-vertices 0..N-1 (global id N + b).
# E is a list of (a, b) pairs, one per edge.
# ----------------------------------------------------------------------------

def _bip_cost(N, E, D):
    """Sum over vertices of the number of vertices at distance > D (0 means diameter <= D)."""
    n = 2 * N
    adj = [[] for _ in range(n)]
    for a, b in E:
        adj[a].append(N + b)
        adj[N + b].append(a)
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(n - r.bit_count() for r in reach)


def _bip_anneal(N, E, D, rng, deadline, iters):
    """Anneal degree-preserving edge switches on E in place. Returns the final cost."""
    eset = set(E)
    cur = _bip_cost(N, E, D)
    m = len(E)
    for it in range(iters):
        if cur == 0:
            break
        if (it & 15) == 0 and time.monotonic() > deadline:
            break
        T = 3.0 * (0.1 / 3.0) ** (it / iters)
        i = rng.randrange(m)
        j = rng.randrange(m)
        a, b = E[i]
        c, e = E[j]
        if a == c or b == e or (a, e) in eset or (c, b) in eset:
            continue
        E[i] = (a, e)
        E[j] = (c, b)
        eset.discard((a, b))
        eset.discard((c, e))
        eset.add((a, e))
        eset.add((c, b))
        new = _bip_cost(N, E, D)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = new
        else:
            E[i] = (a, b)
            E[j] = (c, e)
            eset.discard((a, e))
            eset.discard((c, b))
            eset.add((a, b))
            eset.add((c, e))
    return cur


def _grow(N, E, d, rng):
    """Add one A-vertex and one B-vertex, each of degree d, by splicing a d-matching.

    Remove edges (a_i, b_i) for a matching of size d, then add (a_i, y) and (x, b_i),
    with x the new A-vertex and y the new B-vertex. Old degrees are unchanged.
    """
    for _ in range(50):
        idx = list(range(len(E)))
        rng.shuffle(idx)
        ua, ub, pick = set(), set(), []
        for i in idx:
            a, b = E[i]
            if a in ua or b in ub:
                continue
            ua.add(a)
            ub.add(b)
            pick.append(i)
            if len(pick) == d:
                break
        if len(pick) == d:
            x = N
            y = N
            chosen = set(pick)
            newE = [e for i, e in enumerate(E) if i not in chosen]
            for i in pick:
                a, b = E[i]
                newE.append((a, y))
                newE.append((x, b))
            return N + 1, newE
    return None


def _as_regular(n, edges, d):
    """Return (N, E) if (n, edges) is a d-regular bipartite graph with equal sides, else None."""
    if n % 2:
        return None
    N = n // 2
    deg = [0] * n
    seen = set()
    E = []
    for u, v in edges:
        a, b = (u, v) if u < v else (v, u)
        if not (a < N <= b):
            return None
        if (a, b) in seen:
            return None
        seen.add((a, b))
        deg[a] += 1
        deg[b] += 1
        E.append((a, b - N))
    if any(x != d for x in deg):
        return None
    return N, E


# ----------------------------------------------------------------------------
# Driver
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    lift_deadline = start + FRAC_LIFT_END * time_limit
    final_deadline = start + FRAC_TOTAL * time_limit
    rng = random.Random(seed)

    # Trivial cases.
    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D  # even cycle: bipartite, diameter D
        return L, [(i, (i + 1) % L) for i in range(L)]

    # K_{d,d} has diameter 2 and is the always-valid fallback.
    fallback = lib.haar_graph(d, range(d))
    if D == 2:
        return fallback

    best = fallback
    moore = lib._moore_bound(d, D)

    def consider(n, edges):
        nonlocal best
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)

    # Algebraic seeds.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
    if best[0] >= moore:
        return best

    # Stage 1: annealed group voltage lifts.
    try:
        if D >= 5:
            ks = [1, 1, 2, 2, 3, 4]
            anneal_iters = 1500
        else:
            ks = [1, 2, 2, 3, 4]
            anneal_iters = 400
        while time.monotonic() < lift_deadline and best[0] < moore:
            k = rng.choice(ks)
            base = best[0] // (2 * k)
            if D >= 5:
                G = max(2, base + 1 + rng.randrange(0, 3))
            else:
                G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _lift_anneal(d, D, k, order, mul, rng, lift_deadline, anneal_iters)
            if res is not None:
                consider(res[0], res[1])
    except Exception:
        pass

    # Stage 2: edge-switch annealing from the best regular bipartite graph,
    # growing one vertex pair at a time whenever the diameter bound is reached.
    try:
        reg = _as_regular(best[0], best[1], d)
        if reg is None:
            N = d
            E = [(a, b) for a in range(d) for b in range(d)]
        else:
            N, E = reg
            E = list(E)
        while time.monotonic() < final_deadline and 2 * N < moore:
            if _bip_cost(N, E, D) == 0:
                consider(2 * N, [(a, N + b) for a, b in E])
                g = _grow(N, E, d, rng)
                if g is None:
                    break
                N, E = g
            else:
                _bip_anneal(N, E, D, rng, final_deadline, 1500)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
