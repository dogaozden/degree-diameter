"""Twin blow-up integer program for diameter-3 bipartite graphs.

New in this version: a blow-up view of the projective-plane construction. Replace each
vertex v of a base graph H by mult[v] >= 1 copies. Copies of u and v are joined completely
whenever u ~ v in H. Copies of one vertex are twins, so distances between old vertices are
unchanged, and any base of diameter 3 stays diameter 3 for every multiplicity vector.
The only constraint is degree: for every base vertex v,

    sum over u in N_H(v) of mult[u] <= d.

Maximize sum of mult. The arc extension of the parent is the special case mult = 2 on an
arc of points and an arc of lines, so this generalises it. Multiplicities are optimised by
a plateau local search (add a copy, or swap one copy out to make room), with restarts that
start from the conic seed or from all ones.

Note: for PG(2,13) and d = 16 the blow-up optimum is 394 (per side, the extra weights form
a 2-arc, so at most q+1 = 14 extra points). Beating 394 needs a different base graph, so
the search keeps several prime-power bases and validates every output with lib.is_valid.
Diameter-4 cases keep the parent's generalized quadrangle and voltage-lift search.
"""
import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane bases.
# ----------------------------------------------------------------------------

_PG_CACHE = {}


def _pg(q):
    """Return (n2, nbr, m, pts) for the incidence graph of PG(2, q); points 0..m-1, lines m..2m-1."""
    if q not in _PG_CACHE:
        n2, edges = lib.projective_plane_incidence(q)
        m = n2 // 2
        nbr = [[] for _ in range(n2)]
        for u, v in edges:
            nbr[u].append(v)
            nbr[v].append(u)
        _PG_CACHE[q] = (n2, nbr, m, lib.projective_points(q))
    return _PG_CACHE[q]


def _conic_seed(q, pts):
    """Point indices of a conic (plus nucleus for even q): an arc with no three collinear."""
    F = lib.GF(q)
    index = {p: i for i, p in enumerate(pts)}
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


# ----------------------------------------------------------------------------
# Twin blow-up: build a graph from a base graph and multiplicities.
# ----------------------------------------------------------------------------

def _blowup(n, nbr, mult):
    """Return (total, edges) of the blow-up where each base vertex v becomes mult[v] copies."""
    start = [0] * n
    tot = 0
    for v in range(n):
        start[v] = tot
        tot += mult[v]
    E = []
    for u in range(n):
        for v in nbr[u]:
            if u < v:
                for a in range(mult[u]):
                    for b in range(mult[v]):
                        E.append((start[u] + a, start[v] + b))
    return tot, E


def _blowup_search(n, nbr, d, mult0, rng, deadline, iters):
    """Plateau local search on multiplicities (maximise sum mult, load[v] <= d for all v).

    load[v] = sum of mult over neighbours of v, which is the degree of each copy of v.
    Moves: add a copy of v if every neighbour has spare degree. Otherwise remove up to one
    copy of blocking neighbours, add the copy of v, and keep the move only if the total
    does not drop (removing one copy and adding one is a plateau move).
    Returns the best multiplicity vector seen, or None if mult0 is infeasible.
    """
    mult = list(mult0)
    load = [sum(mult[u] for u in nbr[v]) for v in range(n)]
    if max(load) > d:
        return None
    tot = sum(mult)
    best_tot, best_mult = tot, list(mult)
    for it in range(iters):
        if it % 512 == 0 and time.monotonic() > deadline:
            break
        v = rng.randrange(n)
        if all(load[u] < d for u in nbr[v]):
            mult[v] += 1
            tot += 1
            for u in nbr[v]:
                load[u] += 1
        else:
            removed = []
            for u in nbr[v]:
                while load[u] >= d and len(removed) < 2:
                    cands = [w for w in nbr[u] if mult[w] > 1]
                    if not cands:
                        break
                    w = rng.choice(cands)
                    mult[w] -= 1
                    tot -= 1
                    for x in nbr[w]:
                        load[x] -= 1
                    removed.append(w)
            if len(removed) <= 1 and all(load[u] < d for u in nbr[v]):
                mult[v] += 1
                tot += 1
                for u in nbr[v]:
                    load[u] += 1
            else:
                for w in reversed(removed):
                    mult[w] += 1
                    tot += 1
                    for x in nbr[w]:
                        load[x] += 1
                continue
        if tot > best_tot:
            best_tot, best_mult = tot, list(mult)
    return best_mult


def _blowup_candidates(d, deadline, rng):
    """Return a list of (total, edges) blow-ups of PG(2, q) for prime powers q with q+1 <= d.

    Alternates between a conic-seeded start and an all-ones start, so the search is not
    stuck with one structure. Outputs are sorted by total, largest first.
    """
    qs = [q for q in range(2, d) if lib.is_prime_power(q)]
    if not qs:
        return []
    out = []
    rounds = 0
    while time.monotonic() < deadline and rounds < 60:
        rounds += 1
        for q in qs:
            if time.monotonic() > deadline:
                break
            n2, nbr, m, pts = _pg(q)
            if rounds % 2 == 1:
                mult0 = [1] * n2
                for i in _conic_seed(q, pts):
                    mult0[i] = 2
                    mult0[m + i] = 2
            else:
                mult0 = [1] * n2
            mult = _blowup_search(n2, nbr, d, mult0, rng, deadline, iters=200 * n2)
            if mult is None:
                continue
            tot, E = _blowup(n2, nbr, mult)
            out.append((tot, E))
        out.sort(key=lambda t: -t[0])
        out = out[:4]
    return out


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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Simulated annealing over bi-Cayley voltage lifts (for D >= 4).
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
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    deadline = t0 + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Twin blow-ups of projective planes: valid for every D >= 3.
    if D >= 3:
        for tot, E in _blowup_candidates(d, t0 + 0.75 * time_limit, rng):
            if tot > best_n:
                consider(tot, E)

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Voltage-lift annealing for D >= 4 (larger bases for D >= 5).
    if D >= 4:
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
