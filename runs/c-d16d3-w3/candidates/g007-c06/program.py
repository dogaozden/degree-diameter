import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q) (points 0..m-1, lines m..2m-1).
# Every old vertex has degree q+1, so with d >= q+1 it has spare s = d - q - 1.
#
# A-side: a multiset SA of points (repeats allowed). Each entry P gets a new
#         vertex joined to the q+1 lines through P. Every line may hold <= s entries.
# B-side: a multiset SB of lines. Each entry j gets a new vertex joined to the
#         q+1 points on j. Every point may lie on <= s entries.
#
# Diameter stays 3 for ANY multisets SA, SB (checked by hand: A-A and B-B pairs
# are at distance 2, A-to-old-point 2, A-to-old-line 3, A-to-B 3, and the rest
# follow from PG(2,q)). The parent only reached about 14 entries per side. The
# true per-side capacity is about s*m/(q+1), i.e. 26 for q = 13, s = 2.
#
# New in this version: the multiset is chosen by a dedicated packing local search
# (_pack) that keeps a target size K and repairs line overloads by moving units
# between points, instead of a greedy fill with random perturbations.
# ----------------------------------------------------------------------------

def _pg_data(q):
    """Return (m, edges, point_lines, line_points, index, pts) for PG(2, q)."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, point_lines, line_points, index, pts


def _loads_ok(S, s, m, nbr):
    """True if every target t is hit by <= s entries of S (repeats counted)."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _pack(m, s, nbr, inv, rng, deadline):
    """Find a large multiset of items so that every target is hit at most s times.

    nbr[j]: targets hit by item j.  inv[t]: items hitting target t (inverse of nbr).
    Maintains a fixed size K; while some target is overloaded, move one unit from an
    item on that target to the best of a random sample of items. When feasible, K grows.
    After a long stall, one unit is dropped. Returns the best feasible multiset found.
    """
    if s <= 0 or m <= 0:
        return []
    x = [0] * m
    load = [0] * m
    viol = 0

    def add(j):
        nonlocal viol
        for t in nbr[j]:
            if load[t] >= s:
                viol += 1
            load[t] += 1
        x[j] += 1

    def remove(j):
        nonlocal viol
        x[j] -= 1
        for t in nbr[j]:
            load[t] -= 1
            if load[t] >= s:
                viol -= 1

    def delta(j):
        c = 0
        for t in nbr[j]:
            if load[t] >= s:
                c += 1
        return c

    # Greedy start: add items with zero violation increase, in random order.
    order = list(range(m))
    rng.shuffle(order)
    for j in order:
        while delta(j) == 0:
            add(j)
    K = sum(x)
    best_K = K
    best_x = list(x)
    stall = 0

    while time.monotonic() < deadline:
        if viol == 0:
            if K > best_K:
                best_K = K
                best_x = list(x)
            dm = min(delta(j) for j in range(m))
            js = [j for j in range(m) if delta(j) == dm]
            add(rng.choice(js))
            K += 1
            stall = 0
        else:
            stall += 1
            if stall > 3000:
                # Drop one unit to escape a stuck target configuration.
                nz = [j for j in range(m) if x[j] > 0]
                if nz:
                    remove(rng.choice(nz))
                    K -= 1
                stall = 0
                continue
            over = [t for t in range(m) if load[t] > s]
            if not over:
                break
            t = rng.choice(over)
            items = [i for i in inv[t] if x[i] > 0]
            if not items:
                continue
            i = rng.choice(items)
            remove(i)
            sample = rng.sample(range(m), min(60, m))
            dm = min(delta(j) for j in sample)
            js = [j for j in sample if delta(j) == dm]
            add(rng.choice(js))

    return [j for j in range(m) for _ in range(best_x[j])]


def _arc_graph(m, edges, point_lines, line_points, SA, SB):
    """Old PG incidence plus one new A-vertex per SA entry and one new B-vertex per SB entry."""
    na, nb = len(SA), len(SB)
    n = 2 * m + na + nb
    E = list(edges)
    for t, P in enumerate(SA):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(SB):
        b = 2 * m + na + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _arc_extensions(d, deadline, rng):
    """Return (n, edges) candidates for the best few prime powers q with s = d-q-1 >= 1."""
    out = []
    qs = [q for q in range(2, min(d - 1, 23) + 1)
          if lib.is_prime_power(q) and d - q - 1 >= 1]
    if not qs:
        return out
    ests = {}
    for q in qs:
        m = q * q + q + 1
        s = d - q - 1
        ests[q] = 2 * m + 2 * (s * m // (q + 1))
    top = sorted(qs, key=lambda q: -ests[q])[:3]
    wsum = float(sum(ests[q] for q in top))
    total = max(0.0, deadline - time.monotonic())
    for q in top:
        slot = total * ests[q] / wsum
        m, edges, pl, lp, index, pts = _pg_data(q)
        s = d - q - 1
        half = slot / 2.0
        SA = _pack(m, s, pl, lp, rng, time.monotonic() + half)
        SB = _pack(m, s, lp, pl, rng, time.monotonic() + half)
        if not (_loads_ok(SA, s, m, pl) and _loads_ok(SB, s, m, lp)):
            continue
        out.append(_arc_graph(m, edges, pl, lp, SA, SB))
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
# Simulated annealing over bi-Cayley voltage lifts (used for D >= 4).
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


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
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

    # Arc-extended projective plane graphs with packed A and B multisets (diameter 3).
    if D >= 3:
        try:
            cands = _arc_extensions(d, deadline, random.Random(seed * 7919 + d))
            cands.sort(key=lambda t: -t[0])
            for n_c, e_c in cands:
                if n_c > best_n:
                    consider(n_c, e_c)
        except Exception:
            pass

    if D >= 4 and time.monotonic() < deadline:
        try:
            gq = _best_gq(d)
            if gq is not None:
                consider(gq[0], gq[1])
        except Exception:
            pass

    # Annealed group voltage lifts for D >= 4 (for D = 3 the arc search is the main tool).
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
