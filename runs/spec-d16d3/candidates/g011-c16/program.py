import itertools
import math
import random
import time

import lib

# ----------------------------------------------------------------------------
# D = 3 search: arc-extended incidence graphs of PG(2, q), grown by exact checks.
#
# Base: incidence graph of PG(2, q), plus for each point P of an arc S an
# A-vertex joined to the lines through P, and for each line j of S a B-vertex
# joined to the points on j. Loads must stay within s = d - q - 1.
#
# Growth: a new vertex v is attached only if its neighbourhood reaches every
# existing vertex within distance 3. Adding vertices never lengthens existing
# paths, so every intermediate graph stays valid. Candidates come from
# "pencil" neighbourhoods (all usable neighbours of one vertex) and from a
# randomized greedy cover.
#
# Honest caveat: removing one point from the conic and attaching a pencil
# vertex on each side gives the same total (394) as the conic itself, so this
# family may only tie the record. The search explores arcs and growth moves,
# and every output is re-verified with lib.is_valid before returning.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9
_PG_CACHE = {}


def _pg(q):
    """Return (m, point_lines, line_points) for PG(2, q); point i and line i share index i."""
    if q not in _PG_CACHE:
        n2, edges = lib.projective_plane_incidence(q)
        m = n2 // 2
        point_lines = [[] for _ in range(m)]
        line_points = [[] for _ in range(m)]
        for u, v in edges:
            point_lines[u].append(v - m)
            line_points[v - m].append(u)
        _PG_CACHE[q] = (m, point_lines, line_points)
    return _PG_CACHE[q]


def _loads_ok(S, s, m, point_lines, line_points):
    """True if every line holds <= s points of S and every point lies on <= s lines indexed by S."""
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _random_arc(m, point_lines, line_points, s, rng):
    """One randomized greedy arc respecting the load bound s."""
    order = list(range(m))
    rng.shuffle(order)
    cl = [0] * m
    cp = [0] * m
    S = []
    for P in order:
        if all(cl[L] < s for L in point_lines[P]) and all(cp[Q] < s for Q in line_points[P]):
            S.append(P)
            for L in point_lines[P]:
                cl[L] += 1
            for Q in line_points[P]:
                cp[Q] += 1
    return S


def _arc_base(m, point_lines, line_points, S):
    """Return (n, edges, side) for the arc-extended incidence graph of arc S."""
    k = len(S)
    n = 2 * m + 2 * k
    E = []
    for i in range(m):
        for L in point_lines[i]:
            E.append((i, m + L))
    for t, P in enumerate(S):
        for L in point_lines[P]:
            E.append((2 * m + t, m + L))
    for t, j in enumerate(S):
        for Q in line_points[j]:
            E.append((Q, 2 * m + k + t))
    side = [0] * m + [1] * m + [0] * k + [1] * k
    return n, E, side


def _covers(N, nb, full):
    """True if the vertices within distance 3 of a new vertex adjacent to N cover every old vertex."""
    cov = 0
    t2 = 0
    for u in N:
        cov |= 1 << u
        t2 |= nb[u]
    t3 = 0
    x = t2
    while x:
        low = x & -x
        t3 |= nb[low.bit_length() - 1]
        x ^= low
    cov |= t2 | t3
    return (cov & full) == full


def _find_cover(n, adj, nb, side, d, want, rng):
    """Find a neighbour set N (opposite side to `want`) so a new vertex on side `want` is valid."""
    full = (1 << n) - 1
    # 1. Pencil-type candidates: all usable neighbours of one vertex x on side `want`.
    xs = [x for x in range(n) if side[x] == want]
    rng.shuffle(xs)
    for x in xs:
        N = [u for u in adj[x] if len(adj[u]) < d]
        if 0 < len(N) <= d and _covers(N, nb, full):
            return N
    # 2. Randomized greedy cover.
    cands = [u for u in range(n) if side[u] != want and len(adj[u]) < d]
    if not cands:
        return None
    T = {}
    for u in cands:
        t = 0
        for w in adj[u]:
            t |= nb[w]
        T[u] = t
    for _ in range(3):
        rng.shuffle(cands)
        cov = 0
        cnt = 0
        chosen = []
        taken = set()
        for _step in range(d):
            if (cov & full) == full:
                break
            best_u, best_g = None, 0
            for u in cands:
                if u in taken:
                    continue
                g = ((cov | (1 << u) | nb[u] | T[u]) & full).bit_count() - cnt
                if g > best_g:
                    best_u, best_g = u, g
            if best_u is None:
                break
            chosen.append(best_u)
            taken.add(best_u)
            cov |= (1 << best_u) | nb[best_u] | T[best_u]
            cnt = (cov & full).bit_count()
        if (cov & full) == full:
            return chosen
    return None


def _grow(n, E, side, d, rng, deadline):
    """Greedily attach extra vertices; each one is checked to reach everything within distance 3."""
    adj = [[] for _ in range(n)]
    for u, v in E:
        adj[u].append(v)
        adj[v].append(u)
    nb = [0] * n
    for u in range(n):
        x = 0
        for v in adj[u]:
            x |= 1 << v
        nb[u] = x
    side = list(side)
    while time.monotonic() < deadline:
        found = False
        for want in (0, 1):
            N = _find_cover(n, adj, nb, side, d, want, rng)
            if N is None:
                continue
            v = n
            n += 1
            side.append(want)
            adj.append(list(N))
            vb = 1 << v
            nbv = 0
            for u in N:
                adj[u].append(v)
                nb[u] |= vb
                nbv |= 1 << u
            nb.append(nbv)
            found = True
        if not found:
            break
    E2 = [(u, v) for u in range(n) for v in adj[u] if u < v]
    return n, E2


def _search_d3(d, deadline, rng):
    """Return up to 3 candidate (n, edges) graphs for D = 3, best first."""
    pool = []

    def offer(n, E):
        pool.append((n, E))
        pool.sort(key=lambda t: -t[0])
        del pool[3:]

    qs = sorted((q for q in range(2, d) if lib.is_prime_power(q)), reverse=True)[:2]
    if not qs:
        return pool
    start = time.monotonic()
    span = max(0.0, deadline - start)
    for idx, q in enumerate(qs):
        q_deadline = start + span * (idx + 1) / len(qs)
        s = d - q - 1
        m, point_lines, line_points = _pg(q)
        if s == 0:
            n, E, _side = _arc_base(m, point_lines, line_points, [])
            offer(n, E)
            continue
        pts = lib.projective_points(q)
        index = {p: i for i, p in enumerate(pts)}
        conic = _conic_set(q, index, lib.GF(q))
        conic_ok = _loads_ok(conic, s, m, point_lines, line_points)
        if conic_ok:
            n, E, _side = _arc_base(m, point_lines, line_points, conic)
            offer(n, E)  # plain parent-style base, so a valid answer always exists
        while time.monotonic() < q_deadline:
            if conic_ok and rng.random() < 0.6:
                S = list(conic)
                rem = rng.randint(0, 4)
            else:
                S = _random_arc(m, point_lines, line_points, s, rng)
                rem = rng.randint(0, 2)
            if rem and S:
                drop = set(rng.sample(range(len(S)), min(rem, len(S))))
                S = [p for i, p in enumerate(S) if i not in drop]
            if not _loads_ok(S, s, m, point_lines, line_points):
                continue
            n, E, side = _arc_base(m, point_lines, line_points, S)
            n2, E2 = _grow(n, E, side, d, rng, q_deadline)
            offer(n2, E2)
    return pool


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
# Simulated annealing over bi-Cayley voltage lifts (used for D != 3).
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
# Entry points.
# ----------------------------------------------------------------------------

def _build_d3(d, D, deadline, rng, fallback):
    best = fallback
    for n_c, e_c in _search_d3(d, deadline, rng):
        if n_c > best[0] and lib.is_valid(n_c, e_c, d, D):
            best = (n_c, e_c)
            break  # pool is sorted by order, so the first valid one is the best
    return best


def _build_general(d, D, deadline, rng, fallback):
    best = fallback

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Short slice of the arc search (diameter 3 is also valid for D >= 4).
    now = time.monotonic()
    if D >= 4:
        for n_c, e_c in _search_d3(d, now + 0.2 * max(0.0, deadline - now), rng):
            consider(n_c, e_c)
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
    while time.monotonic() < deadline:
        k = rng.choice(ks)
        base = best[0] // (2 * k)
        G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        res = _anneal(d, D, k, order, mul, rng, deadline, iters=400)
        if res is not None:
            consider(res[0], res[1])
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    fallback = lib.haar_graph(d, range(d))
    try:
        if D == 3:
            return _build_d3(d, D, deadline, rng, fallback)
        return _build_general(d, D, deadline, rng, fallback)
    except Exception:
        return fallback
