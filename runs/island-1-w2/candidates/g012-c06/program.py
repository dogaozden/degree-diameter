import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Known bases: Araujo-Pardo-Lopez, projective plane, polarity double cover,
# and bipartite double covers of undirected Kautz graphs.
# ----------------------------------------------------------------------------

def _araujo_best(d):
    """Araujo-Pardo-Lopez graph for the largest prime power q <= d - 2 (degree q + 2 <= d, diameter 3)."""
    for q in range(min(d - 2, 23), 2, -1):
        if lib.is_prime_power(q):
            try:
                return lib.araujo_lopez_graph(q)
            except ValueError:
                return None
    return None


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _polarity_cover(d):
    """Bipartite double cover of the Erdos-Renyi polarity graph ER_q (q + 1 <= d)."""
    q = None
    for cand in range(d - 1, 1, -1):
        if lib.is_prime_power(cand):
            q = cand
            break
    if q is None:
        return None
    F = lib.GF(q)
    pts = np.array(lib.projective_points(q), dtype=np.int64)
    m = len(pts)
    mul, add = F.mul_table, F.add_table
    terms = [mul[pts[:, None, c], pts[None, :, c]] for c in range(3)]
    dot = add[add[terms[0], terms[1]], terms[2]]
    rows, cols = np.nonzero(dot == 0)
    edges = [(int(i), m + int(j)) for i, j in zip(rows, cols) if i != j]
    return 2 * m, edges


def _kautz_undirected(s, L):
    """Adjacency lists of the undirected Kautz graph K(s, L) (L >= 2)."""
    words = []

    def rec(w):
        if len(w) == L:
            words.append(w)
            return
        for c in range(s):
            if not w or c != w[-1]:
                rec(w + (c,))

    rec(())
    idx = {w: i for i, w in enumerate(words)}
    adj = [set() for _ in words]
    for w in words:
        i = idx[w]
        for c in range(s):
            if c != w[-1]:
                j = idx[w[1:] + (c,)]
                if i != j:
                    adj[i].add(j)
                    adj[j].add(i)
    return [sorted(a) for a in adj]


def _double_cover(N, adj):
    """Bipartite double cover: v -> v (side 0) and N + v (side 1)."""
    edges = []
    for u in range(N):
        for v in adj[u]:
            edges.append((u, N + v))
    return 2 * N, edges


def _kautz_cover_candidates(d, D, deadline):
    """Double covers of undirected Kautz graphs with max degree <= d, for L in {D, D-1}."""
    out = []
    cap = lib.moore_bound(d, D)
    for s in range(2, d // 2 + 2):
        if 2 * (s - 1) > d:
            break
        for L in (D, D - 1):
            if L < 2 or time.monotonic() > deadline:
                continue
            N = s * (s - 1) ** (L - 1)
            if 2 * N > cap:
                continue
            adj = _kautz_undirected(s, L)
            if not adj or max(len(a) for a in adj) > d:
                continue
            out.append(_double_cover(len(adj), adj))
    return out


# ----------------------------------------------------------------------------
# Arc-extended projective plane graphs (diameter 3).
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


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
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
            if all(cl[L] < s for L in point_lines[P]) and all(cp[Q] < s for Q in line_points[P]):
                S.append(P)
                for L in point_lines[P]:
                    cl[L] += 1
                for Q in line_points[P]:
                    cp[Q] += 1
        if len(S) > len(best):
            best = S
    return best


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    """Old PG incidence plus a new A and a new B vertex per element of S."""
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _arc_extensions(d, deadline, rng):
    """Return a list of (n, edges) candidates, one per prime power q with q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        cands = []
        if s >= 1:
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 40, deadline))
        if s >= 2:
            F = lib.GF(q)
            cs = _conic_set(q, index, F)
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len, default=[])
        if not S or not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


# ----------------------------------------------------------------------------
# Cover-based growth, edge saturation, and twin cloning (diameter-preserving).
# ----------------------------------------------------------------------------

def _balls_radius(n, adj, r):
    """Bitmask per vertex of all vertices within distance r."""
    ball = [1 << v for v in range(n)]
    for _ in range(r):
        new = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new.append(x)
        ball = new
    return ball


def _bipartition(n, adj):
    """Two-colouring of a bipartite graph given by adjacency lists."""
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


def _greedy_cover(cands, ball, full, d, rng, randomize):
    """Greedy set cover of `full` by at most d candidate vertices; None if it fails."""
    pool = list(cands)
    if randomize:
        rng.shuffle(pool)
    covered = 0
    chosen = []
    while covered != full and len(chosen) < d and pool:
        gains = [(ball[s] & ~covered).bit_count() for s in pool]
        best_g = max(gains, default=0)
        if best_g == 0:
            break
        thr = best_g
        if randomize and rng.random() < 0.5:
            thr = best_g - 1
        opts = [i for i, g in enumerate(gains) if g >= thr and g > 0]
        i = rng.choice(opts) if randomize else opts[0]
        s = pool.pop(i)
        chosen.append(s)
        covered |= ball[s]
    return chosen if covered == full else None


def _extend_cover(n, edges, d, D, deadline, rng):
    """Greedily add vertices whose neighbourhoods cover all vertices within D-1."""
    if D < 2:
        return n, edges
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)

    while time.monotonic() < deadline:
        ball = _balls_radius(n, adj, D - 1)
        full = (1 << n) - 1
        added = False
        for c in (0, 1):
            cands = [s for s in range(n) if color[s] == c and deg[s] < d]
            if not cands:
                continue
            chosen = None
            for attempt in range(200):
                if time.monotonic() >= deadline:
                    break
                chosen = _greedy_cover(cands, ball, full, d, rng, attempt > 0)
                if chosen:
                    break
            if chosen:
                v = n
                n += 1
                color.append(1 - c)
                adj.append([])
                deg.append(0)
                for s in chosen:
                    edges.append((s, v))
                    adj[s].append(v)
                    adj[v].append(s)
                    deg[s] += 1
                    deg[v] += 1
                added = True
                break
        if not added:
            break
    return n, edges


def _saturate_edges(n, edges, d, rng):
    """Greedily join deficient opposite-side vertices in random order (returns edge list)."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    existing = set()
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
        existing.add((min(u, v), max(u, v)))
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    left = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in left for b in right
             if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return edges


def _grow(n, edges, d, D, deadline, rng):
    """Extend by cover vertices, then saturate edges with the leftover spare degree."""
    cur_n, cur_e = n, list(edges)
    for _ in range(8):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate_edges(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


def _twin_grow(n, edges, d, D, rng):
    """Add false twins of vertices whose neighbours all have spare degree (diameter-preserving for D >= 2)."""
    if D < 2:
        return n, list(edges)
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    order = [w for w in range(n) if adj[w]]
    rng.shuffle(order)
    for w in order:
        while adj[w] and all(deg[u] < d for u in adj[w]):
            v = n
            n += 1
            nbrs = list(adj[w])
            adj.append(nbrs)
            deg.append(len(nbrs))
            for u in nbrs:
                adj[u].append(v)
                deg[u] += 1
                edges.append((u, v))
    return n, edges


# ----------------------------------------------------------------------------
# NEW: bi-Cayley graphs over a single group of order G (one base vertex per side).
#
# Vertices A_g = g and B_h = G + h. Connection set S (|S| = d, distinct group
# elements) gives edges A_g -- B_{g*s} for s in S. Left translation is an
# automorphism, so every pair of vertices is equivalent to a pair involving
# A_e or B_e: validity needs only two BFS runs. This yields a 2G-vertex graph,
# which is d-regular and bipartite.
# ----------------------------------------------------------------------------

def _k1_cost(G, D, adj):
    """Number of (source, vertex) pairs at distance > D from A_e or B_e. Zero means valid."""
    N = 2 * G
    total = 0
    for src in (0, G):
        seen = bytearray(N)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += N - count
    return total


def _k1_edges(G, mul, S):
    """Edge list of the bi-Cayley graph with connection set S."""
    edges = [(g, G + mul(g, s)) for s in S for g in range(G)]
    return 2 * G, edges


def _k1_anneal(d, D, G, mul, rng, end, iters):
    """Anneal a connection set S of size d in a group of order G until bi-Cayley diameter <= D."""
    if d > G:
        return None
    cache = {}

    def perm(s):
        p = cache.get(s)
        if p is None:
            p = [mul(g, s) for g in range(G)]
            cache[s] = p
        return p

    def adj_of(S):
        adj = [[] for _ in range(2 * G)]
        for s in S:
            p = perm(s)
            for g in range(G):
                h = G + p[g]
                adj[g].append(h)
                adj[h].append(g)
        return adj

    S = rng.sample(range(G), d)
    cost = _k1_cost(G, D, adj_of(S))
    t0 = time.monotonic()
    span = max(1e-3, end - t0)
    for _ in range(iters):
        if cost == 0 or time.monotonic() >= end:
            break
        frac = min(1.0, (time.monotonic() - t0) / span)
        T = 3.0 * (0.03 ** frac)
        limit = cost - T * math.log(1.0 - rng.random())
        i = rng.randrange(d)
        new = rng.randrange(G)
        if new in S:
            continue
        old = S[i]
        S[i] = new
        c2 = _k1_cost(G, D, adj_of(S))
        if c2 <= limit:
            cost = c2
        else:
            S[i] = old
    return list(S) if cost == 0 else None


def _k1_ladder(d, D, moore, rng, deadline, consider, get_best):
    """Repeatedly try bi-Cayley graphs of random groups with orders just above the current best half-order."""
    lo = get_best() // 2 + 1
    while time.monotonic() < deadline:
        if 2 * lo > moore:
            break
        w = max(2, lo // 40)
        G = lo + rng.randrange(0, w)
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        run_end = min(deadline, time.monotonic() + 1.5)
        S = _k1_anneal(d, D, order, mul, rng, run_end, 6000)
        if S is not None:
            n, e = _k1_edges(order, mul, S)
            consider(n, e)
            lo = max(lo, order + 1)


# ----------------------------------------------------------------------------
# Bi-Cayley voltage lifts over semidirect products Z_m x| Z_k2 and affine
# groups Z_p x| Z_k (k | p-1), annealed with k base vertices per side.
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


def _prime_list(limit):
    """All primes <= limit."""
    if limit < 2:
        return []
    sieve = bytearray([1]) * (limit + 1)
    sieve[0] = sieve[1] = 0
    for i in range(2, int(limit ** 0.5) + 1):
        if sieve[i]:
            sieve[i * i::i] = bytearray(len(range(i * i, limit + 1, i)))
    return [i for i in range(limit + 1) if sieve[i]]


def _affine_pairs(max_G):
    """All (p, k) with p prime, k >= 2, k | p-1 and p*k <= max_G."""
    pairs = []
    for p in _prime_list(max_G):
        if p < 3:
            continue
        for k in range(2, p):
            if (p - 1) % k == 0 and p * k <= max_G:
                pairs.append((p, k))
    return pairs


_AFFINE = _affine_pairs(2000)


def _prime_factors(n):
    """Distinct prime factors of n."""
    out = []
    q = 2
    while q * q <= n:
        if n % q == 0:
            out.append(q)
            while n % q == 0:
                n //= q
        q += 1
    if n > 1:
        out.append(n)
    return out


def _elem_of_order(p, k, rng):
    """An element of exact multiplicative order k in Z_p^*, or None."""
    fac = _prime_factors(k)
    for _ in range(60):
        x = rng.randrange(2, p)
        r = pow(x, (p - 1) // k, p)
        if pow(r, k, p) == 1 and all(pow(r, k // q, p) != 1 for q in fac):
            return r
    return None


def _sample_affine(lo, hi, rng):
    """Return (order, mul) for a random Z_p x| Z_k with lo <= p*k <= hi, or None."""
    cands = [(p, k) for (p, k) in _AFFINE if lo <= p * k <= hi]
    if not cands:
        return None
    for _ in range(20):
        p, k = rng.choice(cands)
        r = _elem_of_order(p, k, rng)
        if r is None:
            continue
        try:
            order, mul, _ = lib.semidirect_group(p, k, r)
        except ValueError:
            continue
        return order, mul
    return None


def _right_perm(mul, G, s):
    """Permutation g -> mul(g, s) of the group."""
    return [mul(g, s) for g in range(G)]


def _cost(k, G, D, darts, perms, limit=float("inf")):
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
        if total > limit:
            return total
    return total


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, mul, rng, deadline, run_secs, iters):
    """Simulated annealing over voltages and per-layer B-assignments."""
    t0 = time.monotonic()
    end = min(deadline, t0 + run_secs)
    span = max(1e-6, end - t0)

    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

    for it in range(iters):
        if cost == 0:
            break
        now = time.monotonic()
        if now >= end:
            break
        frac = max(it / iters, (now - t0) / span)
        T = 0.05 ** min(1.0, frac)
        u = 1.0 - rng.random()
        limit = cost - T * math.log(u)

        if rng.random() < 0.7 or k == 1:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_perm = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = _right_perm(mul, G, new_s)
            c2 = _cost(k, G, D, darts, perms, limit)
            if c2 <= limit:
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_perm
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
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, min(0.9 * time_limit, time_limit - 3.0))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    def consider_grown(n, e):
        consider(n, e)
        if time.monotonic() < deadline:
            n2, e2 = _twin_grow(n, e, d, D, rng)
            if n2 > n:
                e2 = _saturate_edges(n2, e2, d, rng)
                consider(n2, e2)

    # Kautz double covers (any D >= 2).
    try:
        kautz_deadline = start + 0.2 * time_limit
        for n_c, e_c in _kautz_cover_candidates(d, D, start + 0.1 * time_limit):
            consider(n_c, e_c)
            e_s = _saturate_edges(n_c, e_c, d, rng)
            consider(n_c, e_s)
            n2, e2 = _grow(n_c, e_s, d, D, kautz_deadline, rng)
            consider_grown(n2, e2)
    except Exception:
        pass

    # Diameter-3 bases (also used as seeds for larger D).
    if D >= 3 and best_n < moore:
        try:
            ara = _araujo_best(d)
            if ara is not None:
                consider_grown(ara[0], ara[1])
                n2, e2 = _grow(ara[0], ara[1], d, D, start + 0.25 * time_limit,
                               random.Random(seed + 2))
                consider_grown(n2, e2)
        except Exception:
            pass
        try:
            pg = _best_pg(d)
            if pg is not None:
                consider_grown(pg[0], pg[1])
                n2, e2 = _grow(pg[0], pg[1], d, D, start + 0.3 * time_limit,
                               random.Random(seed + 1))
                consider_grown(n2, e2)
        except Exception:
            pass
        try:
            pc = _polarity_cover(d)
            if pc is not None:
                consider_grown(pc[0], pc[1])
                n2, e2 = _grow(pc[0], pc[1], d, D, start + 0.33 * time_limit,
                               random.Random(seed + 5))
                consider_grown(n2, e2)
        except Exception:
            pass
        try:
            for n_c, e_c in _arc_extensions(d, start + 0.36 * time_limit,
                                            random.Random(seed * 7919 + d)):
                consider_grown(n_c, e_c)
        except Exception:
            pass

    # NEW bold stage: bi-Cayley graphs over groups of order just above best/2,
    # targeted at the weakest cases (large d, D >= 4). Falls back to the
    # existing best graph if no candidate validates.
    if D >= 4 and d >= 5 and best_n < moore and time.monotonic() < start + 0.7 * time_limit:
        try:
            _k1_ladder(d, D, moore, random.Random(seed * 31 + d), start + 0.7 * time_limit,
                       consider, lambda: best_n)
        except Exception:
            pass

    # Main search: annealed group voltage lifts (semidirect and affine families).
    ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
    affine_prob = 0.35 if D >= 5 else 0.15
    span = 0.125
    SPAN_MIN, SPAN_MAX = 1.0 / 16, 0.5
    while time.monotonic() < deadline and best_n < moore:
        k = rng.choice(ks)
        base = best_n // (2 * k)
        if rng.random() < affine_prob:
            lo = base + 1
            hi = base + max(3, int(base * span) + 1)
            g = _sample_affine(lo, hi, rng)
        else:
            G = max(2, base + 1 + rng.randrange(0, max(3, int(base * span) + 1)))
            g = _sample_group(G, rng)
        if g is None:
            span = max(SPAN_MIN, span * 0.97)
            continue
        order, mul = g
        res = _anneal(d, D, k, order, mul, rng, deadline, run_secs=3.0, iters=1200)
        if res is not None and res[0] > best_n:
            consider_grown(res[0], res[1])
            span = min(SPAN_MAX, span * 1.25)
        elif res is not None:
            consider(res[0], res[1])
        else:
            span = max(SPAN_MIN, span * 0.9)

    # Final polish: twin cloning into spare degree, then saturation.
    if D >= 2:
        try:
            n2, e2 = _twin_grow(best[0], best[1], d, D, rng)
            if n2 > best[0]:
                e2 = _saturate_edges(n2, e2, d, rng)
                consider(n2, e2)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
