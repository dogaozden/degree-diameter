import itertools
import math
import random
import time

import numpy as np

import lib

N_CAP = 6000                  # hard cap on vertex count
ITERS = 6000                  # annealing iterations per attempt (cyclic lifts)
S_LIST = (1, 2, 3, 4, 5, 6)   # number of base vertices per side (cyclic lifts)
GQ_Q_MAX = 9                  # largest q for which W(q) is built (pair loop is O(P^2))
RETRIES = 2                   # annealing attempts per candidate lift size
TIME_FRAC = 0.6               # fraction of parent time_limit used for the main search
POST_FRAC = 0.7               # fraction of parent time_limit after which post-processing stops
ILS_FRAC = 0.85               # fraction of parent time_limit after which ILS stops
GROW_SLICE = 0.5              # seconds per greedy growth variant (base graphs)
POST_LIFTS = 3                # number of largest lifts that get post-processing
POST_SLICE = 0.5              # seconds per growth variant on a lift
ILS_STEP = 0.5                # seconds allowed for one remove-and-regrow step
ILS_SLACK = 2                 # ILS may wander at most this far below the best size
ILS_DOWN_P = 0.2              # chance to accept a one-vertex shrink
REPAIR_FRAC = 0.1             # fraction of time_limit for repairing near-miss lifts

# Group-lift branch (semidirect products, representative-BFS evaluator).
ITERS_GROUP = 600             # hill-climb moves per group-lift attempt
PARENT_SHARE = 0.45           # share of time_limit given to the parent pipeline
G_FRAC = 0.85                 # group search runs until this fraction of time_limit
_BIG = 10 ** 9


# ---------------------------------------------------------------- shared helpers

def _two_colour(n, edges):
    """Return a proper 2-colouring (0/1 per vertex) of a bipartite graph, component by component."""
    adj = lib.adjacency(n, edges)
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


def _greedy_cover(cand, sets, target, budget):
    """Pick at most `budget` candidates whose `sets` bitmasks jointly cover `target`.

    Returns the chosen list (possibly empty if target is already covered), or None.
    """
    cand = list(cand)
    covered = 0
    chosen = []
    while (target & ~covered) and len(chosen) < budget and cand:
        best_u, best_gain = -1, 0
        for u in cand:
            g = (sets[u] & target & ~covered).bit_count()
            if g > best_gain:
                best_u, best_gain = u, g
        if best_u < 0:
            break
        chosen.append(best_u)
        covered |= sets[best_u]
        cand.remove(best_u)
    if target & ~covered:
        return None
    return chosen


def _extend(n, edges, d, D, rng, deadline):
    """Greedily add new vertices, each attached to a set cover of the current graph."""
    edges = list(edges)
    if D < 2 or n == 0:
        return n, edges
    color = _two_colour(n, edges)
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1

    while time.monotonic() < deadline:
        full = (1 << n) - 1
        balls = lib._balls(n, edges, D - 1)
        grown = False
        order = [0, 1] if rng.random() < 0.5 else [1, 0]
        for c in order:
            cand = [u for u in range(n) if color[u] == 1 - c and deg[u] < d]
            rng.shuffle(cand)
            covered, chosen = 0, []
            while covered != full and len(chosen) < d and cand:
                best_u, best_gain = -1, 0
                for u in cand:
                    g = (balls[u] & ~covered).bit_count()
                    if g > best_gain:
                        best_u, best_gain = u, g
                if best_u < 0:
                    break
                chosen.append(best_u)
                covered |= balls[best_u]
                cand.remove(best_u)
            if covered == full and chosen:
                x = n
                n += 1
                color.append(c)
                deg.append(len(chosen))
                for u in chosen:
                    edges.append((u, x))
                    deg[u] += 1
                grown = True
                break
        if not grown:
            break
    return n, edges


def _pair_extend(n, edges, d, D, rng, deadline):
    """Add two adjacent new vertices x (side c) and y (side 1-c) at once."""
    edges = list(edges)
    if D < 3 or n == 0 or d < 2:
        return n, edges
    color = _two_colour(n, edges)
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1

    while time.monotonic() < deadline:
        full = (1 << n) - 1
        b1 = lib._balls(n, edges, D - 1)
        b2 = lib._balls(n, edges, D - 2)
        placed = False
        order = [0, 1] if rng.random() < 0.5 else [1, 0]
        for c in order:
            side_other = [u for u in range(n) if color[u] == 1 - c and deg[u] < d]
            side_c = [u for u in range(n) if color[u] == c and deg[u] < d]
            N = _greedy_cover(side_other, b1, full, d - 1)
            if not N:
                continue
            b2N = 0
            for u in N:
                b2N |= b2[u]
            M = _greedy_cover(side_c, b1, full & ~b2N, d - 1)
            if M is None:
                continue
            x, y = n, n + 1
            n += 2
            color.append(c)
            color.append(1 - c)
            deg.append(len(N) + 1)
            deg.append(len(M) + 1)
            for u in N:
                edges.append((u, x))
                deg[u] += 1
            for u in M:
                edges.append((u, y))
                deg[u] += 1
            edges.append((x, y))
            placed = True
            break
        if not placed:
            break
    return n, edges


def _grow(n, edges, d, D, rng, deadline):
    """Alternate single-vertex and paired greedy extension until neither adds anything."""
    prev = -1
    while n != prev and time.monotonic() < deadline:
        prev = n
        n, edges = _extend(n, edges, d, D, rng, deadline)
        n, edges = _pair_extend(n, edges, d, D, rng, deadline)
    return n, edges


def _augment(n, edges, d, seed):
    """Add edges between opposite colour classes using spare degree."""
    rng = random.Random(seed + 7)
    color = _two_colour(n, edges)
    deg = [0] * n
    adj = [set() for _ in range(n)]
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
        adj[u].add(v)
        adj[v].add(u)
    side0 = [u for u in range(n) if color[u] == 0]
    side1 = [v for v in range(n) if color[v] == 1]
    new_edges = list(edges)
    for _ in range(3):
        us = [u for u in side0 if deg[u] < d]
        rng.shuffle(us)
        for u in us:
            if deg[u] >= d:
                continue
            cands = [v for v in side1 if deg[v] < d and v not in adj[u]]
            if not cands:
                continue
            v = rng.choice(cands)
            adj[u].add(v)
            adj[v].add(u)
            deg[u] += 1
            deg[v] += 1
            new_edges.append((u, v))
    return n, new_edges


def _growth_variants(g, d, D, rng, end, slice_s):
    """Run both greedy growth styles on graph g."""
    out = []
    for fn in (_extend, _grow):
        e = min(end, time.monotonic() + slice_s)
        out.append(fn(g[0], g[1], d, D, rng, e))
    return out


def _best_valid(cands, d, D):
    """Return the largest candidate that passes lib.is_valid, or None."""
    for n, e in sorted(cands, key=lambda c: -c[0]):
        if lib.is_valid(n, e, d, D):
            return n, e
    return None


def _finish(cands, d, D):
    """Return the largest candidate that passes lib.is_valid, else K_{d,d}."""
    best = _best_valid(cands, d, D)
    if best is not None:
        return best
    return lib.haar_graph(d, range(d))


# ---------------------------------------------------------------- iterated remove-and-regrow

def _remove_vertex(n, edges, v):
    """Return (n-1, edges) with vertex v deleted and the remaining labels compacted."""
    out = []
    for a, b in edges:
        if a == v or b == v:
            continue
        a2 = a - 1 if a > v else a
        b2 = b - 1 if b > v else b
        out.append((a2, b2))
    return n - 1, out


def _ils(n, edges, d, D, rng, end):
    """Iterated local search: delete a random vertex, regrow, accept if valid and not too small."""
    cur = (n, list(edges))
    best = cur
    while time.monotonic() < end:
        n0, e0 = cur
        if n0 < 4:
            break
        v = rng.randrange(n0)
        m, e1 = _remove_vertex(n0, e0, v)
        step_end = min(end, time.monotonic() + ILS_STEP)
        m, e2 = _grow(m, e1, d, D, rng, step_end)
        if m < best[0] - ILS_SLACK:
            continue
        accept = m >= n0 or (m == n0 - 1 and rng.random() < ILS_DOWN_P)
        if accept and lib.is_valid(m, e2, d, D):
            cur = (m, e2)
            if m > best[0]:
                best = (m, e2)
    return best


# ---------------------------------------------------------------- bad-pair repair

def _repair(n, edges, d, D, rng, deadline):
    """Delete the vertices involved in the most bad pairs until every pair is within D."""
    edges = list(edges)
    while n > 2 and time.monotonic() < deadline:
        balls = lib._balls(n, edges, D)
        bad = [n - r.bit_count() for r in balls]
        if not any(bad):
            break
        k = max(1, n // 40)
        order = sorted(range(n), key=lambda v: (-bad[v], rng.random()))
        chosen = [v for v in order[:k] if bad[v] > 0]
        for v in sorted(chosen, reverse=True):
            n, edges = _remove_vertex(n, edges, v)
    return n, edges


# ---------------------------------------------------------------- D = 3 : projective plane

def _pg_base(d):
    """Incidence graph of PG(2,q), q the largest prime power <= d-1."""
    q = d - 1
    while q >= 2 and not lib.is_prime_power(q):
        q -= 1
    if q < 2:
        return None
    return lib.projective_plane_incidence(q)


# ---------------------------------------------------------------- D = 3 : polarity double cover

def _polarity_cover(q):
    """Bipartite double cover of the Erdos-Renyi polarity graph ER_q."""
    F = lib.GF(q)
    pts = np.array(lib.projective_points(q), dtype=np.int64)
    m = len(pts)
    mul, add = F.mul_table, F.add_table
    terms = [mul[pts[:, None, c], pts[None, :, c]] for c in range(3)]
    dot = add[add[terms[0], terms[1]], terms[2]]
    A = (dot == 0)
    np.fill_diagonal(A, False)
    rows, cols = np.nonzero(np.triu(A, 1))
    edges = []
    for i, j in zip(rows.tolist(), cols.tolist()):
        edges.append((i, m + j))
        edges.append((j, m + i))
    return 2 * m, edges


def _er_base(d):
    """Polarity double cover for the largest prime power q <= d-1."""
    q = d - 1
    while q >= 2 and not lib.is_prime_power(q):
        q -= 1
    if q < 2:
        return None
    return _polarity_cover(q)


# ---------------------------------------------------------------- D >= 4 : generalized quadrangle

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q)."""
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
    """W(q) for the largest prime power q with q <= d-1 and q <= GQ_Q_MAX."""
    for q in range(min(d - 1, GQ_Q_MAX), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ---------------------------------------------------------------- Haar graphs (hill-climb)

def _search_haar(d, D, m, rng, deadline, iters):
    """Hill-climb a connection set S (|S| = d, containing 0) in Z_m so the Haar graph has diameter <= D."""
    others = list(range(1, m))
    if len(others) < d - 1:
        return None

    def cost(S):
        n, edges = lib.haar_graph(m, S)
        return lib.bad_pairs(n, edges, D)

    S = [0] + rng.sample(others, d - 1)
    c = cost(S)
    for _ in range(iters):
        if c == 0:
            return S
        if time.monotonic() >= deadline:
            break
        cand = [x for x in others if x not in S]
        if not cand:
            break
        i = rng.randrange(1, d)
        T = S[:]
        T[i] = rng.choice(cand)
        ct = cost(T)
        if ct <= c:
            S, c = T, ct
    return S if c == 0 else None


# ---------------------------------------------------------------- cyclic lifts (annealing)

def _neighbors(P, Pinv, V, s, m):
    """Neighbour table (n x d) of the Z_m lift of a d-regular bipartite base on s+s vertices."""
    d = P.shape[0]
    g = np.arange(m, dtype=np.int64)
    nbr = np.empty((2 * s * m, d), dtype=np.int64)
    for k in range(d):
        for i in range(s):
            j = int(P[k, i])
            nbr[i * m:(i + 1) * m, k] = s * m + j * m + (g + int(V[k, i])) % m
        for j in range(s):
            i = int(Pinv[k, j])
            nbr[(s + j) * m:(s + j + 1) * m, k] = i * m + (g - int(V[k, i])) % m
    return nbr


def _cost(nbr, sources, D):
    """Number of (source, vertex) pairs NOT within distance D. Zero iff the lift is valid."""
    n = nbr.shape[0]
    S = len(sources)
    R = np.zeros((S, n), dtype=bool)
    R[np.arange(S), sources] = True
    for _ in range(D):
        M = R.copy()
        for k in range(nbr.shape[1]):
            M |= R[:, nbr[:, k]]
        if np.array_equal(M, R):
            break
        R = M
    return int(S * n - np.count_nonzero(R))


def _swap(P, Pinv, k, a, b):
    P[k, a], P[k, b] = P[k, b], P[k, a]
    Pinv[k, P[k, a]] = a
    Pinv[k, P[k, b]] = b


def _anneal_any(s, m, d, D, rng, deadline):
    """Simulated annealing over permutations and voltages. Returns (final_cost, P, V)."""
    P = np.array([rng.sample(range(s), s) for _ in range(d)], dtype=np.int64)
    Pinv = np.zeros_like(P)
    for k in range(d):
        for i in range(s):
            Pinv[k, P[k, i]] = i
    V = np.array([[rng.randrange(m) for _ in range(s)] for _ in range(d)], dtype=np.int64)
    sources = [i * m for i in range(2 * s)]
    nbr = _neighbors(P, Pinv, V, s, m)
    cur = _cost(nbr, sources, D)
    for it in range(ITERS):
        if cur == 0 or time.monotonic() > deadline:
            break
        temp = 2.0 * (1.0 - it / ITERS) + 0.05
        if s == 1 or rng.random() < 0.7:
            k, i = rng.randrange(d), rng.randrange(s)
            old = int(V[k, i])
            new_v = rng.randrange(m)
            if new_v == old:
                continue
            V[k, i] = new_v
            cand = _neighbors(P, Pinv, V, s, m)
            c = _cost(cand, sources, D)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur, nbr = c, cand
            else:
                V[k, i] = old
        else:
            k = rng.randrange(d)
            a, b = rng.sample(range(s), 2)
            _swap(P, Pinv, k, a, b)
            cand = _neighbors(P, Pinv, V, s, m)
            c = _cost(cand, sources, D)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur, nbr = c, cand
            else:
                _swap(P, Pinv, k, a, b)
    return cur, P.copy(), V.copy()


def _graph(s, m, P, V, d):
    """Materialise the cyclic lift as (n, edges), deduplicated."""
    Pinv = np.zeros_like(P)
    for k in range(d):
        for i in range(s):
            Pinv[k, P[k, i]] = i
    nbr = _neighbors(P, Pinv, V, s, m)
    edges = set()
    for x in range(s * m):
        for y in nbr[x].tolist():
            edges.add((x, y))
    return 2 * s * m, sorted(edges)


def _try_size(s, m, d, D, rng, deadline):
    """Attempt to anneal a valid lift of size m, with a few restarts."""
    worst = None
    for _ in range(RETRIES):
        if time.monotonic() > deadline:
            break
        cost, P, V = _anneal_any(s, m, d, D, rng, deadline)
        if cost == 0:
            return (P, V), None
        if worst is None or cost < worst[0]:
            worst = (cost, P, V)
    return None, worst


def _search(s, d, D, rng, deadline, cap):
    """For fixed s, find the largest m whose cyclic lift passes annealing. Returns (best, near)."""
    best = None
    near = None
    lo, hi = 0, None
    m = 1
    while time.monotonic() < deadline:
        if 2 * s * m > cap:
            hi = m
        else:
            st, miss = _try_size(s, m, d, D, rng, deadline)
            if st is not None:
                lo = m
                best = (m, st[0], st[1])
            else:
                hi = m
                if miss is not None:
                    ratio = miss[0] / (2 * s * m)
                    if near is None or ratio < near[0]:
                        near = (ratio, m, miss[1], miss[2])
        if hi is None:
            m = 2 * lo
        else:
            if hi - lo <= 1:
                break
            m = (lo + hi) // 2
    return best, near


# ---------------------------------------------------------------- semidirect-group lifts (g006 evaluator)

# Group G = Z_m x|_r Z_k, element (a, b) coded as a*k + b, product (a,b)(c,d) = (a + r^b c, b + d).
# Left multiplication is an automorphism of the bi-Cayley lift, so BFS from one representative
# per base class decides diameter for the whole graph.

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
    """Permutation g -> g*s of the group."""
    return [mul(g, s) for g in range(G)]


def _gadj(k, G, darts, perms):
    """Adjacency lists (multiset) of the bi-Cayley lift described by darts and perms."""
    adj = [[] for _ in range(2 * k * G)]
    for (i, j, _s), pm in zip(darts, perms):
        _gdart_edges(adj, k, G, i, j, pm, 1)
    return adj


def _gdart_edges(adj, k, G, i, j, pm, sign):
    """Add (sign=+1) or remove (sign=-1) the matching edges of one dart from adj."""
    base_a = i * G
    base_b = (k + j) * G
    for g in range(G):
        a = base_a + g
        b = base_b + pm[g]
        if sign > 0:
            adj[a].append(b)
            adj[b].append(a)
        else:
            adj[a].remove(b)
            adj[b].remove(a)


def _gcost(k, G, D, darts, adj, bound):
    """Number of (representative, vertex) pairs not reached within distance D.

    Zero means valid. Stops early and returns a value above `bound` once the running
    total exceeds `bound`, since the caller would reject such a move anyway.
    """
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
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
        if total > bound:
            return total
    return total


def _gedges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _gsearch(k, G, d, D, rng, iters, deadline):
    """Hill-climb voltages in a random semidirect group of order G with k base vertices per side."""
    g = _sample_group(G, rng)
    if g is None:
        return None
    order, mul = g
    G = order
    layers = [rng.sample(range(k), k) for _ in range(d)]
    darts = []
    for p in layers:
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    adj = _gadj(k, G, darts, perms)
    cost = _gcost(k, G, D, darts, adj, _BIG)

    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        idx = rng.randrange(len(darts))
        i, j, old_s = darts[idx]
        old_perm = perms[idx]
        new_s = rng.randrange(G)
        new_perm = _right_perm(mul, G, new_s)
        # A move is accepted if it does not increase cost, or with small probability regardless.
        # Drawing the random acceptance first lets the evaluator prune against the current cost.
        accept_anyway = rng.random() < 0.02
        bound = _BIG if accept_anyway else cost
        _gdart_edges(adj, k, G, i, j, old_perm, -1)
        _gdart_edges(adj, k, G, i, j, new_perm, 1)
        darts[idx][2] = new_s
        perms[idx] = new_perm
        c2 = _gcost(k, G, D, darts, adj, bound)
        if c2 <= bound:
            cost = c2
        else:
            _gdart_edges(adj, k, G, i, j, new_perm, -1)
            _gdart_edges(adj, k, G, i, j, old_perm, 1)
            darts[idx][2] = old_s
            perms[idx] = old_perm

    if cost == 0:
        return _gedges(k, G, darts, perms)
    return None


def _group_search(d, D, seed, deadline, cap):
    """Random search over bi-Cayley lifts over semidirect products, growing the order."""
    rng = random.Random(seed * 1000003 + 17)
    best = None
    best_n = 0
    while time.monotonic() < deadline:
        if best_n >= cap:
            break
        k = rng.choice([1, 1, 1, 2, 2, 3])
        base = best_n // (2 * k)
        G = max(2, base + 1 + rng.randrange(0, max(3, base // 6 + 1)))
        if 2 * k * G > cap:
            G = cap // (2 * k)
            if G < 2:
                continue
        res = _gsearch(k, G, d, D, rng, ITERS_GROUP, deadline)
        if res is not None:
            n, edges = res
            if n > best_n and lib.is_valid(n, edges, d, D):
                best_n, best = n, (n, edges)
    return best


# ---------------------------------------------------------------- driver

def _extremal(d, D):
    """True when the parent already returns a Moore-extremal (or near-extremal) construction."""
    if D == 3 and lib.is_prime_power(d - 1):
        return True
    if D == 4 and lib.is_prime_power(d - 1) and d - 1 <= GQ_Q_MAX:
        return True
    return False


def _parent_build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, TIME_FRAC * time_limit - 1.0)
    post_end = start + max(0.5, POST_FRAC * time_limit - 1.0)
    ils_end = start + max(0.5, ILS_FRAC * time_limit - 1.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if D == 2:
        return lib.haar_graph(d, range(d))

    cands = [lib.haar_graph(d, range(d))]   # K_{d,d}: diameter 2, always valid

    # D >= 3: projective plane / polarity cover, extended into spare degree.
    if d >= 3:
        base = _pg_base(d)
        if base is not None:
            if lib.is_prime_power(d - 1) and D == 3:
                return _finish(cands + [base], d, D)
            cands.append(base)
            aug = _augment(base[0], base[1], d, seed)
            for g in (base, aug):
                cands.extend(_growth_variants(g, d, D, rng,
                                              min(deadline, time.monotonic() + 2 * GROW_SLICE),
                                              GROW_SLICE))

        if D == 3:
            er = _er_base(d)
            if er is not None:
                cands.append(er)
                er_aug = _augment(er[0], er[1], d, seed + 1)
                for g in (er, er_aug):
                    cands.extend(_growth_variants(g, d, D, rng,
                                                  min(deadline, time.monotonic() + 2 * GROW_SLICE),
                                                  GROW_SLICE))

    # D >= 4: generalized quadrangle W(q).
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            if D == 4 and d - 1 <= GQ_Q_MAX and lib.is_prime_power(d - 1):
                return _finish(cands + [gq], d, D)
            cands.append(gq)
            aug = _augment(gq[0], gq[1], d, seed)
            for g in (gq, aug):
                cands.extend(_growth_variants(g, d, D, rng,
                                              min(deadline, time.monotonic() + 2 * GROW_SLICE),
                                              GROW_SLICE))

    cap = min(N_CAP, lib._moore_bound(d, D))

    # Haar graphs with growing modulus (small slice of remaining time).
    now = time.monotonic()
    haar_frac = 0.2 if D <= 4 else 0.1
    haar_end = now + haar_frac * max(0.0, deadline - now)
    haar_best, haar_m, haar_miss = None, d + 1, 0
    while time.monotonic() < haar_end and haar_miss < 4:
        S = _search_haar(d, D, haar_m, rng, haar_end, 120)
        if S is not None:
            haar_best = lib.haar_graph(haar_m, S)
            haar_miss = 0
        else:
            haar_miss += 1
        haar_m += 1
    if haar_best is not None:
        cands.append(haar_best)

    # Cyclic voltage-lift annealing, one slice per base size s.
    lifts = []
    nears = []
    for idx, s in enumerate(S_LIST):
        now = time.monotonic()
        if now >= deadline:
            break
        slice_end = now + (deadline - now) / (len(S_LIST) - idx)
        res, near = _search(s, d, D, rng, slice_end, cap)
        if near is not None:
            nears.append((s, near))
        if res is not None:
            m, P, V = res
            g = _graph(s, m, P, V, d)
            cands.append(g)
            lifts.append(g)

    # Post-process the largest lifts.
    lifts.sort(key=lambda g: -g[0])
    for g in lifts[:POST_LIFTS]:
        if time.monotonic() >= post_end:
            break
        aug = _augment(g[0], g[1], d, seed)
        cands.append(aug)
        cands.extend(_growth_variants(aug, d, D, rng, post_end, POST_SLICE))

    # Bad-pair repair on the least-bad failed lift per base size.
    rep_end = min(post_end, time.monotonic() + REPAIR_FRAC * time_limit)
    for s, (ratio, m, P, V) in nears:
        if time.monotonic() >= rep_end:
            break
        n0, e0 = _graph(s, m, P, V, d)
        n1, e1 = _repair(n0, e0, d, D, rng, rep_end)
        n1, e1 = _grow(n1, e1, d, D, rng, rep_end)
        cands.append((n1, e1))

    # Iterated remove-and-regrow on the best valid graph so far.
    if D >= 3 and time.monotonic() < ils_end:
        best = _best_valid(cands, d, D)
        if best is not None:
            cands.append(_ils(best[0], best[1], d, D, rng, ils_end))

    return _finish(cands, d, D)


def build(d, D, seed, time_limit):
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if D == 2:
        return lib.haar_graph(d, range(d))

    # Calibration / Moore-extremal / tiny-degree cases: parent pipeline alone.
    if d < 3 or _extremal(d, D):
        return _parent_build(d, D, seed, time_limit)

    start = time.monotonic()
    # Parent pipeline gets a share of the budget and serves as the safe fallback.
    fallback = _parent_build(d, D, seed, PARENT_SHARE * time_limit)

    # Group-lift search for the remaining budget.
    cap = min(N_CAP, lib._moore_bound(d, D))
    end = start + max(0.5, G_FRAC * time_limit - 1.0)
    cand = None
    try:
        cand = _group_search(d, D, seed, end, cap)
    except Exception:
        cand = None

    if cand is not None and cand[0] > fallback[0] and lib.is_valid(cand[0], cand[1], d, D):
        return cand
    return fallback
