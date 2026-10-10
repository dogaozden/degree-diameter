import itertools
import math
import random
import time

import numpy as np

import lib

N_CAP = 6000                  # hard cap on vertex count
ITERS = 6000                  # annealing iterations for cyclic lifts
ITERS_G = 800                 # annealing iterations for group lifts
S_LIST = (1, 2, 3, 4, 5, 6)   # base vertices per side for cyclic lifts
GQ_Q_MAX = 9                  # largest q for which W(q) is built
RETRIES = 2                   # annealing restarts per candidate size
GROUP_SIZES = (1, 2, 3, 4)    # base vertices per side for climbing group lifts

# Time fractions of the usable budget (usable = 0.82 * time_limit - 1 s).
F_BASE = 0.20                 # projective plane / quadrangle + growth
F_HAAR = 0.24                 # Haar graphs
F_CYC = 0.50                  # cyclic annealing lifts
F_POST = 0.56                 # growth of the best cyclic lifts
F_GROUP = 0.82                # group-lift searches (ILS uses the rest)


# ---------------------------------------------------------------- base constructions

def _pg_base(d):
    """Incidence graph of PG(2,q), q the largest prime power <= d-1."""
    q = d - 1
    while q >= 2 and not lib.is_prime_power(q):
        q -= 1
    if q < 2:
        return None
    return lib.projective_plane_incidence(q)


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q).

    Degree q + 1, diameter 4, order 2(q+1)(q^2+1).
    """
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
    """W(q) for the largest prime power q <= min(d-1, GQ_Q_MAX)."""
    for q in range(min(d - 1, GQ_Q_MAX), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ---------------------------------------------------------------- shared helpers

def _two_colour(n, edges):
    """Proper 2-colouring of a bipartite graph, component by component."""
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
    """Pick at most `budget` candidates whose bitmasks jointly cover `target`, or None."""
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
    """Add single new vertices, each joined to a radius-(D-1) cover of the current graph."""
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
    """Alternate single and paired greedy extension until neither adds anything."""
    prev = -1
    while n != prev and time.monotonic() < deadline:
        prev = n
        n, edges = _extend(n, edges, d, D, rng, deadline)
        n, edges = _pair_extend(n, edges, d, D, rng, deadline)
    return n, edges


def _augment(n, edges, d, seed):
    """Add edges between opposite colour classes using spare degree (keeps bipartite and diameter)."""
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


def _search_haar(d, D, m, rng, deadline, iters):
    """Hill-climb a connection set S (|S| = d, containing 0) in Z_m for a Haar graph of diameter <= D."""
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


# ---------------------------------------------------------------- iterated remove-and-regrow

def _remove_vertex(n, edges, v):
    out = []
    for a, b in edges:
        if a == v or b == v:
            continue
        a2 = a - 1 if a > v else a
        b2 = b - 1 if b > v else b
        out.append((a2, b2))
    return n - 1, out


def _ils(n, edges, d, D, rng, end):
    """Delete a random vertex, regrow, accept if valid and not much smaller. Returns best seen."""
    cur = (n, list(edges))
    best = cur
    while time.monotonic() < end:
        n0, e0 = cur
        if n0 < 4:
            break
        v = rng.randrange(n0)
        m, e1 = _remove_vertex(n0, e0, v)
        step_end = min(end, time.monotonic() + 0.5)
        m, e2 = _grow(m, e1, d, D, rng, step_end)
        if m < best[0] - 2:
            continue
        accept = m >= n0 or (m == n0 - 1 and rng.random() < 0.2)
        if accept and lib.is_valid(m, e2, d, D):
            cur = (m, e2)
            if m > best[0]:
                best = (m, e2)
    return best


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


def _anneal(s, m, d, D, rng, deadline):
    """Simulated annealing over permutations and voltages. Returns (P, V) with zero cost, or None."""
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
    if cur == 0:
        return P.copy(), V.copy()
    return None


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
    for _ in range(RETRIES):
        if time.monotonic() > deadline:
            break
        st = _anneal(s, m, d, D, rng, deadline)
        if st is not None:
            return st
    return None


def _search(s, d, D, rng, deadline, cap):
    """For fixed s, find the largest m (doubling then bisection) whose lift anneals to zero cost."""
    best = None
    lo, hi = 0, None
    m = 1
    while time.monotonic() < deadline:
        if 2 * s * m > cap:
            hi = m
        else:
            st = _try_size(s, m, d, D, rng, deadline)
            if st is not None:
                lo = m
                best = (m, st[0], st[1])
            else:
                hi = m
        if hi is None:
            m = 2 * lo
        else:
            if hi - lo <= 1:
                break
            m = (lo + hi) // 2
    return best


# ---------------------------------------------------------------- semidirect-group lifts (vectorised)

# Group Z_m x|_r Z_k, element (a, b) coded as a*k + b, product (a,b)(c,d) = (a + r^b c, b + d).
# Left multiplication is an automorphism of the lift, so checking the 2s vertices with
# group coordinate 0 decides the diameter for the whole graph.

def _gmul(X, Y, m, k, powers):
    a1, b1 = X // k, X % k
    a2, b2 = Y // k, Y % k
    a = (a1 + powers[b1] * a2) % m
    b = (b1 + b2) % k
    return a * k + b


def _ginv(g, m, k, powers):
    a, b = g // k, g % k
    nb = (-b) % k
    c = (-int(powers[nb]) * a) % m
    return c * k + nb


def _gcol(nbr, kk, sig, sinv, G, s, M, m, k, powers):
    Y = np.arange(M, dtype=np.int64)
    for i in range(s):
        j = int(sig[kk, i])
        g = int(G[kk, i])
        nbr[i * M:(i + 1) * M, kk] = s * M + j * M + _gmul(Y, g, m, k, powers)
    for j in range(s):
        i = int(sinv[kk, j])
        gi = _ginv(int(G[kk, i]), m, k, powers)
        nbr[s * M + j * M: s * M + (j + 1) * M, kk] = i * M + _gmul(Y, gi, m, k, powers)


def _gsolve(s, M, m, k, powers, d, D, rng, deadline):
    """Anneal darts of a group lift until diameter <= D. Returns neighbour table or None."""
    n = 2 * s * M
    sig = np.array([rng.sample(range(s), s) for _ in range(d)], dtype=np.int64)
    sinv = np.zeros_like(sig)
    for kk in range(d):
        for i in range(s):
            sinv[kk, sig[kk, i]] = i
    G = np.array([[rng.randrange(M) for _ in range(s)] for _ in range(d)], dtype=np.int64)
    nbr = np.empty((n, d), dtype=np.int64)
    for kk in range(d):
        _gcol(nbr, kk, sig, sinv, G, s, M, m, k, powers)
    sources = [i * M for i in range(s)] + [s * M + j * M for j in range(s)]
    cur = _cost(nbr, sources, D)
    for it in range(ITERS_G):
        if cur == 0 or time.monotonic() > deadline:
            break
        temp = 2.0 * (1.0 - it / ITERS_G) + 0.05
        if s == 1 or rng.random() < 0.6:
            kk, i = rng.randrange(d), rng.randrange(s)
            old = int(G[kk, i])
            new = rng.randrange(M)
            if new == old:
                continue
            G[kk, i] = new
            _gcol(nbr, kk, sig, sinv, G, s, M, m, k, powers)
            c = _cost(nbr, sources, D)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur = c
            else:
                G[kk, i] = old
                _gcol(nbr, kk, sig, sinv, G, s, M, m, k, powers)
        else:
            kk = rng.randrange(d)
            a, b = rng.sample(range(s), 2)
            _swap(sig, sinv, kk, a, b)
            _gcol(nbr, kk, sig, sinv, G, s, M, m, k, powers)
            c = _cost(nbr, sources, D)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur = c
            else:
                _swap(sig, sinv, kk, a, b)
                _gcol(nbr, kk, sig, sinv, G, s, M, m, k, powers)
    if cur == 0:
        return nbr
    return None


def _nbr_edges(nbr):
    n, d = nbr.shape
    xs = np.repeat(np.arange(n, dtype=np.int64), d)
    ys = nbr.reshape(-1)
    lo = np.minimum(xs, ys)
    hi = np.maximum(xs, ys)
    return sorted(set(zip(lo.tolist(), hi.tolist())))


def _group_search(d, D, seed, deadline, cap):
    """Random search over vectorised group lifts with growing order. Returns best valid (n, edges) or None."""
    rng = random.Random(seed * 1000003 + 17)
    best = None
    best_n = 0
    failhi = {}
    while time.monotonic() < deadline:
        if best_n >= cap:
            break
        s = rng.choice((1, 1, 2, 2, 3, 4))
        hi = cap // (2 * s)
        if hi < 2:
            continue
        lo = max(2, best_n // (2 * s) + 1)
        top = min(hi, failhi.get(s, hi + 1) - 1)
        if lo > top:
            failhi.pop(s, None)
            continue
        if rng.random() < 0.5:
            M = lo + rng.randint(0, min(top - lo, max(1, lo // 16)))
        else:
            M = rng.randint(lo, top)
        ks = [x for x in range(1, 9) if M % x == 0]
        k = rng.choice(ks)
        m = M // k
        if m == 1:
            r = 0
        elif k == 1:
            r = 1
        else:
            rs = [x for x in range(1, m) if math.gcd(x, m) == 1 and pow(x, k, m) == 1]
            if not rs:
                continue
            r = rng.choice(rs)
        powers = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
        nbr = _gsolve(s, M, m, k, powers, d, D, rng, deadline)
        if nbr is None:
            failhi[s] = min(failhi.get(s, M), M)
            continue
        n = 2 * s * M
        edges = _nbr_edges(nbr)
        if n > best_n and lib.is_valid(n, edges, d, D):
            best_n, best = n, (n, edges)
    return best


# ---------------------------------------------------------------- group lifts (lib-based climb)

def _sample_group(G, rng):
    """(order, mul) for a random semidirect product Z_m x| Z_k of order G, or None."""
    for _ in range(60):
        k2 = rng.randint(1, 12)
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in rng.sample(range(1, m), min(m - 1, 40))
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


def _group_climb(d, D, s, G, rng, iters, deadline):
    """Hill-climb dart voltages of a group lift over a random d-regular base with s+s vertices."""
    g = _sample_group(G, rng)
    if g is None:
        return None
    order, mul = g
    perms = [rng.sample(range(s), s) for _ in range(d)]
    darts = [[i, s + p[i], rng.randrange(order)] for p in perms for i in range(s)]

    def evaluate():
        n, e = lib.group_lift(2 * s, [tuple(x) for x in darts], order, mul)
        return n, e, lib.bad_pairs(n, e, D)

    n, e, c = evaluate()
    for _ in range(iters):
        if c == 0 or time.monotonic() > deadline or order < 2:
            break
        j = rng.randrange(len(darts))
        old = darts[j][2]
        darts[j][2] = (old + rng.randrange(1, order)) % order
        n2, e2, c2 = evaluate()
        if c2 <= c:
            n, e, c = n2, e2, c2
        else:
            darts[j][2] = old
    return (n, e) if c == 0 else None


def _climb_search(d, D, rng, deadline, best_n, cap):
    """Climb group lifts with growing group order. Returns best valid (n, edges) found, or None."""
    best = None
    state = {s: {"G": 2, "step": 1, "miss": 0} for s in GROUP_SIZES}
    while time.monotonic() < deadline and best_n < cap:
        s = rng.choice(GROUP_SIZES)
        st = state[s]
        floor = best_n // (2 * s) + 1
        G = max(st["G"], floor, 2)
        if 2 * s * G > cap + 2 * s:
            st.update(G=2, step=1, miss=0)
            continue
        res = _group_climb(d, D, s, G, rng, 200, deadline)
        if res is None:
            st["G"] = G
            st["miss"] += 1
            if st["miss"] >= 3:
                st.update(step=1, miss=0, G=floor)
        else:
            n, e = res
            if n > best_n and lib.is_valid(n, e, d, D):
                best_n, best = n, (n, e)
            st["G"] = G + st["step"]
            st["step"] = min(st["step"] * 2, max(1, G // 10))
            st["miss"] = 0
    return best


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = max(0.5, 0.82 * time_limit - 1.0)
    end = start + total

    def at(f):
        return start + f * total

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]
    if D == 2:
        return lib.haar_graph(d, range(d))

    # Moore-extremal shortcuts.
    if D == 3 and lib.is_prime_power(d - 1):
        cand = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(cand[0], cand[1], d, D):
            return cand
    if D == 4 and d - 1 <= GQ_Q_MAX and lib.is_prime_power(d - 1):
        cand = _gq_w(d - 1)
        if lib.is_valid(cand[0], cand[1], d, D):
            return cand

    # Best valid graph so far; K_{d,d} is always valid for D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    rng = random.Random(seed)
    cap = min(N_CAP, lib._moore_bound(d, D))

    # Phase 1: projective plane (D >= 3) and quadrangle (D >= 4), each grown and filled.
    bases = []
    pg = _pg_base(d)
    if pg is not None:
        bases.append(pg)
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            bases.append(gq)
    for idx, (n0, e0) in enumerate(bases):
        consider(n0, e0)
        now = time.monotonic()
        stop = now + max(1.0, (at(F_BASE) - now) / (len(bases) - idx))
        n1, e1 = _grow(n0, e0, d, D, rng, stop)
        consider(n1, e1)
        n2, e2 = _augment(n1, e1, d, seed + idx)
        consider(n2, e2)

    # Phase 2: Haar graphs with growing modulus.
    haar_m, haar_miss = d + 1, 0
    haar_end = at(F_HAAR)
    while time.monotonic() < haar_end and haar_miss < 4:
        S = _search_haar(d, D, haar_m, rng, haar_end, 120)
        if S is not None:
            consider(*lib.haar_graph(haar_m, S))
            haar_miss = 0
        else:
            haar_miss += 1
        haar_m += 1

    # Phase 3: cyclic voltage lifts by annealing, one slice per base size.
    lifts = []
    for idx, s in enumerate(S_LIST):
        now = time.monotonic()
        if now >= at(F_CYC):
            break
        slice_end = now + (at(F_CYC) - now) / (len(S_LIST) - idx)
        res = _search(s, d, D, rng, slice_end, cap)
        if res is not None:
            m, P, V = res
            g = _graph(s, m, P, V, d)
            consider(*g)
            lifts.append(g)

    # Phase 4: fill spare degree on, and grow, the largest cyclic lifts.
    lifts.sort(key=lambda g: -g[0])
    for g in lifts[:2]:
        if time.monotonic() >= at(F_POST):
            break
        n1, e1 = _augment(g[0], g[1], d, seed + 3)
        consider(n1, e1)
        now = time.monotonic()
        n2, e2 = _grow(n1, e1, d, D, rng, min(at(F_POST), now + 1.0))
        consider(n2, e2)

    # Phase 5: group lifts, half vectorised annealing and half lib-based climbing.
    g_start = time.monotonic()
    g_end = at(F_GROUP)
    if g_start < g_end:
        mid = g_start + 0.5 * (g_end - g_start)
        res = _group_search(d, D, seed, mid, cap)
        if res is not None:
            consider(*res)
        res = _climb_search(d, D, rng, g_end, best_n, cap)
        if res is not None:
            consider(*res)

    # Phase 6: iterated remove-and-regrow on the best graph.
    if time.monotonic() < end:
        res = _ils(best_n, best_e, d, D, rng, end)
        consider(*res)

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, best_e
