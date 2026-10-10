import itertools
import math
import random
import time

import numpy as np

import lib

N_CAP = 6000          # hard cap on vertex count
ITERS = 6000          # cyclic annealing moves per attempt
ITERS_G = 800         # group annealing moves per attempt
S_LIST = (1, 2, 3, 4, 5, 6)
GQ_Q_MAX = 9          # largest q for which W(q) is built
RETRIES = 2           # cyclic annealing restarts per size
TOTAL_FRAC = 0.8      # fraction of time_limit used overall
LOOP_FRAC = 0.75      # share of the working window spent on the family search
GROW_FRAC = 0.15      # share of the working window for growth of base graphs


# ---------------------------------------------------------------- algebraic bases

def _best_pg(d):
    """Incidence graph of PG(2, q), q the largest prime power with q <= d - 1 (degree q + 1 <= d)."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


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
    """W(q) for the largest prime power q <= min(d - 1, GQ_Q_MAX)."""
    for q in range(min(d - 1, GQ_Q_MAX), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ---------------------------------------------------------------- shared graph helpers

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
    """Proper 2-colouring of a bipartite graph given by adjacency lists."""
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


def _extend_cover(n, edges, d, D, deadline):
    """Greedily add vertices whose neighbourhoods cover everything within radius D-1.

    A new vertex joined to a set S of deficient opposite-side vertices is within D of
    every old vertex when the radius-(D-1) balls of S cover the graph. Old distances
    only shrink, so validity is preserved.
    """
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
            covered = 0
            chosen = []
            pool = set(cands)
            while covered != full and len(chosen) < d and pool:
                best_s, best_g = None, 0
                for s in pool:
                    g = (ball[s] & ~covered).bit_count()
                    if g > best_g:
                        best_g, best_s = g, s
                if best_s is None:
                    break
                chosen.append(best_s)
                covered |= ball[best_s]
                pool.discard(best_s)
            if covered == full and chosen:
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
    """Join deficient opposite-side non-adjacent vertices. Never increases a distance."""
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
    """Alternate saturation and cover extension until neither adds anything."""
    cur_n, cur_e = n, list(edges)
    for _ in range(8):
        if time.monotonic() >= deadline:
            break
        cur_e = _saturate_edges(cur_n, cur_e, d, rng)
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline)
        if n2 == cur_n:
            break
        cur_n, cur_e = n2, e2
    return cur_n, cur_e


# ---------------------------------------------------------------- Haar graphs

def _search_haar(d, D, m, rng, deadline, iters):
    """Hill-climb S (|S| = d, 0 in S) in Z_m so the Haar graph has diameter <= D."""
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


# ---------------------------------------------------------------- cyclic lifts (numpy annealing)

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
    """Anneal permutations and voltages of a cyclic lift. Returns (P, V) with zero cost, or None."""
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
    """Materialise a cyclic lift as (n, edges)."""
    Pinv = np.zeros_like(P)
    for k in range(d):
        for i in range(s):
            Pinv[k, P[k, i]] = i
    nbr = _neighbors(P, Pinv, V, s, m)
    edges = set()
    for x in range(s * m):
        for y in nbr[x].tolist():
            edges.add((min(x, y), max(x, y)))
    return 2 * s * m, sorted(edges)


def _cyclic_attempt(d, D, best_n, cap, rng, deadline):
    """Try one cyclic lift just larger than the current best. Returns (n, edges) or None."""
    s = rng.choice(S_LIST)
    m = max(2, best_n // (2 * s) + 1)
    if 2 * s * m > cap:
        return None
    st = None
    for _ in range(RETRIES):
        if time.monotonic() > deadline:
            break
        st = _anneal(s, m, d, D, rng, deadline)
        if st is not None:
            break
    if st is None:
        return None
    return _graph(s, m, st[0], st[1], d)


# ---------------------------------------------------------------- semidirect-group lifts

# Group Z_m x|_r Z_k, element (a, b) coded as a*k + b, (a,b)(c,d) = (a + r^b c, b + d).

def _gmul(X, Y, m, k, powers):
    """Vectorised group product."""
    a1, b1 = X // k, X % k
    a2, b2 = Y // k, Y % k
    a = (a1 + powers[b1] * a2) % m
    b = (b1 + b2) % k
    return a * k + b


def _ginv(g, m, k, powers):
    """Inverse of a scalar group code."""
    a, b = g // k, g % k
    nb = (-b) % k
    c = (-int(powers[nb]) * a) % m
    return c * k + nb


def _gcol(nbr, kk, sig, sinv, G, s, M, m, k, powers):
    """Fill neighbour column kk for every lift vertex."""
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
    """Deduplicated edge list from a neighbour table."""
    n, d = nbr.shape
    xs = np.repeat(np.arange(n, dtype=np.int64), d)
    ys = nbr.reshape(-1)
    lo = np.minimum(xs, ys)
    hi = np.maximum(xs, ys)
    return sorted(set(zip(lo.tolist(), hi.tolist())))


def _group_attempt(d, D, best_n, cap, rng, deadline):
    """Try one semidirect-group lift just larger than the current best. Returns (n, edges) or None."""
    s = rng.choice((1, 1, 2, 2, 3, 4))
    hi = cap // (2 * s)
    if hi < 2:
        return None
    lo = max(2, best_n // (2 * s) + 1)
    if lo > hi:
        return None
    M = rng.randint(lo, min(hi, lo + max(1, lo // 8)))
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
            return None
        r = rng.choice(rs)
    powers = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
    nbr = _gsolve(s, M, m, k, powers, d, D, rng, deadline)
    if nbr is None:
        return None
    return 2 * s * M, _nbr_edges(nbr)


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    end = start + max(0.5, TOTAL_FRAC * time_limit - 1.0)
    loop_end = start + LOOP_FRAC * (end - start)
    rng = random.Random(seed)

    # Trivial cases.
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D                       # even cycle: bipartite, diameter D, Moore-extremal
        return L, [(i, (i + 1) % L) for i in range(L)]

    # Fallback and D = 2 answer: K_{d,d}.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    if D == 2:
        return best

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    grow_end = lambda: min(loop_end, time.monotonic() + GROW_FRAC * (end - start))

    # D >= 3: projective plane (diameter 3).
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best                 # Moore-extremal for D = 3
            n2, e2 = _grow(pg[0], pg[1], d, D, grow_end(), rng)
            consider(n2, e2)

    # D >= 4: generalized quadrangle W(q) (diameter 4).
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and lib.is_prime_power(d - 1) and d - 1 <= GQ_Q_MAX:
                return best                 # Moore-extremal for D = 4
            n2, e2 = _grow(gq[0], gq[1], d, D, grow_end(), rng)
            consider(n2, e2)

    cap = min(N_CAP, lib._moore_bound(d, D))

    # Adaptive family scheduling: Haar, cyclic lifts, and (D >= 4) group lifts.
    weight = {"haar": 1.0, "cyclic": 1.0, "group": 2.0 if D >= 4 else 0.0}
    floor, wcap = 0.05, 10.0
    haar_m, haar_miss = d + 1, 0

    while time.monotonic() < loop_end:
        if haar_miss >= 4 or 2 * haar_m > cap:
            haar_miss = 4
        fams = [f for f in ("haar", "cyclic", "group")
                if weight[f] > 0 and not (f == "haar" and haar_miss >= 4)]
        if not fams:
            break
        total = sum(weight[f] for f in fams)
        r = rng.random() * total
        fam = fams[-1]
        for f in fams:
            r -= weight[f]
            if r <= 0:
                fam = f
                break

        before = best_n
        if fam == "haar":
            S = _search_haar(d, D, haar_m, rng, loop_end, 120)
            if S is not None:
                consider(*lib.haar_graph(haar_m, S))
                haar_miss = 0
            else:
                haar_miss += 1
            haar_m += 1
        elif fam == "cyclic":
            res = _cyclic_attempt(d, D, best_n, cap, rng, loop_end)
            if res is not None:
                consider(*res)
        else:
            res = _group_attempt(d, D, best_n, cap, rng, loop_end)
            if res is not None:
                consider(*res)

        if best_n > before:
            weight[fam] = min(wcap, weight[fam] * 1.5)
        else:
            weight[fam] = max(floor, weight[fam] * 0.95)

    # Post-processing: fill spare degree and grow the best graph found.
    n2, e2 = _grow(best[0], best[1], d, D, end, rng)
    consider(n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
