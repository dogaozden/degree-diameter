import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# NEW IDEA: cyclic Haar graphs with diameter 4 found by hill-climbing.
#
# H(m, S) has parts a_i, b_j (i, j in Z_m), with a_i ~ b_{i+s} for s in S, |S| = d.
# It is d-regular, bipartite, and vertex-transitive (the swap a_i <-> b_{-i} is an
# automorphism), so its diameter equals the eccentricity of a_0. Writing D for the
# difference set S - S, the vertices within distance 4 of a_0 are:
#   a-side:  {0} | D | D + D
#   b-side:  S + D
# So H(m, S) has diameter <= 4 iff both sets cover all of Z_m. The score
# |A| + |B| is hill-climbed by swapping one element of S at a time; success is
# score == 2m. Each success gives a verified order 2m, and m is pushed upward.
# ----------------------------------------------------------------------------

def _haar_score(m, S):
    Dset = {(s - t) % m for s in S for t in S}
    A = {(x + y) % m for x in Dset for y in Dset} | Dset | {0}
    B = {(s + x) % m for s in S for x in Dset}
    return len(A) + len(B)


def _haar_search(d, D, deadline, rng):
    """Largest m found with a cyclic Haar graph of degree d, diameter <= D (D = 4)."""
    moore = lib.moore_bound(d, D)
    best = None
    m = max(d + 1, moore // 5)
    while m <= moore // 2 and time.monotonic() < deadline:
        full = 2 * m
        for _ in range(30):
            if time.monotonic() >= deadline:
                break
            S = rng.sample(range(m), d)
            cur = _haar_score(m, S)
            for _ in range(600):
                if cur == full:
                    break
                i = rng.randrange(d)
                r = rng.randrange(m)
                if r in S:
                    continue
                T = S[:]
                T[i] = r
                sc = _haar_score(m, T)
                if sc >= cur:
                    S, cur = T, sc
            if cur == full:
                best = (m, sorted(S))
                break
        m += 1
    return best


# ----------------------------------------------------------------------------
# Base graph: incidence graph of the generalized quadrangle W(q), diameter 4.
# ----------------------------------------------------------------------------

def _gq_w(q):
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


# ----------------------------------------------------------------------------
# Diameter-preserving growth: a new vertex joined to S keeps diameter D if the
# radius-(D-1) balls of S cover every existing vertex.
# ----------------------------------------------------------------------------

def _balls(n, adj, r):
    ball = [1 << v for v in range(n)]
    for _ in range(r):
        nb = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            nb.append(x)
        ball = nb
    return ball


def _colour(n, adj):
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


def _grow(n, edges, d, D, deadline, rng):
    edges = list(edges)
    while time.monotonic() < deadline:
        adj = [[] for _ in range(n)]
        for u, v in edges:
            adj[u].append(v)
            adj[v].append(u)
        color = _colour(n, adj)
        ball = _balls(n, adj, D - 1)
        full = (1 << n) - 1
        added = False
        sides = [0, 1]
        rng.shuffle(sides)
        for c in sides:
            pool = [s for s in range(n) if color[s] == c and len(adj[s]) < d]
            chosen, covered = [], 0
            while covered != full and len(chosen) < d and pool:
                bs = max(pool, key=lambda s: (ball[s] & ~covered).bit_count())
                if (ball[bs] & ~covered) == 0:
                    break
                chosen.append(bs)
                covered |= ball[bs]
                pool.remove(bs)
            if chosen and covered == full:
                for s in chosen:
                    edges.append((s, n))
                n += 1
                added = True
                break
        if not added:
            break
    return n, edges


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = float(time_limit)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}, diameter 2

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 2:
        return best
    if best[0] >= lib.moore_bound(d, D):
        return best

    if D == 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                consider(*lib.projective_plane_incidence(q))
                break
        return best

    if D == 4 and d >= 3:
        # Phase 1: cyclic Haar graph search (new construction).
        hit = _haar_search(d, D, start + 0.70 * T, rng)
        if hit is not None:
            m, S = hit
            consider(*lib.haar_graph(m, S))

        # Phase 2: W(q) base plus diameter-preserving cover growth.
        if best[0] < lib.moore_bound(d, D) and time.monotonic() < start + 0.88 * T:
            qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)]
            if qs:
                try:
                    n0, e0 = _gq_w(qs[0])
                    consider(n0, e0)
                    n1, e1 = _grow(n0, e0, d, D, start + 0.88 * T, rng)
                    consider(n1, e1)
                except Exception:
                    pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
