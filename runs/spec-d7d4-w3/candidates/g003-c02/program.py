import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Generic graph helpers.
# ----------------------------------------------------------------------------

def _adjacency(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    return adj


def _colors(n, adj):
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


def _ball_masks(n, adj, r):
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


# ----------------------------------------------------------------------------
# Base construction: incidence graph of the generalized quadrangle W(q), diam 4.
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
# Diameter-preserving growth. Adding a vertex whose neighbours cover every
# vertex within D-1 of the graph keeps diameter <= D. Adding edges never
# increases distances, so saturation is also safe.
# ----------------------------------------------------------------------------

def _greedy_cover(cands, ball, full, d, rng):
    pool = list(cands)
    rng.shuffle(pool)
    covered = 0
    chosen = []
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
        pool.remove(best_s)
    return chosen if covered == full else None


def _grow(n, edges, d, D, deadline, rng):
    edges = list(edges)
    while time.monotonic() < deadline:
        adj = _adjacency(n, edges)
        deg = [len(a) for a in adj]
        color = _colors(n, adj)
        ball = _ball_masks(n, adj, D - 1)
        full = (1 << n) - 1
        sides = [0, 1]
        rng.shuffle(sides)
        grown = False
        for c in sides:
            cands = [s for s in range(n) if color[s] == c and deg[s] < d]
            if not cands:
                continue
            chosen = _greedy_cover(cands, ball, full, d, rng)
            if chosen:
                v = n
                n += 1
                edges.extend((s, v) for s in chosen)
                grown = True
                break
        if not grown:
            break
    return n, edges


def _saturate(n, edges, d, rng):
    edges = list(edges)
    adj = _adjacency(n, edges)
    deg = [len(a) for a in adj]
    color = _colors(n, adj)
    existing = {(min(u, v), max(u, v)) for u, v in edges}
    L = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    R = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in L for b in R if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return edges


# ----------------------------------------------------------------------------
# New strategy for D >= 4: bi-Cayley graphs over small groups.
# Vertices A_g = g and B_h = N + h. Connection set S (|S| = d) in group G gives
# A_g ~ B_{g s} for s in S. Left translation is an automorphism, so diameter
# <= D is equivalent to: from A_0 every vertex is within D, and from B_0 every
# B vertex is within D. The search anneals S to minimise the number of
# violated pairs, over a range of group orders chosen to beat the current best.
# ----------------------------------------------------------------------------

def _reached(adj, n, src, D):
    seen = bytearray(n)
    seen[src] = 1
    frontier = [src]
    for _ in range(D):
        nxt = []
        for u in frontier:
            for v in adj[u]:
                if not seen[v]:
                    seen[v] = 1
                    nxt.append(v)
        if not nxt:
            break
        frontier = nxt
    return seen


def _bc_cost(N, S, T, invs, D):
    invS = [invs[s] for s in S]
    adj = [[N + T[g][s] for s in S] for g in range(N)]
    adj += [[T[h][t] for t in invS] for h in range(N)]
    sa = _reached(adj, 2 * N, 0, D)
    sb = _reached(adj, 2 * N, N, D)
    return (2 * N - sum(sa)) + (N - sum(sb[N:]))


def _anneal(N, T, invs, d, D, rng, deadline, iters):
    S = rng.sample(range(N), d)
    cost = _bc_cost(N, S, T, invs, D)
    for it in range(iters):
        if cost == 0:
            break
        if (it & 31) == 0 and time.monotonic() > deadline:
            break
        temp = 1.5 * (0.05 / 1.5) ** (it / iters)
        i = rng.randrange(d)
        c = rng.randrange(N)
        if c in S:
            continue
        old = S[i]
        S[i] = c
        c2 = _bc_cost(N, S, T, invs, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost = c2
        else:
            S[i] = old
    return S if cost == 0 else None


def _group(spec):
    if spec[0] == "cyc":
        order, mul, inv = lib.cyclic_group(spec[1])
    else:
        _, m, k, r = spec
        order, mul, inv = lib.semidirect_group(m, k, r)
    T = [[mul(a, b) for b in range(order)] for a in range(order)]
    invs = [inv(a) for a in range(order)]
    return order, T, invs


def _specs(N, rng):
    out = [("cyc", N)]
    for k in range(2, 13):
        if N % k:
            continue
        m = N // k
        if m < 3:
            continue
        rs = [r for r in range(2, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        rng.shuffle(rs)
        for r in rs[:2]:
            out.append(("sd", m, k, r))
    return out


def _bicayley_search(d, D, rng, deadline, consider, get_best):
    bound = lib._moore_bound(d, D) // 2
    while time.monotonic() < deadline:
        best_n = get_best()
        lo = max(best_n // 2 + 1, d + 1)
        hi = min(bound, lo + 8)
        if lo > hi:
            break
        N = rng.randint(lo, hi)
        spec = rng.choice(_specs(N, rng))
        order, T, invs = _group(spec)
        S = _anneal(order, T, invs, d, D, rng, deadline, 700)
        if S is None:
            continue
        edges = [(g, order + T[g][s]) for g in range(order) for s in S]
        consider(2 * order, edges)


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is optimal for D = 2.
    best = lib.haar_graph(d, range(d))
    if D == 2 or best[0] >= lib._moore_bound(d, D):
        return best

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    def get_best():
        return best[0]

    if D == 3:
        qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)][:2]
        for q in qs:
            n, e = lib.projective_plane_incidence(q)
            consider(n, e)
            n2, e2 = _grow(n, e, d, D, start + 0.5 * time_limit, rng)
            consider(n2, _saturate(n2, e2, d, rng))
        if lib.is_prime_power(d - 2) and d - 2 >= 3:
            n, e = lib.araujo_lopez_graph(d - 2)
            consider(n, e)
    else:
        # Generalized quadrangle bases with cover growth (short phase).
        gq_deadline = start + 0.3 * time_limit
        qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)][:2]
        for q in qs:
            if time.monotonic() > gq_deadline:
                break
            n, e = _gq_w(q)
            consider(n, e)
            for _ in range(3):
                n2, e2 = _grow(n, e, d, D, gq_deadline, rng)
                consider(n2, _saturate(n2, e2, d, rng))

        # Main phase: bi-Cayley annealing over group orders above the best.
        _bicayley_search(d, D, rng, deadline, consider, get_best)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
