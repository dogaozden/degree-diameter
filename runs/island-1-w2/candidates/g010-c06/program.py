import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Known bases (diameter 3 and 4). Each returns (n, edges) or None.
# ----------------------------------------------------------------------------

def _araujo_best(d):
    for q in range(min(d - 2, 23), 2, -1):
        if lib.is_prime_power(q):
            try:
                return lib.araujo_lopez_graph(q)
            except ValueError:
                return None
    return None


def _best_pg(d):
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of the generalized quadrangle W(q); diameter 4."""
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
    edges = [(p, P + j) for j, L in enumerate(lines) for p in L]
    return 2 * P, edges


def _best_gq(d):
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _affine_incidence(q):
    """Point-line incidence graph of AG(2, q); diameter 4, degree q+1 on points."""
    F = lib.GF(q)
    n_pts = q * q
    edges = []
    for m in range(q):
        for b in range(q):
            L = n_pts + m * q + b
            for x in range(q):
                edges.append((x * q + F.add(F.mul(m, x), b), L))
    for c in range(q):
        L = n_pts + q * q + c
        for y in range(q):
            edges.append((c * q + y, L))
    return n_pts + q * q + q, edges


def _best_affine(d):
    for q in range(min(d - 1, 23), 1, -1):
        if lib.is_prime_power(q):
            return _affine_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Diameter-preserving growth: twin cloning, cover extension, edge saturation.
# ----------------------------------------------------------------------------

def _clone_grow(n, edges, d, deadline, rng):
    """Add twins of vertices whose whole neighbourhood still has spare degree."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    grew = True
    while grew and time.monotonic() < deadline:
        grew = False
        order = list(range(n))
        rng.shuffle(order)
        for v in order:
            if time.monotonic() >= deadline:
                break
            nb = adj[v]
            if not nb or len(nb) > d or any(deg[u] >= d for u in nb):
                continue
            w = n
            n += 1
            adj.append(list(nb))
            deg.append(len(nb))
            for u in nb:
                adj[u].append(w)
                deg[u] += 1
                edges.append((u, w))
            grew = True
    return n, edges


def _balls_radius(n, adj, r):
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
        opts = [i for i, g in enumerate(gains) if g == best_g]
        i = rng.choice(opts) if randomize else opts[0]
        s = pool.pop(i)
        chosen.append(s)
        covered |= ball[s]
    return chosen if covered == full else None


def _extend_cover(n, edges, d, D, deadline, rng):
    """Add vertices whose neighbourhoods cover everything within distance D-1."""
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
            for attempt in range(100):
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
    """Join deficient opposite-side vertices with spare degree."""
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
    pairs = [(a, b) for a in left for b in right if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return edges


def _grow(n, edges, d, D, deadline, rng):
    cur_n, cur_e = n, list(edges)
    for _ in range(6):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate_edges(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# Bi-Cayley voltage lifts over semidirect products Z_m x| Z_k2.
#
# Vertices: A_i,g = i*G + g and B_j,h = (k+j)*G + h.
# Dart (i, j, s) joins A_i,g to B_j,mul(g,s) for every g.
# Left translation is an automorphism, so the graph is valid iff every
# representative (vertices t*G, t < 2k) reaches all vertices within D.
#
# Cost evaluation is bit-parallel: M[v] is a bitmask over the 2k
# representatives, and one round ORs neighbour masks. The total number of
# unreached (representative, vertex) pairs is the cost, and zero means valid.
# Each layer contributes one dart per i and one per j, so degree is exactly d.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _sample_group(G, rng):
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


def _lift_cost(k, G, D, darts, perms):
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    nbr = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        ba = i * G
        bb = (k + j) * G
        for g in range(G):
            a = ba + g
            b = bb + pm[g]
            nbr[a].append(b)
            nbr[b].append(a)
    M = [0] * N
    for t in range(2 * k):
        M[t * G] |= 1 << t  # representative t sits at vertex t*G
    for _ in range(D):
        new = [0] * N
        for v in range(N):
            x = M[v]
            for u in nbr[v]:
                x |= M[u]
            new[v] = x
        if new == M:
            break
        M = new
    full = 2 * k
    return sum(full - M[v].bit_count() for v in range(N))


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal(D, k, G, mul, d, rng, end):
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [[mul(g, s) for g in range(G)] for _, _, s in darts]
    cost = _lift_cost(k, G, D, darts, perms)
    t0 = time.monotonic()
    span = max(1e-6, end - t0)

    while cost > 0 and time.monotonic() < end:
        frac = min(1.0, (time.monotonic() - t0) / span)
        T = 0.05 ** frac
        u = 1.0 - rng.random()
        thr = cost - T * math.log(u)
        if k == 1 or rng.random() < 0.7:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_perm = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = [mul(g, new_s) for g in range(G)]
            c2 = _lift_cost(k, G, D, darts, perms)
            if c2 <= thr:
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
            if c2 <= thr:
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _edges(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# Haar graph hill-climb (small D only).
# ----------------------------------------------------------------------------

def _search_haar(d, D, m, rng, deadline, iters):
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


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, min(0.9 * time_limit, time_limit - 3.0))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    def consider_clone(n, e, s):
        if time.monotonic() >= deadline:
            return
        n2, e2 = _clone_grow(n, e, d, deadline, random.Random(s))
        if n2 > n:
            consider(n2, e2)

    # Structured bases. Each is valid for its diameter and for every larger D.
    if D >= 3 and best_n < moore:
        ara = _araujo_best(d)
        if ara is not None:
            consider(ara[0], ara[1])
            consider_clone(ara[0], ara[1], seed + 11)
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            consider_clone(pg[0], pg[1], seed + 13)
            n2, e2 = _grow(pg[0], pg[1], d, D, start + 0.15 * time_limit,
                           random.Random(seed + 1))
            consider(n2, e2)
            consider_clone(n2, e2, seed + 14)

    if D >= 4 and best_n < moore and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            consider_clone(gq[0], gq[1], seed + 16)
            n2, e2 = _grow(gq[0], gq[1], d, D, start + 0.25 * time_limit,
                           random.Random(seed + 17))
            consider(n2, e2)
            consider_clone(n2, e2, seed + 18)
        aff = _best_affine(d)
        if aff is not None and best_n < moore:
            consider(aff[0], aff[1])
            consider_clone(aff[0], aff[1], seed + 20)

    # Main phase: bi-Cayley lifts. For larger D the base is not tied to
    # best_n, because the structured bases are weak there. Aim the group order
    # at a fraction of the Moore bound and widen the window after failures.
    if D >= 5:
        ks = [1, 2, 2, 3, 4, 5, 6]
        target_frac = 0.3
    else:
        ks = [1, 1, 2, 3]
        target_frac = 0.0
    haar_m, haar_miss = d + 1, 0
    fails = 0

    while time.monotonic() < deadline and best_n < moore:
        if D <= 4 and haar_miss < 4 and rng.random() < 0.1:
            S = _search_haar(d, D, haar_m, rng, deadline, 120)
            if S is not None:
                n, e = lib.haar_graph(haar_m, S)
                consider(n, e)
                haar_miss = 0
            else:
                haar_miss += 1
            haar_m += 1
            continue

        k = rng.choice(ks)
        target = max(best_n, int(target_frac * moore))
        base = max(2, target // (2 * k))
        spread = min(1.0, 0.05 * (1 + fails))
        hi = max(base // 8 + 1, int(base * spread))
        G = max(2, base + 1 + rng.randrange(0, hi))
        g = _sample_group(G, rng)
        if g is None:
            fails += 1
            continue
        order, mul = g
        run_end = min(deadline, time.monotonic() + (4.0 if D >= 5 else 3.0))
        res = _anneal(D, k, order, mul, d, rng, run_end)
        if res is not None:
            consider(res[0], res[1])
            consider_clone(res[0], res[1], seed + 19 + fails)
            fails = 0
        else:
            fails += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
