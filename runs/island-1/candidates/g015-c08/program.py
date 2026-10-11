import itertools
import math
import random
import time

import numpy as np

import lib

_BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Safe baseline families (unchanged from the parent for D <= 4).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


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


def _largest_pp_le(x):
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def _araujo_candidate(d):
    q = _largest_pp_le(d - 2)
    if q is None or q < 3:
        return None
    try:
        return lib.araujo_lopez_graph(q)
    except Exception:
        return None


def _fill_slack(n, edges, d, seed):
    adjs = [set() for _ in range(n)]
    for u, v in edges:
        adjs[u].add(v)
        adjs[v].add(u)
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for w in adjs[u]:
                if color[w] == -1:
                    color[w] = 1 - color[u]
                    stack.append(w)
    deg = [len(a) for a in adjs]
    rng = random.Random(seed)
    out = list(edges)
    for _ in range(4):
        A = [v for v in range(n) if color[v] == 0 and deg[v] < d]
        B = [v for v in range(n) if color[v] == 1 and deg[v] < d]
        rng.shuffle(A)
        rng.shuffle(B)
        added = False
        for a in A:
            for b in B:
                if deg[a] >= d:
                    break
                if deg[b] < d and b not in adjs[a]:
                    adjs[a].add(b)
                    adjs[b].add(a)
                    deg[a] += 1
                    deg[b] += 1
                    out.append((a, b))
                    added = True
        if not added:
            break
    return n, out


def _greedy_cover(cands, reach, full, d, rng):
    """Pick up to d candidates whose radius-(D-1) balls cover full; return list or None."""
    pool = list(cands)
    rng.shuffle(pool)
    covered = 0
    chosen = []
    while len(chosen) < d and covered != full:
        best = None
        best_gain = 0
        for c in pool:
            g = (reach[c] & ~covered).bit_count()
            if g > best_gain:
                best, best_gain = c, g
        if best is None:
            break
        chosen.append(best)
        covered |= reach[best]
        pool = [c for c in pool if c != best]
    if covered == full:
        return chosen
    return None


def _extend(n, edges, d, D, seed, deadline):
    """Attach new vertices to spare-degree vertices while keeping diameter <= D and bipartiteness."""
    if D < 2 or n == 0:
        return n, list(edges)
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    if any(len(a) > d for a in adj):
        return n, list(edges)
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for w in adj[u]:
                if color[w] == -1:
                    color[w] = 1 - color[u]
                    stack.append(w)
                elif color[w] == color[u]:
                    return n, list(edges)
    rng = random.Random(seed)
    out = list(edges)
    R = D - 1
    fails = 0
    while fails < 4 and time.monotonic() < deadline:
        N = len(adj)
        full = (1 << N) - 1
        reach = [1 << v for v in range(N)]
        for _ in range(R):
            nxt = []
            for v in range(N):
                r = reach[v]
                for u in adj[v]:
                    r |= reach[u]
                nxt.append(r)
            reach = nxt
        added = False
        sides = [0, 1]
        rng.shuffle(sides)
        for opp in sides:
            cands = [c for c in range(N) if color[c] == opp and len(adj[c]) < d]
            if not cands:
                continue
            chosen = _greedy_cover(cands, reach, full, d, rng)
            if chosen:
                x = N
                adj.append(set(chosen))
                color.append(1 - opp)
                for c in chosen:
                    adj[c].add(x)
                    out.append((c, x))
                added = True
                break
        if added:
            fails = 0
        else:
            fails += 1
    return len(adj), out


# ----------------------------------------------------------------------------
# NEW ENGINE: incrementally grown random-like bipartite regular graphs.
#
# Each graph is d layers of perfect matchings between left 0..m-1 and right
# 0..m-1 (left a joins right P[l][a] in every layer l). Distinct images per
# left vertex rule out parallel edges, so the graph is d-regular and bipartite.
#
# Growth: add one left and one right vertex at a time by splicing them into
# each layer (this keeps regularity with no duplicate edges). After each growth
# batch, edge-switch annealing (swap two targets inside one layer) drives the
# number of pairs at distance > D to zero. Batch size adapts: it doubles on
# success and halves on failure.
#
# Distances are computed with bit-parallel reachability over numpy uint64 words.
# ----------------------------------------------------------------------------

def _bad_pairs(P, invP, m, d, D):
    """Unordered pairs at distance > D, from bit-parallel ball expansion."""
    N = 2 * m
    W = (N + 63) // 64
    nbr = np.empty((N, d), dtype=np.int64)
    nbr[:m] = P.T + m
    nbr[m:] = invP.T
    idx = np.arange(N, dtype=np.int64)
    reach = np.zeros((N, W), dtype=np.uint64)
    reach[idx, idx >> 6] = np.left_shift(np.uint64(1), (idx & 63).astype(np.uint64))
    for _ in range(D):
        new = reach.copy()
        for c in range(d):
            new |= reach[nbr[:, c]]
        reach = new
    total = int(np.unpackbits(reach.view(np.uint8)).sum())
    return (N * N - total) // 2


def _grow_one(P, invP, m, d, rng):
    """Add one left vertex m and one right vertex m by splicing into every layer. Returns (P2, invP2) or None."""
    if m < d:
        return None
    for _ in range(20):
        a0s = rng.sample(range(m), d)
        b0s = [int(P[l, a0s[l]]) for l in range(d)]
        if len(set(b0s)) < d:
            continue
        P2 = np.empty((d, m + 1), dtype=np.int64)
        I2 = np.empty((d, m + 1), dtype=np.int64)
        P2[:, :m] = P
        I2[:, :m] = invP
        for l in range(d):
            a0, b0 = a0s[l], b0s[l]
            P2[l, a0] = m          # a0 -> new right vertex m
            P2[l, m] = b0          # new left vertex m -> b0
            I2[l, m] = a0
            I2[l, b0] = m
        return P2, I2
    return None


def _anneal_bip(P, invP, m, d, D, rng, iters, deadline):
    """Edge-switch annealing inside single layers. Returns (best_cost, bestP, bestInvP)."""
    cur = _bad_pairs(P, invP, m, d, D)
    best = cur
    bestP, bestI = P.copy(), invP.copy()
    for it in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        T = 0.6 * (1.0 - it / iters) + 0.05
        l = rng.randrange(d)
        a1, a2 = rng.sample(range(m), 2)
        b1 = int(P[l, a1])
        b2 = int(P[l, a2])
        if b1 == b2:
            continue
        if (P[:, a1] == b2).any() or (P[:, a2] == b1).any():
            continue
        P[l, a1] = b2
        P[l, a2] = b1
        invP[l, b2] = a1
        invP[l, b1] = a2
        c = _bad_pairs(P, invP, m, d, D)
        if c <= cur or rng.random() < math.exp(-(c - cur) / T):
            cur = c
            if cur < best:
                best = cur
                bestP, bestI = P.copy(), invP.copy()
        else:
            P[l, a1] = b1
            P[l, a2] = b2
            invP[l, b1] = a1
            invP[l, b2] = a2
    return best, bestP, bestI


def _grow_engine(d, D, seed, moore, deadline):
    """Grow a valid d-regular bipartite graph as far as time allows. Returns (n, edges)."""
    if d < 2:
        return None
    rng = random.Random(seed * 1009 + 17)
    m = d
    P = np.array([[(a + l) % m for a in range(m)] for l in range(d)], dtype=np.int64)
    I = np.array([[(b - l) % m for b in range(m)] for l in range(d)], dtype=np.int64)
    step = 1
    max_m = moore // 2
    while time.monotonic() < deadline:
        if m + 1 > max_m:
            break
        s = min(step, max_m - m)
        Pc, Ic, mc = P, I, m
        ok = True
        for _ in range(s):
            g = _grow_one(Pc, Ic, mc, d, rng)
            if g is None:
                ok = False
                break
            Pc, Ic = g
            mc += 1
        if ok:
            cost, Pb, Ib = _anneal_bip(Pc, Ic, mc, d, D, rng, 500, deadline)
            if cost == 0:
                P, I, m = Pb, Ib, mc
                step = min(step * 2, max(1, m // 8))
                continue
        step //= 2
        if step == 0:
            break
    edges = [(a, m + int(P[l, a])) for a in range(m) for l in range(d)]
    return 2 * m, edges


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over semidirect products (parent engine, kept as a
# secondary search for whatever time remains).
# ----------------------------------------------------------------------------

def _sample_group(lo, hi, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 with order in [lo, hi], or None."""
    for _ in range(40):
        G = rng.randrange(lo, hi + 1)
        divs = [k2 for k2 in range(1, 17) if G % k2 == 0 and G // k2 >= 2]
        if not divs:
            continue
        k2 = rng.choice(divs)
        m = G // k2
        cands = [1]
        if k2 > 1 and m > 2:
            cands += [r for r in rng.sample(range(2, m), min(m - 2, 120))
                      if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
        r = rng.choice(cands)
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def _rperm_cache(mul, G):
    cache = {}

    def get(s):
        if s not in cache:
            p = np.fromiter((mul(g, s) for g in range(G)), dtype=np.int64, count=G)
            inv = np.empty(G, dtype=np.int64)
            inv[p] = np.arange(G, dtype=np.int64)
            cache[s] = (p, inv)
        return cache[s]

    return get


def _build_adj(k, G, P, S, get):
    d = P.shape[0]
    N = 2 * k * G
    A = np.empty((N, d), dtype=np.int64)
    for l in range(d):
        for i in range(k):
            j = int(P[l, i])
            s = int(S[l, i])
            p, inv = get(s)
            A[i * G:(i + 1) * G, l] = (k + j) * G + p
            A[(k + j) * G:(k + j + 1) * G, l] = i * G + inv
    return A


def _cost(k, G, D, A):
    N = A.shape[0]
    total = 0
    sources = list(range(0, k * G, G)) + list(range(k * G, 2 * k * G, G))
    for src in sources:
        seen = np.zeros(N, dtype=bool)
        seen[src] = True
        front = np.array([src], dtype=np.int64)
        for _ in range(D):
            mark = np.zeros(N, dtype=bool)
            mark[A[front].ravel()] = True
            mark &= ~seen
            front = np.flatnonzero(mark)
            if front.size == 0:
                break
            seen |= mark
        total += N - int(np.count_nonzero(seen))
    return total


def _anneal(d, D, k, G, mul, rng, iters, deadline):
    get = _rperm_cache(mul, G)
    P = np.array([rng.sample(range(k), k) for _ in range(d)], dtype=np.int64)
    S = np.array([[rng.randrange(G) for _ in range(k)] for _ in range(d)], dtype=np.int64)
    ar = np.arange(k, dtype=np.int64)

    def evaluate(P, S):
        keys = (ar[None, :] * k + P) * G + S
        if np.unique(keys).size < keys.size:
            return _BIG, None
        A = _build_adj(k, G, P, S, get)
        return _cost(k, G, D, A), A

    cost, _ = evaluate(P, S)
    best = cost
    best_P = P.copy()
    best_S = S.copy()
    T0 = 2.0

    for t in range(iters):
        if best == 0 or time.monotonic() > deadline:
            break
        T = T0 * (1.0 - t / iters) + 0.05
        if k == 1 or rng.random() < 0.5:
            l = rng.randrange(d)
            i = rng.randrange(k)
            old = int(S[l, i])
            S[l, i] = rng.randrange(G)
            c, _ = evaluate(P, S)
            if c <= cost or rng.random() < math.exp(-(c - cost) / T):
                cost = c
            else:
                S[l, i] = old
        else:
            l = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            P[l, a], P[l, b] = P[l, b], P[l, a]
            c, _ = evaluate(P, S)
            if c <= cost or rng.random() < math.exp(-(c - cost) / T):
                cost = c
            else:
                P[l, a], P[l, b] = P[l, b], P[l, a]
        if cost < best:
            best = cost
            best_P = P.copy()
            best_S = S.copy()

    if best != 0:
        return None
    _, A = evaluate(best_P, best_S)
    if A is None:
        return None
    N = A.shape[0]
    edges = []
    for a in range(k * G):
        for b in A[a].tolist():
            edges.append((a, int(b)))
    return N, edges


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, min(0.85 * time_limit, time_limit - 4.0))

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

    if D == 2:
        return best

    moore = lib._moore_bound(d, D)

    # Algebraic base constructions.
    bases = []
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            bases.append(pg)
        al = _araujo_candidate(d)
        if al is not None:
            n_al, e_al = al
            bases.append(_fill_slack(n_al, e_al, d, seed))
    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            bases.append(gq)

    for b in bases:
        consider(b[0], b[1])

    # Extension of algebraic bases by spare-degree vertices.
    ext_frac = 0.3 if D <= 4 else 0.1
    ext_end = start + ext_frac * (deadline - start)
    for idx, (n0, e0) in enumerate(bases):
        if best_n >= moore:
            break
        now = time.monotonic()
        if now >= ext_end:
            break
        slice_end = now + (ext_end - now) / (len(bases) - idx)
        n1, e1 = _extend(n0, e0, d, D, seed + idx, slice_end)
        consider(n1, e1)

    # NEW main engine: incrementally grown, edge-switch-annealed random-like
    # d-regular bipartite graphs. Gets the larger share of the remaining time.
    if D >= 3 and best_n < moore and time.monotonic() < deadline:
        now = time.monotonic()
        eng_end = now + 0.6 * (deadline - now)
        try:
            res = _grow_engine(d, D, seed, moore, eng_end)
        except Exception:
            res = None
        if res is not None:
            consider(res[0], res[1])

    # Secondary engine: annealed bi-Cayley lifts with the remaining time.
    rng = random.Random(seed)
    while time.monotonic() < deadline and best_n < moore:
        k = rng.choice([1, 2, 2, 3, 3, 4, 6])
        lo = max(2, best_n // (2 * k) + 1)
        if 2 * k * lo > moore:
            k = 1
            lo = max(2, best_n // 2 + 1)
            if 2 * lo > moore:
                break
        hi = int(lo * 1.35) + 2
        g = _sample_group(lo, hi, rng)
        if g is None:
            continue
        G, mul = g
        res = _anneal(d, D, k, G, mul, rng, 4000, deadline)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
