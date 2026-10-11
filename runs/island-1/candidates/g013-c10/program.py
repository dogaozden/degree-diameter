import itertools
import math
import random
import time

import numpy as np

import lib

_BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Safe baseline families (algebraic bases and spare-degree extension).
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
# Group sampling.
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


# ----------------------------------------------------------------------------
# NEW ENGINE: tabu search over single-block bi-Cayley graphs.
#
# Left vertices g in G (ids 0..G-1), right vertices h in G (ids G..2G-1), with
# g ~ g*s for each s in S, where S is a set of d distinct group elements.
# Left multiplication is a side-preserving automorphism, so the diameter is at
# most D iff BFS from left identity and from right identity reach everything
# within D steps. The graph is simple, bipartite and d-regular by construction.
# Moves replace one connection element; a tabu list forbids undoing recent
# moves, with the usual aspiration rule.
# ----------------------------------------------------------------------------

def _tabu_bicayley(d, D, G, mul, rng, deadline, K=20):
    if d > G or G < 2:
        return None
    perm = {}

    def get(s):
        if s not in perm:
            p = np.fromiter((mul(g, s) for g in range(G)), dtype=np.int64, count=G)
            inv = np.empty(G, dtype=np.int64)
            inv[p] = np.arange(G, dtype=np.int64)
            perm[s] = (p, inv)
        return perm[s]

    def build(S):
        A = np.empty((2 * G, d), dtype=np.int64)
        for l, s in enumerate(S):
            p, inv = get(s)
            A[:G, l] = G + p
            A[G:, l] = inv
        return A

    N = 2 * G

    def cost(A):
        total = 0
        for src in (0, G):
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

    S = rng.sample(range(G), d)
    cur = cost(build(S))
    best = cur
    best_S = list(S)
    tabu = {}
    it = 0
    while best > 0 and time.monotonic() < deadline:
        it += 1
        move = None
        for _ in range(K):
            l = rng.randrange(d)
            x = rng.randrange(G)
            if x in S:
                continue
            old = S[l]
            S[l] = x
            c = cost(build(S))
            S[l] = old
            if tabu.get((l, x), -1) > it and c >= best:
                continue
            if move is None or c < move[0]:
                move = (c, l, x)
        if move is None:
            continue
        c, l, x = move
        tabu[(l, S[l])] = it + 5 + rng.randrange(6)
        S[l] = x
        cur = c
        if cur < best:
            best = cur
            best_S = list(S)

    if best != 0:
        return None
    A = build(best_S)
    edges = [(a, int(b)) for a in range(G) for b in A[a].tolist()]
    return 2 * G, edges


# ----------------------------------------------------------------------------
# Parent engine (kept): annealed multi-block bi-Cayley lifts.
# ----------------------------------------------------------------------------

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


def _cost_multi(k, G, D, A):
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
        return _cost_multi(k, G, D, A), A

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

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
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

    # Main engine: alternate the new tabu bi-Cayley search (D >= 4) with the
    # parent's annealed lifts.
    rng = random.Random(seed)
    while time.monotonic() < deadline and best_n < moore:
        now = time.monotonic()
        use_tabu = D >= 4 and rng.random() < 0.6
        if use_tabu:
            lo = max(d + 1, best_n // 2 + 1)
            if 2 * lo <= moore:
                hi = int(lo * 1.25) + 2
                g = _sample_group(lo, hi, rng)
                if g is not None:
                    G, mul = g
                    slice_end = min(deadline, now + 4.0)
                    res = _tabu_bicayley(d, D, G, mul, rng, slice_end)
                    if res is not None:
                        consider(res[0], res[1])
                continue

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
