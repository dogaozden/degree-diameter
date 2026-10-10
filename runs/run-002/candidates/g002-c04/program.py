import itertools
import math
import random
import time

import numpy as np

import lib

N_CAP = 6000                  # hard cap on vertex count
ITERS = 6000                  # annealing iterations per attempt
S_LIST = (1, 2, 3, 4, 5, 6)   # number of base vertices per side
GQ_Q_MAX = 9                  # largest q for which W(q) is built (pair loop is O(P^2))
RETRIES = 3                   # annealing attempts per candidate lift size
GROUP_POOL = 6                # semidirect products tried per group order (cyclic always added)
TIME_FRAC = 0.8               # fraction of time_limit used for search
POST_FRAC = 0.85              # fraction of time_limit after which nothing new starts
POST_EXTEND_SLICE = 1.5       # seconds given to greedy growth of the best lift

# Bold branch (used for D >= 5): random regular bipartite graphs repaired by
# edge-swap simulated annealing on the number of pairs at distance > D.
LEGACY_SHARE = 0.35           # share of time_limit kept for the structured fallback
SA_FRAC = 0.85                # fraction of time_limit after which SA stops
SA_N_CAP = 1400               # largest vertex count the SA branch will try
SA_T0 = 6.0                   # initial annealing temperature (ordered-pair units)
SA_T1 = 0.3                   # final annealing temperature


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
    """Greedily add new vertices, each attached to a set cover of the current graph.

    A new vertex x with neighbour set N is within distance D of every old vertex iff the
    radius-(D-1) balls of N cover all vertices. Old pairs only get closer, so the diameter
    bound is preserved.
    """
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
    """Add two adjacent new vertices x (side c) and y (side 1-c) at once.

    x gets neighbours N (old vertices on side 1-c) whose radius-(D-1) balls cover everything.
    y gets neighbours M (old vertices on side c) chosen so that
        balls_{D-1}(M) covers everything not already within D-2 of N,
    which is exactly the condition for y to reach each old vertex, either directly
    through M or through x and N (length 2 + dist(N, v)).
    Old-to-old distances only shrink, so the diameter bound is preserved.
    """
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
    """Add edges between opposite colour classes using spare degree.

    Extra edges only shorten distances and keep the graph bipartite, so the diameter
    bound and bipartiteness are preserved.
    """
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


def _finish(cands, d, D):
    """Return the largest candidate that passes lib.is_valid, else K_{d,d}."""
    for n, e in sorted(cands, key=lambda c: -c[0]):
        if lib.is_valid(n, e, d, D):
            return n, e
    return lib.haar_graph(d, range(d))


# ---------------------------------------------------------------- D = 3 : projective plane

def _pg_base(d):
    """Incidence graph of PG(2,q), q the largest prime power <= d-1."""
    q = d - 1
    while q >= 2 and not lib.is_prime_power(q):
        q -= 1
    if q < 2:
        return None
    return lib.projective_plane_incidence(q)


# ---------------------------------------------------------------- D >= 4 : generalized quadrangle

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


# ---------------------------------------------------------------- groups for lifts

def _group_pool(M, rng):
    """Group choices of order M: a few shuffled semidirect products Z_m x| Z_k, then cyclic (None)."""
    opts = []
    for m in range(2, M):
        if M % m:
            continue
        k = M // m
        if k < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                opts.append((m, k, r))
    rng.shuffle(opts)
    opts = opts[:GROUP_POOL]
    opts.append(None)
    return opts


def _group_tables(M, opt):
    """Multiplication table mul[x, y] = x*y and inverse table inv[x] on elements 0..M-1 (identity 0).

    opt None gives Z_M. Otherwise opt = (m, k, r) gives Z_m x| Z_k with element a*k+b,
    (a, b)(c, d) = (a + r^b c, b + d); needs r^k = 1 mod m and gcd(r, m) = 1.
    """
    x = np.arange(M, dtype=np.int64)
    if opt is None:
        return (x[:, None] + x[None, :]) % M, (-x) % M
    m, k, r = opt
    a, b = x // k, x % k
    pw = np.array([pow(r, t, m) for t in range(k)], dtype=np.int64)
    mul = ((a[:, None] + pw[b][:, None] * a[None, :]) % m) * k + (b[:, None] + b[None, :]) % k
    nb = (-b) % k
    inv = ((-pw[nb] * a) % m) * k + nb
    return mul, inv


# ---------------------------------------------------------------- lifts (annealing)

def _neighbors(P, Pinv, V, s, M, mul, inv):
    """Neighbour table (n x d) of the G-lift of a d-regular bipartite base on s+s vertices.

    Dart (k, i -> j) with voltage g joins A(i, x) to B(j, x*g) for all x in G.
    """
    d = P.shape[0]
    nbr = np.empty((2 * s * M, d), dtype=np.int64)
    for k in range(d):
        for i in range(s):
            j = int(P[k, i])
            g = int(V[k, i])
            nbr[i * M:(i + 1) * M, k] = s * M + j * M + mul[:, g]
        for j in range(s):
            i = int(Pinv[k, j])
            g = int(V[k, i])
            nbr[(s + j) * M:(s + j + 1) * M, k] = i * M + mul[:, inv[g]]
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


def _anneal(s, M, d, D, rng, deadline, mul, inv):
    """Simulated annealing over permutations and voltages. Returns (P, V) with zero cost, or None."""
    P = np.array([rng.sample(range(s), s) for _ in range(d)], dtype=np.int64)
    Pinv = np.zeros_like(P)
    for k in range(d):
        for i in range(s):
            Pinv[k, P[k, i]] = i
    V = np.array([[rng.randrange(M) for _ in range(s)] for _ in range(d)], dtype=np.int64)
    # Left multiplication is an automorphism, so one source per A-side class suffices.
    sources = [i * M for i in range(2 * s)]
    nbr = _neighbors(P, Pinv, V, s, M, mul, inv)
    cur = _cost(nbr, sources, D)
    for it in range(ITERS):
        if cur == 0 or time.monotonic() > deadline:
            break
        temp = 2.0 * (1.0 - it / ITERS) + 0.05
        if s == 1 or rng.random() < 0.7:
            k, i = rng.randrange(d), rng.randrange(s)
            old = int(V[k, i])
            new_v = rng.randrange(M)
            if new_v == old:
                continue
            V[k, i] = new_v
            cand = _neighbors(P, Pinv, V, s, M, mul, inv)
            c = _cost(cand, sources, D)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur, nbr = c, cand
            else:
                V[k, i] = old
        else:
            k = rng.randrange(d)
            a, b = rng.sample(range(s), 2)
            _swap(P, Pinv, k, a, b)
            cand = _neighbors(P, Pinv, V, s, M, mul, inv)
            c = _cost(cand, sources, D)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur, nbr = c, cand
            else:
                _swap(P, Pinv, k, a, b)
    if cur == 0:
        return P.copy(), V.copy()
    return None


def _graph(s, M, P, V, d, mul, inv):
    """Materialise the lift as (n, edges), deduplicated."""
    Pinv = np.zeros_like(P)
    for k in range(d):
        for i in range(s):
            Pinv[k, P[k, i]] = i
    nbr = _neighbors(P, Pinv, V, s, M, mul, inv)
    edges = set()
    for x in range(s * M):
        for y in nbr[x].tolist():
            edges.add((x, y))
    return 2 * s * M, sorted(edges)


def _try_size(s, M, d, D, rng, deadline):
    """Attempt to anneal a valid lift over a group of order M, varying the group across restarts.

    Returns (P, V, mul, inv) or None.
    """
    pool = _group_pool(M, rng)
    for t in range(RETRIES):
        if time.monotonic() > deadline:
            break
        opt = pool[t % len(pool)]
        mul, inv = _group_tables(M, opt)
        st = _anneal(s, M, d, D, rng, deadline, mul, inv)
        if st is not None:
            return st[0], st[1], mul, inv
    return None


def _search(s, d, D, rng, deadline, cap):
    """For fixed s, find the largest group order M (doubling then bisection) whose lift passes annealing."""
    best = None
    lo, hi = 0, None
    M = 1
    while time.monotonic() < deadline:
        if 2 * s * M > cap:
            hi = M
        else:
            st = _try_size(s, M, d, D, rng, deadline)
            if st is not None:
                lo = M
                best = (M, st[0], st[1], st[2], st[3])
            else:
                hi = M
        if hi is None:
            M = 2 * lo
        else:
            if hi - lo <= 1:
                break
            M = (lo + hi) // 2
    return best


# ---------------------------------------------------------------- bold branch: regular SA

def _reach_cost(nbrA, nbrB, m, d, D, W):
    """Number of ordered vertex pairs at distance > D in the bipartite graph (A = 0..m-1, B = m..2m-1).

    Reachability sets are bit-packed rows of W uint64 words and are expanded D times.
    """
    n = 2 * m
    nbr = np.concatenate([nbrA + m, nbrB], axis=0)
    idx = np.arange(n, dtype=np.int64)
    R = np.zeros((n, W), dtype=np.uint64)
    R[idx, idx >> 6] = np.left_shift(np.uint64(1), (idx & 63).astype(np.uint64))
    for _ in range(D):
        M = R.copy()
        for k in range(d):
            M |= R[nbr[:, k]]
        if np.array_equal(M, R):
            break
        R = M
    reached = int(np.unpackbits(R.view(np.uint8)).sum())
    return n * n - reached


def _random_regular(m, d, np_rng):
    """Random d-regular bipartite adjacency on m+m vertices as nbrA (A -> B indices) and nbrB (B -> A indices)."""
    if m < d or d < 2:
        return None
    nbrA = np.empty((m, d), dtype=np.int64)
    for k in range(d):
        for _ in range(2000):
            p = np_rng.permutation(m)
            if not np.any(nbrA[:, :k] == p[:, None]):
                nbrA[:, k] = p
                break
        else:
            return None
    nbrB = np.empty((m, d), dtype=np.int64)
    for k in range(d):
        nbrB[nbrA[:, k], k] = np.arange(m)
    return nbrA, nbrB


def _sa_regular(m, d, D, rng, np_rng, deadline):
    """Edge-swap annealing on a random d-regular bipartite graph with m+m vertices.

    Swaps (a1,b1),(a2,b2) -> (a1,b2),(a2,b1) keep regularity, bipartiteness and simplicity.
    Returns (nbrA, nbrB) with zero cost, or None.
    """
    init = _random_regular(m, d, np_rng)
    if init is None:
        return None
    nbrA, nbrB = init
    W = (2 * m + 63) // 64
    cur = _reach_cost(nbrA, nbrB, m, d, D, W)
    start = time.monotonic()
    span = max(1e-3, deadline - start)
    while cur > 0:
        now = time.monotonic()
        if now >= deadline:
            return None
        frac = min(1.0, (now - start) / span)
        temp = SA_T0 * (1.0 - frac) + SA_T1 * frac
        a1, s1 = rng.randrange(m), rng.randrange(d)
        a2, s2 = rng.randrange(m), rng.randrange(d)
        b1 = int(nbrA[a1, s1])
        b2 = int(nbrA[a2, s2])
        if a1 == a2 or b1 == b2:
            continue
        if np.any(nbrA[a1] == b2) or np.any(nbrA[a2] == b1):
            continue
        nbrA[a1, s1] = b2
        nbrA[a2, s2] = b1
        t1 = int(np.nonzero(nbrB[b1] == a1)[0][0])
        nbrB[b1, t1] = a2
        t2 = int(np.nonzero(nbrB[b2] == a2)[0][0])
        nbrB[b2, t2] = a1
        c = _reach_cost(nbrA, nbrB, m, d, D, W)
        if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
            cur = c
        else:
            nbrA[a1, s1] = b1
            nbrA[a2, s2] = b2
            nbrB[b1, t1] = a1
            nbrB[b2, t2] = a2
    return nbrA, nbrB


def _sa_graph(m, nbrA):
    """Materialise the bipartite graph: A vertices 0..m-1, B vertices m..2m-1."""
    edges = [(a, m + int(b)) for a in range(m) for b in nbrA[a].tolist()]
    return 2 * m, edges


def _sa_phase(base_n, d, D, seed, deadline):
    """Bisection on the side size m, each probe a fresh SA run. Returns (m, nbrA) or None."""
    rng = random.Random(seed + 101)
    np_rng = np.random.default_rng(seed + 101)
    lo_m = max(d, base_n // 2)
    hi_m = min(SA_N_CAP // 2, lib._moore_bound(d, D) // 2) + 1   # exclusive
    best = None
    m_try = lo_m + max(1, lo_m // 20)
    while time.monotonic() < deadline and hi_m - lo_m > 1:
        m_try = min(max(m_try, lo_m + 1), hi_m - 1)
        now = time.monotonic()
        remaining = deadline - now
        slice_end = now + max(0.5, 0.5 * remaining)
        slice_end = min(slice_end, deadline)
        res = _sa_regular(m_try, d, D, rng, np_rng, slice_end)
        if res is not None:
            lo_m = m_try
            best = (m_try, res[0])
        else:
            hi_m = m_try
        m_try = (lo_m + hi_m) // 2
    return best


# ---------------------------------------------------------------- structured builder (previous parent)

def _legacy_build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, TIME_FRAC * time_limit - 1.0)
    post_end = start + max(0.5, POST_FRAC * time_limit - 1.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if D == 2:
        return lib.haar_graph(d, range(d))  # K_{d,d} is extremal for D = 2

    cands = [lib.haar_graph(d, range(d))]   # K_{d,d}: diameter 2, always valid

    # D >= 3: projective plane (diameter 3), extended into spare degree.
    if d >= 3:
        base = _pg_base(d)
        if base is not None:
            if lib.is_prime_power(d - 1) and D == 3:   # Moore-extremal, nothing to improve
                return _finish(cands + [base], d, D)
            cands.append(base)
            aug = _augment(base[0], base[1], d, seed)
            for g in (base, aug):
                cands.append(_grow(g[0], g[1], d, D, rng, min(deadline, time.monotonic() + 0.7)))

    # D >= 4: generalized quadrangle W(q) (diameter 4 <= D), extended as well.
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            if D == 4 and d - 1 <= GQ_Q_MAX and lib.is_prime_power(d - 1):
                return _finish(cands + [gq], d, D)  # Moore-extremal for D = 4
            cands.append(gq)
            aug = _augment(gq[0], gq[1], d, seed)
            for g in (gq, aug):
                cands.append(_grow(g[0], g[1], d, D, rng, min(deadline, time.monotonic() + 0.7)))

    cap = min(N_CAP, lib._moore_bound(d, D))

    # Haar graphs with growing modulus (small slice of the remaining time).
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

    # Group-lift annealing, one slice per base size s.
    lift_best = None
    for idx, s in enumerate(S_LIST):
        now = time.monotonic()
        if now >= deadline:
            break
        slice_end = now + (deadline - now) / (len(S_LIST) - idx)
        res = _search(s, d, D, rng, slice_end, cap)
        if res is not None:
            M, P, V, mul, inv = res
            g = _graph(s, M, P, V, d, mul, inv)
            cands.append(g)
            if lift_best is None or g[0] > lift_best[0]:
                lift_best = g

    # Post-process the largest lift: fill spare degree, then grow with single and paired vertices.
    if lift_best is not None and time.monotonic() < post_end:
        aug = _augment(lift_best[0], lift_best[1], d, seed)
        cands.append(aug)
        ext_end = min(post_end, time.monotonic() + POST_EXTEND_SLICE)
        cands.append(_grow(aug[0], aug[1], d, D, rng, ext_end))

    return _finish(cands, d, D)


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]

    # Structured fallback first (always valid), with a reduced budget when the SA branch runs.
    if d < 3 or D < 5:
        return _legacy_build(d, D, seed, time_limit)

    try:
        base_n, base_e = _legacy_build(d, D, seed, LEGACY_SHARE * time_limit)
    except Exception:
        base_n, base_e = lib.haar_graph(d, range(d))

    cands = [(base_n, base_e)]
    sa_end = start + max(0.5, SA_FRAC * time_limit - 1.0)
    try:
        res = _sa_phase(base_n, d, D, seed, sa_end)
        if res is not None:
            m, nbrA = res
            cands.append(_sa_graph(m, nbrA))
    except Exception:
        pass

    return _finish(cands, d, D)
