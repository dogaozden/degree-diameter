import itertools
import math
import random
import time

import numpy as np

import lib

N_CAP = 6000                 # hard cap on vertex count
ITERS = 6000                 # annealing iterations per attempt
S_LIST = (1, 2, 3, 4, 5, 6)  # base vertices per side
SD_S = (2, 3, 4)             # base sizes that also try non-abelian semidirect lifts
SD_K = (3, 4, 5, 6)          # orders k of the Z_k factor in Z_m x| Z_k
GQ_Q_MAX = 9                 # largest q for which W(q) is built (pair loop is O(P^2))
RETRIES = 2                  # annealing attempts per candidate lift size
TIME_FRAC = 0.8              # fraction of time_limit used for search
POST_FRAC = 0.85             # fraction of time_limit after which nothing new starts


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


def _finish(cands, d, D):
    """Largest candidate that passes lib.is_valid, else K_{d,d}."""
    for n, e in sorted(cands, key=lambda c: -c[0]):
        if lib.is_valid(n, e, d, D):
            return n, e
    return lib.haar_graph(d, range(d))


def _saturate(n, edges, d, rng):
    """Join deficient opposite-colour vertices that are not yet adjacent.

    Adding such edges never increases a distance and keeps the graph bipartite.
    """
    edges = list(edges)
    deg = [0] * n
    existing = set()
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
        existing.add((u, v) if u < v else (v, u))
    color = _two_colour(n, edges)
    left = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    rights = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    rng.shuffle(left)
    rng.shuffle(rights)
    for a in left:
        for b in rights:
            if deg[a] >= d:
                break
            if deg[b] >= d:
                continue
            key = (a, b) if a < b else (b, a)
            if key in existing:
                continue
            edges.append((a, b))
            existing.add(key)
            deg[a] += 1
            deg[b] += 1
    return edges


def _extend(n, edges, d, D, rng, deadline):
    """Greedily add vertices, each joined to a set cover of the current graph.

    A new vertex x with neighbour set N is within distance D of every old vertex iff
    the radius-(D-1) balls of N cover all vertices. Old distances only shrink, so the
    diameter bound is preserved.
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


def _grow(n, edges, d, D, deadline, rng):
    """Alternate saturation and cover extension until no vertex can be added."""
    cur_n, cur_e = n, list(edges)
    for _ in range(8):
        if time.monotonic() >= deadline:
            break
        cur_e = _saturate(cur_n, cur_e, d, rng)
        n2, e2 = _extend(cur_n, cur_e, d, D, rng, deadline)
        if n2 == cur_n:
            break
        cur_n, cur_e = n2, e2
    return cur_n, cur_e


# ---------------------------------------------------------------- D = 3 : projective plane

def _pg_base(d):
    """Incidence graph of PG(2, q), q the largest prime power <= d - 1."""
    q = d - 1
    while q >= 2 and not lib.is_prime_power(q):
        q -= 1
    if q < 2:
        return None
    return lib.projective_plane_incidence(q)


# ---------------------------------------------------------------- D = 4 : generalized quadrangle

def _gq_w(q):
    """Incidence graph of points and lines of W(q). Degree q + 1, diameter 4, order 2(q+1)(q^2+1)."""
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
    """W(q) for the largest prime power q with q <= d - 1 and q <= GQ_Q_MAX."""
    for q in range(min(d - 1, GQ_Q_MAX), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ---------------------------------------------------------------- Haar graphs (hill-climb)

def _search_haar(d, D, m, rng, deadline, iters):
    """Hill-climb a connection set S (|S| = d, containing 0) in Z_m for diameter <= D."""
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


# ---------------------------------------------------------------- groups Z_m x| Z_k

def _make_ctx(m, k, r):
    """Context for the group Z_m x|_r Z_k, element (a, b) coded as a*k + b.

    (a,b)*(c,e) = (a + r^b c, b + e). Returns (k, m, pw, G, INV) with pw[b] = r^b mod m
    and INV[g] the inverse of g.
    """
    G = m * k
    pw = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
    X = np.arange(G, dtype=np.int64)
    a = X // k
    b = X % k
    nb = (-b) % k
    INV = ((-pw[nb] * a) % m) * k + nb
    return (k, m, pw, G, INV)


def _mul(ctx, g, v):
    """Array g * v (right multiplication by the element v)."""
    k, m, pw = ctx[0], ctx[1], ctx[2]
    a, b = g // k, g % k
    c, e = v // k, v % k
    return ((a + pw[b] * c) % m) * k + (b + e) % k


def _family_ctx(fam, k, m, rng):
    """Group context for family fam ('cyc', 'dih', 'sd') with modulus m and order factor k."""
    if fam == "dih":
        r = m - 1
    elif fam == "sd":
        rs = [r for r in range(1, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        r = rng.choice(rs) if rs else 1
    else:
        r = 1
    return _make_ctx(m, k, r)


# ---------------------------------------------------------------- lifts (annealing)

def _neighbors(P, Pinv, V, s, ctx):
    """Neighbour table (n x d) of the group lift of a d-regular bipartite base on s+s vertices."""
    G = ctx[3]
    d = P.shape[0]
    g = np.arange(G, dtype=np.int64)
    nbr = np.empty((2 * s * G, d), dtype=np.int64)
    for kk in range(d):
        for i in range(s):
            j = int(P[kk, i])
            v = int(V[kk, i])
            nbr[i * G:(i + 1) * G, kk] = s * G + j * G + _mul(ctx, g, v)
        for j in range(s):
            i = int(Pinv[kk, j])
            v_inv = int(ctx[4][int(V[kk, i])])
            nbr[(s + j) * G:(s + j + 1) * G, kk] = i * G + _mul(ctx, g, v_inv)
    return nbr


def _cost(nbr, sources, D):
    """Number of (source, vertex) pairs NOT within distance D. Zero iff the lift is valid."""
    n = nbr.shape[0]
    S = len(sources)
    R = np.zeros((S, n), dtype=bool)
    R[np.arange(S), sources] = True
    for _ in range(D):
        M = R.copy()
        for kk in range(nbr.shape[1]):
            M |= R[:, nbr[:, kk]]
        if np.array_equal(M, R):
            break
        R = M
    return int(S * n - np.count_nonzero(R))


def _swap(P, Pinv, row, a, b):
    P[row, a], P[row, b] = P[row, b], P[row, a]
    Pinv[row, P[row, a]] = a
    Pinv[row, P[row, b]] = b


def _anneal(s, ctx, d, D, rng, deadline):
    """Simulated annealing over permutations and voltages. Returns (P, V) with zero cost, or None."""
    G = ctx[3]
    P = np.array([rng.sample(range(s), s) for _ in range(d)], dtype=np.int64)
    Pinv = np.zeros_like(P)
    for kk in range(d):
        for i in range(s):
            Pinv[kk, P[kk, i]] = i
    V = np.array([[rng.randrange(G) for _ in range(s)] for _ in range(d)], dtype=np.int64)
    sources = [i * G for i in range(2 * s)]
    nbr = _neighbors(P, Pinv, V, s, ctx)
    cur = _cost(nbr, sources, D)
    for it in range(ITERS):
        if cur == 0 or time.monotonic() > deadline:
            break
        temp = 2.0 * (1.0 - it / ITERS) + 0.05
        if s == 1 or rng.random() < 0.7:
            kk, i = rng.randrange(d), rng.randrange(s)
            old = int(V[kk, i])
            new_v = rng.randrange(G)
            if new_v == old:
                continue
            V[kk, i] = new_v
            cand = _neighbors(P, Pinv, V, s, ctx)
            c = _cost(cand, sources, D)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur, nbr = c, cand
            else:
                V[kk, i] = old
        else:
            kk = rng.randrange(d)
            a, b = rng.sample(range(s), 2)
            _swap(P, Pinv, kk, a, b)
            cand = _neighbors(P, Pinv, V, s, ctx)
            c = _cost(cand, sources, D)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur, nbr = c, cand
            else:
                _swap(P, Pinv, kk, a, b)
    if cur == 0:
        return P.copy(), V.copy()
    return None


def _graph(s, ctx, P, V, d):
    """Materialise the lift as (n, edges), deduplicated, with python int labels."""
    G = ctx[3]
    Pinv = np.zeros_like(P)
    for kk in range(d):
        for i in range(s):
            Pinv[kk, P[kk, i]] = i
    nbr = _neighbors(P, Pinv, V, s, ctx)
    edges = set()
    for x in range(s * G):
        for y in nbr[x].tolist():
            edges.add((x, y))
    return 2 * s * G, sorted(edges)


def _try_size(s, ctx, d, D, rng, deadline):
    """Several independent annealing restarts for one group."""
    for _ in range(RETRIES):
        if time.monotonic() > deadline:
            break
        st = _anneal(s, ctx, d, D, rng, deadline)
        if st is not None:
            return st
    return None


def _search(s, fam, k, d, D, rng, deadline, cap):
    """Find the largest modulus m (doubling then bisection) whose lift anneals to zero cost.

    Returns (best, lo, hi): best is (ctx, P, V) or None; lo is the largest success (0 if none);
    hi the smallest failure above lo (None if not established).
    """
    m_min = 3 if fam == "dih" else (2 if fam == "sd" else 1)
    best = None
    lo, hi = 0, None
    m = m_min
    while time.monotonic() < deadline:
        G = m * k
        if 2 * s * G > cap:
            hi = m if hi is None else min(hi, m)
        else:
            ctx = _family_ctx(fam, k, m, rng)
            st = _try_size(s, ctx, d, D, rng, deadline)
            if st is not None:
                lo = m
                best = (ctx, st[0], st[1])
            else:
                hi = m
        if hi is None:
            m = 2 * lo
        else:
            if hi - lo <= 1:
                break
            m = (lo + hi) // 2
        if m < m_min:
            break
    return best, lo, hi


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
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

    bases = []
    if d >= 3 and D >= 3:
        pg = _pg_base(d)
        if pg is not None:
            if D == 3 and lib.is_prime_power(d - 1):   # Moore-extremal
                return _finish(cands + [pg], d, D)
            bases.append(pg)

    if d >= 3 and D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            if D == 4 and d - 1 <= GQ_Q_MAX and lib.is_prime_power(d - 1):  # Moore-extremal
                return _finish(cands + [gq], d, D)
            bases.append(gq)

    # Grow each structured base into its spare degree.
    for base in bases:
        cands.append(base)
        now = time.monotonic()
        if now < deadline:
            cands.append(_grow(base[0], base[1], d, D, min(deadline, now + 1.0), rng))

    cap = min(N_CAP, lib._moore_bound(d, D))

    # Small Haar slice (cheap, sometimes competitive for small d).
    now = time.monotonic()
    haar_frac = 0.1 if D <= 4 else 0.05
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

    # Group-lift annealing over cyclic, dihedral and (for some s) semidirect families.
    lift_best = None
    lift_rec = None
    for idx, s in enumerate(S_LIST):
        now = time.monotonic()
        if now >= deadline:
            break
        fams = [("cyc", 1), ("dih", 2)]
        if s in SD_S:
            fams.append(("sd", rng.choice(SD_K)))
        slice_end = now + (deadline - now) / (len(S_LIST) - idx)
        for f_idx, (fam, k) in enumerate(fams):
            now = time.monotonic()
            if now >= slice_end:
                break
            fam_end = now + (slice_end - now) / (len(fams) - f_idx)
            best, lo, hi = _search(s, fam, k, d, D, rng, fam_end, cap)
            if best is not None:
                ctx, P, V = best
                g = _graph(s, ctx, P, V, d)
                cands.append(g)
                if lift_best is None or g[0] > lift_best[0]:
                    lift_best = g
                    lift_rec = (s, fam, k, lo, hi)

    # Retry annealing just above the best lift size with the leftover time.
    if lift_rec is not None:
        s, fam, k, lo, hi = lift_rec
        m = hi if hi is not None else lo + 1
        while time.monotonic() < post_end:
            if 2 * s * (m * k) > cap:
                break
            ctx = _family_ctx(fam, k, m, rng)
            st = _anneal(s, ctx, d, D, rng, post_end)
            if st is not None:
                g = _graph(s, ctx, st[0], st[1], d)
                cands.append(g)
                if g[0] > lift_best[0]:
                    lift_best = g
                m += 1

    return _finish(cands, d, D)
