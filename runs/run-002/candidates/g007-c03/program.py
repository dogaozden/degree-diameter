import itertools
import math
import random
import time

import numpy as np

import lib

N_CAP = 6000                  # hard cap on vertex count
ITERS = 6000                  # annealing iterations per attempt
S_LIST = (1, 2, 3, 4, 5, 6)   # number of base vertices per side
FAMILIES = (1, 2)             # 1: cyclic Z_m lifts, 2: dihedral Z_m x| Z_2 lifts
GQ_Q_MAX = 9                  # largest q for which W(q) is built (pair loop is O(P^2))
RETRIES = 2                   # annealing attempts per candidate lift size
TIME_FRAC = 0.8               # fraction of time_limit used for search
POST_FRAC = 0.85              # fraction of time_limit after which nothing new starts
POST_EXTEND_SLICE = 1.5       # seconds given to greedy extension of the best lift
EXTEND_SLICE = 0.7            # seconds given to greedy extension of each base graph
EXTEND_TRIES = 8              # randomized greedy restarts per base graph

# Bi-Cayley construction (used for weak target cases with D >= 4, d >= 4)
BC_N_MAX = 1600               # largest group order searched (graph has 2N vertices)
BC_GROUPS_PER_ORDER = 3       # semidirect groups tried per group order
BC_SAFETY_MARGIN = 1.0        # seconds kept free at the end
BC_PROBE_MAX = 6              # orders probed above the binary-search result

# Bold search parameters: greedy coverage seeding + sampled best-move local search
GREEDY_SAMPLE = 200           # candidates examined per greedy step
LOCAL_SAMPLE = 80             # candidate replacements examined per local move
STALL_LIMIT = 150             # non-improving moves before a perturbation


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


def _extend_best(n, edges, d, D, rng, deadline, tries=EXTEND_TRIES):
    """Run _extend several times with fresh random tie-breaking, keeping the largest result."""
    best = (n, list(edges))
    for t in range(tries):
        now = time.monotonic()
        if now >= deadline:
            break
        per = now + (deadline - now) / (tries - t)
        cand = _extend(n, edges, d, D, rng, per)
        if cand[0] > best[0]:
            best = cand
    return best


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

def _group(m, fam):
    """Return (order, inverse table) for the group of family fam built on modulus m.

    fam 1: cyclic Z_m. fam 2: dihedral-type Z_m x| Z_2 with (a,b)*(c,d) = (a + (-1)^b c, b + d),
    coded as 2a + b.
    """
    if fam == 1:
        G = m
        X = np.arange(G, dtype=np.int64)
        return G, (-X) % m
    G = 2 * m
    X = np.arange(G, dtype=np.int64)
    a, b = X // 2, X % 2
    pw = np.where(b == 0, 1, m - 1)
    INV = ((-pw * a) % m) * 2 + b
    return G, INV


def _mul(fam, m, g, v):
    """Return the array g * v (right multiplication by the scalar element v)."""
    if fam == 1:
        return (g + v) % m
    a, b = g // 2, g % 2
    c, d = v // 2, v % 2
    pw = np.where(b == 0, 1, m - 1)
    return ((a + pw * c) % m) * 2 + (b + d) % 2


# ---------------------------------------------------------------- lifts (annealing)

def _neighbors(P, Pinv, V, s, ctx):
    """Neighbour table (n x d) of the group lift of a d-regular bipartite base on s+s vertices."""
    fam, m, G, INV = ctx
    d = P.shape[0]
    g = np.arange(G, dtype=np.int64)
    nbr = np.empty((2 * s * G, d), dtype=np.int64)
    for kk in range(d):
        for i in range(s):
            j = int(P[kk, i])
            v = int(V[kk, i])
            nbr[i * G:(i + 1) * G, kk] = s * G + j * G + _mul(fam, m, g, v)
        for j in range(s):
            i = int(Pinv[kk, j])
            v_inv = int(INV[int(V[kk, i])])
            nbr[(s + j) * G:(s + j + 1) * G, kk] = i * G + _mul(fam, m, g, v_inv)
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


def _anneal(s, ctx, d, D, rng, deadline):
    """Simulated annealing over permutations and voltages. Returns (P, V) with zero cost, or None."""
    G = ctx[2]
    P = np.array([rng.sample(range(s), s) for _ in range(d)], dtype=np.int64)
    Pinv = np.zeros_like(P)
    for k in range(d):
        for i in range(s):
            Pinv[k, P[k, i]] = i
    V = np.array([[rng.randrange(G) for _ in range(s)] for _ in range(d)], dtype=np.int64)
    sources = [i * G for i in range(2 * s)]
    nbr = _neighbors(P, Pinv, V, s, ctx)
    cur = _cost(nbr, sources, D)
    for it in range(ITERS):
        if cur == 0 or time.monotonic() > deadline:
            break
        temp = 2.0 * (1.0 - it / ITERS) + 0.05
        if s == 1 or rng.random() < 0.7:
            k, i = rng.randrange(d), rng.randrange(s)
            old = int(V[k, i])
            new_v = rng.randrange(G)
            if new_v == old:
                continue
            V[k, i] = new_v
            cand = _neighbors(P, Pinv, V, s, ctx)
            c = _cost(cand, sources, D)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur, nbr = c, cand
            else:
                V[k, i] = old
        else:
            k = rng.randrange(d)
            a, b = rng.sample(range(s), 2)
            _swap(P, Pinv, k, a, b)
            cand = _neighbors(P, Pinv, V, s, ctx)
            c = _cost(cand, sources, D)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur, nbr = c, cand
            else:
                _swap(P, Pinv, k, a, b)
    if cur == 0:
        return P.copy(), V.copy()
    return None


def _graph(s, ctx, P, V, d):
    """Materialise the lift as (n, edges), deduplicated."""
    G = ctx[2]
    Pinv = np.zeros_like(P)
    for k in range(d):
        for i in range(s):
            Pinv[k, P[k, i]] = i
    nbr = _neighbors(P, Pinv, V, s, ctx)
    edges = set()
    for x in range(s * G):
        for y in nbr[x].tolist():
            edges.add((x, y))
    return 2 * s * G, sorted(edges)


def _try_size(s, ctx, d, D, rng, deadline):
    """Attempt to anneal a valid lift with the given group, with a few independent restarts."""
    for _ in range(RETRIES):
        if time.monotonic() > deadline:
            break
        st = _anneal(s, ctx, d, D, rng, deadline)
        if st is not None:
            return st
    return None


def _search(s, fam, d, D, rng, deadline, cap):
    """For fixed s and family, find the largest m (doubling then bisection) whose lift passes annealing.

    Returns (best, lo, hi): best is (ctx, P, V) or None, lo the largest m that succeeded
    (0 if none), hi the smallest m above lo that failed (None if not established).
    """
    best = None
    lo, hi = 0, None
    m = 1 if fam == 1 else 3
    while time.monotonic() < deadline:
        G = m if fam == 1 else 2 * m
        if 2 * s * G > cap:
            hi = m
        else:
            G, INV = _group(m, fam)
            ctx = (fam, m, G, INV)
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
    return best, lo, hi


# ---------------------------------------------------------------- bi-Cayley graphs over semidirect groups
#
# Group G = Z_m x|_r Z_k, element (a, b) coded as a*k + b, product (a,b)(c,d) = (a + r^b c, b + d).
# Left vertices x in G, right vertices y in G, edge x ~ y iff x^{-1} y in S (|S| = d).
# Left multiplication is an automorphism that is transitive on each side, so the diameter is
# at most D iff the radius-D balls around (e, L) and (e, R) both cover the whole graph.

def _group_tables(m, k, r):
    """Return (N, tab, invs): tab[s, x] = x * s, invs[s] = s^{-1}, for G = Z_m x|_r Z_k."""
    N = m * k
    pw = [pow(r, b, m) for b in range(k)]
    pw_arr = np.array(pw, dtype=np.int64)
    X = np.arange(N, dtype=np.int64)
    A, B = X // k, X % k
    tab = np.empty((N, N), dtype=np.int32)
    invs = np.empty(N, dtype=np.int64)
    for s in range(N):
        c, dd = divmod(s, k)
        tab[s] = ((A + pw_arr[B] * c) % m) * k + (B + dd) % k
        nb = (-dd) % k
        na = (-pw[nb] * c) % m
        invs[s] = na * k + nb
    return N, tab, invs


def _groups_for_order(N, rng):
    """Return a few (m, k, r) semidirect presentations of groups of order N (cyclic included)."""
    found = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) != 1:
                continue
            if pow(r, k, m) != 1 % m:
                continue
            found.append((m, k, r))
    rng.shuffle(found)
    return found[:BC_GROUPS_PER_ORDER]


def _uncovered(tab, invs, S, N, D):
    """Number of (source, vertex) pairs not within distance D, over sources (e, L) and (e, R)."""
    fwd = [tab[s] for s in S]          # left x -> right x*s
    bwd = [tab[invs[s]] for s in S]    # right y -> left y*s^{-1}
    total = 0
    for src_side in (0, 1):
        visL = np.zeros(N, dtype=bool)
        visR = np.zeros(N, dtype=bool)
        if src_side == 0:
            visL[0] = True
            fL = np.array([0], dtype=np.int64)
            fR = np.empty(0, dtype=np.int64)
        else:
            visR[0] = True
            fR = np.array([0], dtype=np.int64)
            fL = np.empty(0, dtype=np.int64)
        for _ in range(D):
            nR = np.zeros(N, dtype=bool)
            for row in fwd:
                nR[row[fL]] = True
            nL = np.zeros(N, dtype=bool)
            for row in bwd:
                nL[row[fR]] = True
            nR &= ~visR
            nL &= ~visL
            visR |= nR
            visL |= nL
            fL = np.flatnonzero(nL)
            fR = np.flatnonzero(nR)
            if fL.size == 0 and fR.size == 0:
                break
        total += 2 * N - int(visL.sum()) - int(visR.sum())
    return total


def _greedy_S(N, tab, invs, d, D, rng, end):
    """Build S element by element, each time keeping the sampled candidate with fewest uncovered pairs."""
    S = []
    for _ in range(d):
        if time.monotonic() >= end:
            return None
        pool = [t for t in rng.sample(range(N), min(N, GREEDY_SAMPLE)) if t not in S]
        best_t, best_c = None, None
        for t in pool:
            c = _uncovered(tab, invs, S + [t], N, D)
            if best_c is None or c < best_c:
                best_t, best_c = t, c
        if best_t is None:
            return None
        S.append(best_t)
    return S


def _search_S(N, tab, invs, d, D, rng, end):
    """Greedy seed, then sampled best-move local search with perturbation on stall. Returns S or None."""
    if d > N:
        return None
    S = _greedy_S(N, tab, invs, d, D, rng, end)
    if S is None:
        return None
    cur = _uncovered(tab, invs, S, N, D)
    if N == d:
        return S if cur == 0 else None
    stall = 0
    while cur > 0:
        if time.monotonic() >= end:
            break
        i = rng.randrange(d)
        Sset = set(S)
        pool = rng.sample(range(N), min(N, LOCAL_SAMPLE))
        best_t, best_c = None, None
        for t in pool:
            if t in Sset:
                continue
            T = S[:]
            T[i] = t
            c = _uncovered(tab, invs, T, N, D)
            if best_c is None or c < best_c:
                best_t, best_c = t, c
        if best_t is not None and best_c <= cur:
            stall = 0 if best_c < cur else stall + 1
            S[i] = best_t
            cur = best_c
        else:
            stall += 1
        if stall > STALL_LIMIT:
            Sset = set(S)
            for _ in range(2):
                j = rng.randrange(d)
                t = rng.randrange(N)
                while t in Sset:
                    t = rng.randrange(N)
                Sset.discard(S[j])
                S[j] = t
                Sset.add(t)
            cur = _uncovered(tab, invs, S, N, D)
            stall = 0
    return S if cur == 0 else None


def _bc_graph(N, tab, S):
    """Materialise the bi-Cayley graph: left x (0..N-1) joined to right N + x*s for s in S."""
    edges = []
    for s in S:
        row = tab[s].tolist()
        for x in range(N):
            edges.append((x, N + row[x]))
    return 2 * N, edges


def _try_order_bold(N, groups, d, D, rng, end):
    """Try to realise a valid bi-Cayley graph of group order N, splitting time across presentations."""
    for idx, (m, k, r) in enumerate(groups):
        now = time.monotonic()
        if now >= end:
            break
        per_end = now + (end - now) / (len(groups) - idx)
        _, tab, invs = _group_tables(m, k, r)
        S = _search_S(N, tab, invs, d, D, rng, per_end)
        if S is not None:
            return _bc_graph(N, tab, S)
    return None


def _bold_bicayley(d, D, seed, deadline):
    """Binary search over group orders with greedy-seeded search, then probe a few larger orders.

    Existence is not monotone in N, so after the binary search the next few larger orders
    are probed as well. Every returned graph is re-checked by the caller.
    """
    moore = lib._moore_bound(d, D)
    N_hi = min(N_CAP // 2, moore // 2, BC_N_MAX)
    N_lo = max(d, N_hi // 3)
    if N_hi < N_lo or N_hi < d:
        return None
    rng = random.Random(seed * 1000003 + 29 * d + 3 * D + 5)
    orders, groups = [], {}
    for N in range(N_lo, N_hi + 1):
        gs = _groups_for_order(N, rng)
        if gs:
            orders.append(N)
            groups[N] = gs
    if not orders:
        return None

    best, best_idx = None, -1
    lo, hi = 0, len(orders) - 1
    while lo <= hi and time.monotonic() < deadline - 0.2:
        mid = (lo + hi) // 2
        N = orders[mid]
        now = time.monotonic()
        budget_end = min(deadline, now + max(0.5, 0.3 * (deadline - now)))
        g = _try_order_bold(N, groups[N], d, D, rng, budget_end)
        if g is not None:
            if best is None or g[0] > best[0]:
                best, best_idx = g, mid
            lo = mid + 1
        else:
            hi = mid - 1

    if best is not None:
        idx = best_idx + 1
        probes = 0
        while (idx < len(orders) and probes < BC_PROBE_MAX
               and time.monotonic() < deadline - 0.2):
            N = orders[idx]
            now = time.monotonic()
            budget_end = min(deadline, now + max(0.3, 0.2 * (deadline - now)))
            g = _try_order_bold(N, groups[N], d, D, rng, budget_end)
            if g is not None and g[0] > best[0]:
                best = g
            idx += 1
            probes += 1
    return best


# ---------------------------------------------------------------- driver

def _parent_build(d, D, seed, time_limit):
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
                cands.append(_extend_best(g[0], g[1], d, D, rng,
                                          min(deadline, time.monotonic() + EXTEND_SLICE)))

    # D >= 4: generalized quadrangle W(q) (diameter 4 <= D), extended as well.
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            if D == 4 and d - 1 <= GQ_Q_MAX and lib.is_prime_power(d - 1):
                return _finish(cands + [gq], d, D)  # Moore-extremal for D = 4
            cands.append(gq)
            aug = _augment(gq[0], gq[1], d, seed)
            for g in (gq, aug):
                cands.append(_extend_best(g[0], g[1], d, D, rng,
                                          min(deadline, time.monotonic() + EXTEND_SLICE)))

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

    # Group-lift annealing: one slice per base size s, split across the group families.
    lift_best = None
    lift_rec = None   # (s, fam, lo, hi) for the largest lift found
    for idx, s in enumerate(S_LIST):
        now = time.monotonic()
        if now >= deadline:
            break
        slice_end = now + (deadline - now) / (len(S_LIST) - idx)
        for f_idx, fam in enumerate(FAMILIES):
            now = time.monotonic()
            if now >= slice_end:
                break
            fam_end = now + (slice_end - now) / (len(FAMILIES) - f_idx)
            best, lo, hi = _search(s, fam, d, D, rng, fam_end, cap)
            if best is not None:
                ctx, P, V = best
                g = _graph(s, ctx, P, V, d)
                cands.append(g)
                if lift_best is None or g[0] > lift_best[0]:
                    lift_best = g
                    lift_rec = (s, fam, lo, hi)

    # Retry annealing at the first size above the best lift.
    if lift_rec is not None:
        s, fam, lo, hi = lift_rec
        m = hi if hi is not None else lo + 1
        while time.monotonic() < post_end:
            G, INV = _group(m, fam)
            if 2 * s * G > cap:
                break
            ctx = (fam, m, G, INV)
            st = _anneal(s, ctx, d, D, rng, post_end)
            if st is not None:
                g = _graph(s, ctx, st[0], st[1], d)
                cands.append(g)
                if g[0] > lift_best[0]:
                    lift_best = g
                m += 1

    return _finish(cands, d, D)


def _ok(g, d, D):
    """True if the candidate passes the exact scorer checks."""
    try:
        return lib.is_valid(g[0], g[1], d, D)
    except Exception:
        return False


def build(d, D, seed, time_limit):
    start = time.monotonic()
    weak = d >= 4 and D >= 4 and time_limit >= 6   # bold path only for the weak target regime

    # Safe parent construction first. Weak cases give it a smaller slice so the bold search gets most time.
    parent_limit = 0.25 * time_limit if weak else time_limit
    best = None
    try:
        best = _parent_build(d, D, seed, parent_limit)
    except Exception:
        best = None
    if best is not None and not _ok(best, d, D):
        best = None

    # Bold bi-Cayley search; keep it only if it validates and is larger than the parent result.
    if weak:
        try:
            deadline = start + 0.85 * time_limit - BC_SAFETY_MARGIN
            cand = _bold_bicayley(d, D, seed, deadline)
            if cand is not None and _ok(cand, d, D):
                if best is None or cand[0] > best[0]:
                    best = cand
        except Exception:
            pass

    # Last-resort fallbacks, each verified.
    if best is None:
        if d < 1 or D < 1:
            return 1, []
        if d == 1 or D == 1:
            return 2, [(0, 1)]
        cand = lib.haar_graph(d, range(d))
        if _ok(cand, d, D):
            return cand
        return 2, [(0, 1)]
    return best
