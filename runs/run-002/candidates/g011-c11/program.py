"""Combined construction program.

Pipeline A (bi-Cayley graphs, semidirect-group lifts, algebraic bases with growth).
Pipeline B (polarity and projective bases, cyclic voltage-lift annealing, bad-pair
repair, iterated remove-and-regrow). Both run in sequence on disjoint time shares,
and the largest valid graph wins.
"""
import itertools
import math
import random
import time

import numpy as np

import lib

# ---------------------------------------------------------------- constants

N_CAP = 6000                  # hard cap on vertex count
S_LIST = (1, 2, 3, 4, 5, 6)   # base vertices per side (lifts)
GQ_Q_MAX = 9                  # largest q for which W(q) is built
RETRIES = 2                   # annealing attempts per lift order
TOTAL_FRAC = 0.8              # share of time_limit used overall
SPLIT_A = 0.5                 # share of the budget for pipeline A
POOL_KEEP = 8                 # candidates kept in pipeline A's pool

# pipeline A (bi-Cayley / semidirect lifts / algebraic)
ITERS_G = 1200                # annealing moves per group-lift attempt
EXTEND_SLICE = 0.5            # seconds per greedy extension run
EXTEND_TRIES = 6              # randomized greedy restarts per base graph
BC_N_MAX = 1600               # largest group order searched for bi-Cayley graphs
BC_GROUPS_PER_ORDER = 3       # semidirect presentations tried per group order
BC_PROBE_MAX = 6              # orders probed above the binary-search result
ALG_FRAC = 0.15               # share of working time for algebraic base extension
HAAR_FRAC = 0.1               # share of remaining time for Haar search
BC_FRAC = 0.3                 # share of remaining time for bi-Cayley search
POST_FRAC_A = 0.1             # share of working time reserved for final extension
TIME_FRAC_A = 0.8             # internal deadline fraction of pipeline A

# pipeline B (cyclic annealing / repair / ILS)
ITERS = 6000                  # annealing iterations per attempt (cyclic lifts)
GROW_SLICE = 0.5              # seconds per greedy growth variant (base graphs)
POST_LIFTS = 3                # number of largest lifts that get post-processing
POST_SLICE = 0.5              # seconds per growth variant on a lift
ILS_STEP = 0.5                # seconds allowed for one remove-and-regrow step
ILS_SLACK = 2                 # ILS may wander at most this far below the best size
ILS_DOWN_P = 0.2              # chance to accept a one-vertex shrink
REPAIR_FRAC = 0.1             # fraction of time_limit for repairing near-miss lifts
TIME_FRAC_B = 0.6             # internal deadline fraction of pipeline B
POST_FRAC_B = 0.7             # internal post-processing end fraction of pipeline B
ILS_FRAC = 0.85               # internal ILS end fraction of pipeline B


def _safe(fn, *args, **kw):
    """Call fn; return None on any exception so one failing phase cannot sink the build."""
    try:
        return fn(*args, **kw)
    except Exception:
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


def _extend(n, edges, d, D, rng, deadline):
    """Greedily add vertices, each attached to a set cover of the current graph."""
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
    """Several randomized greedy extensions, keeping the largest result."""
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
    """Add edges between opposite colour classes using spare degree."""
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


def _grow_alt(n, edges, d, D, rng, deadline):
    """Alternate spare-degree edge augmentation and greedy cover extension."""
    for _ in range(4):
        if time.monotonic() >= deadline:
            break
        _, e2 = _augment(n, edges, d, rng.randrange(1 << 30))
        n2, e3 = _extend(n, e2, d, D, rng, deadline)
        if n2 == n and len(e2) == len(edges):
            break
        n, edges = n2, e3
    return n, edges


def _greedy_cover(cand, sets, target, budget):
    """Pick at most `budget` candidates whose `sets` bitmasks jointly cover `target`."""
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
    """Alternate single-vertex and paired greedy extension until neither adds anything."""
    prev = -1
    while n != prev and time.monotonic() < deadline:
        prev = n
        n, edges = _extend(n, edges, d, D, rng, deadline)
        n, edges = _pair_extend(n, edges, d, D, rng, deadline)
    return n, edges


def _growth_variants(g, d, D, rng, end, slice_s):
    """Run both greedy growth styles on graph g."""
    out = []
    for fn in (_extend, _grow):
        e = min(end, time.monotonic() + slice_s)
        out.append(fn(g[0], g[1], d, D, rng, e))
    return out


def _best_valid(cands, d, D):
    """Return the largest candidate that passes lib.is_valid, or None."""
    for n, e in sorted(cands, key=lambda c: -c[0]):
        if lib.is_valid(n, e, d, D):
            return n, e
    return None


def _finish(cands, d, D):
    """Return the largest candidate that passes lib.is_valid, else K_{d,d}."""
    best = _best_valid(cands, d, D)
    if best is not None:
        return best
    return lib.haar_graph(d, range(d))


def _remove_vertex(n, edges, v):
    """Return (n-1, edges) with vertex v deleted and the remaining labels compacted."""
    out = []
    for a, b in edges:
        if a == v or b == v:
            continue
        a2 = a - 1 if a > v else a
        b2 = b - 1 if b > v else b
        out.append((a2, b2))
    return n - 1, out


def _ils(n, edges, d, D, rng, end):
    """Iterated local search: delete a random vertex, regrow, accept if valid and not too small."""
    cur = (n, list(edges))
    best = cur
    while time.monotonic() < end:
        n0, e0 = cur
        if n0 < 4:
            break
        v = rng.randrange(n0)
        m, e1 = _remove_vertex(n0, e0, v)
        step_end = min(end, time.monotonic() + ILS_STEP)
        m, e2 = _grow(m, e1, d, D, rng, step_end)
        if m < best[0] - ILS_SLACK:
            continue
        accept = m >= n0 or (m == n0 - 1 and rng.random() < ILS_DOWN_P)
        if accept and lib.is_valid(m, e2, d, D):
            cur = (m, e2)
            if m > best[0]:
                best = (m, e2)
    return best


def _repair(n, edges, d, D, rng, deadline):
    """Delete the vertices involved in the most bad pairs until every pair is within D."""
    edges = list(edges)
    while n > 2 and time.monotonic() < deadline:
        balls = lib._balls(n, edges, D)
        bad = [n - r.bit_count() for r in balls]
        if not any(bad):
            break
        k = max(1, n // 40)
        order = sorted(range(n), key=lambda v: (-bad[v], rng.random()))
        chosen = [v for v in order[:k] if bad[v] > 0]
        for v in sorted(chosen, reverse=True):
            n, edges = _remove_vertex(n, edges, v)
    return n, edges


# ---------------------------------------------------------------- algebraic bases

def _pg_base(d):
    """Incidence graph of PG(2,q), q the largest prime power <= d-1 (diameter 3)."""
    q = d - 1
    while q >= 2 and not lib.is_prime_power(q):
        q -= 1
    if q < 2:
        return None
    return lib.projective_plane_incidence(q)


def _polarity_cover(q):
    """Bipartite double cover of the Erdos-Renyi polarity graph ER_q."""
    F = lib.GF(q)
    pts = np.array(lib.projective_points(q), dtype=np.int64)
    m = len(pts)
    mul, add = F.mul_table, F.add_table
    terms = [mul[pts[:, None, c], pts[None, :, c]] for c in range(3)]
    dot = add[add[terms[0], terms[1]], terms[2]]
    A = (dot == 0)
    np.fill_diagonal(A, False)
    rows, cols = np.nonzero(np.triu(A, 1))
    edges = []
    for i, j in zip(rows.tolist(), cols.tolist()):
        edges.append((i, m + j))
        edges.append((j, m + i))
    return 2 * m, edges


def _er_base(d):
    """Polarity double cover for the largest prime power q <= d-1."""
    q = d - 1
    while q >= 2 and not lib.is_prime_power(q):
        q -= 1
    if q < 2:
        return None
    return _polarity_cover(q)


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


# ---------------------------------------------------------------- Haar graphs

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


# ---------------------------------------------------------------- shared lift cost

def _swap(P, Pinv, k, a, b):
    P[k, a], P[k, b] = P[k, b], P[k, a]
    Pinv[k, P[k, a]] = a
    Pinv[k, P[k, b]] = b


def _cost(nbr, sources, D):
    """Number of (source, vertex) pairs NOT within distance D. Zero iff valid (fiber-transitive lifts)."""
    n = nbr.shape[0]
    S = len(sources)
    R = np.zeros((S, n), dtype=bool)
    R[np.arange(S), sources] = True
    for _ in range(D):
        Mx = R.copy()
        for k in range(nbr.shape[1]):
            Mx |= R[:, nbr[:, k]]
        if np.array_equal(Mx, R):
            break
        R = Mx
    return int(S * n - np.count_nonzero(R))


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


def _anneal_any(s, m, d, D, rng, deadline):
    """Simulated annealing over permutations and voltages. Returns (final_cost, P, V)."""
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
    return cur, P.copy(), V.copy()


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
    """Attempt to anneal a valid lift of size m, with a few restarts."""
    worst = None
    for _ in range(RETRIES):
        if time.monotonic() > deadline:
            break
        cost, P, V = _anneal_any(s, m, d, D, rng, deadline)
        if cost == 0:
            return (P, V), None
        if worst is None or cost < worst[0]:
            worst = (cost, P, V)
    return None, worst


def _search(s, d, D, rng, deadline, cap):
    """For fixed s, find the largest m whose cyclic lift passes annealing. Returns (best, near)."""
    best = None
    near = None
    lo, hi = 0, None
    m = 1
    while time.monotonic() < deadline:
        if 2 * s * m > cap:
            hi = m
        else:
            st, miss = _try_size(s, m, d, D, rng, deadline)
            if st is not None:
                lo = m
                best = (m, st[0], st[1])
            else:
                hi = m
                if miss is not None:
                    ratio = miss[0] / (2 * s * m)
                    if near is None or ratio < near[0]:
                        near = (ratio, m, miss[1], miss[2])
        if hi is None:
            m = 2 * lo
        else:
            if hi - lo <= 1:
                break
            m = (lo + hi) // 2
    return best, near


# ---------------------------------------------------------------- semidirect groups

# Group Z_m x|_r Z_k, element (a, b) coded as a*k + b, product (a,b)(c,d) = (a + r^b c, b + d).

def _presentations(M, rng, limit):
    """Random semidirect presentations (m, k, r) of groups of order M (k <= 8)."""
    out = []
    ks = [k for k in range(1, 9) if M % k == 0]
    rng.shuffle(ks)
    for k in ks:
        m = M // k
        if m == 1:
            out.append((1, k, 0))
        elif k == 1:
            out.append((m, 1, 1))
        else:
            cands = [m - 1] if k == 2 else []
            for _ in range(40):
                r = rng.randrange(1, m)
                if math.gcd(r, m) == 1 and pow(r, k, m) == 1:
                    cands.append(r)
            if cands:
                out.append((m, k, rng.choice(cands)))
        if len(out) >= limit:
            break
    return out


class _Grp:
    """Semidirect group Z_m x|_r Z_k of order M = m*k with vectorised right multiplication."""

    def __init__(self, m, k, r):
        self.m, self.k, self.r = m, k, r
        self.M = m * k
        self.powers = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
        X = np.arange(self.M, dtype=np.int64)
        a, b = X // k, X % k
        nb = (-b) % k
        c = (-self.powers[nb] * a) % m
        self.inv = c * k + nb

    def mul(self, X, g):
        """Return X * g elementwise (X an array, g a scalar element)."""
        a1, b1 = X // self.k, X % self.k
        a2, b2 = g // self.k, g % self.k
        a = (a1 + self.powers[b1] * a2) % self.m
        b = (b1 + b2) % self.k
        return a * self.k + b


def _gcol(nbr, kk, sig, sinv, G, s, M, grp):
    """Fill neighbour column kk for every lift vertex."""
    Y = np.arange(M, dtype=np.int64)
    for i in range(s):
        j = int(sig[kk, i])
        nbr[i * M:(i + 1) * M, kk] = s * M + j * M + grp.mul(Y, int(G[kk, i]))
    for j in range(s):
        i = int(sinv[kk, j])
        gi = int(grp.inv[int(G[kk, i])])
        nbr[s * M + j * M: s * M + (j + 1) * M, kk] = i * M + grp.mul(Y, gi)


def _lift_anneal(s, M, grp, d, D, rng, deadline, iters):
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
        _gcol(nbr, kk, sig, sinv, G, s, M, grp)
    sources = [i * M for i in range(s)] + [s * M + j * M for j in range(s)]
    cur = _cost(nbr, sources, D)
    for it in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        temp = 2.0 * (1.0 - it / iters) + 0.05
        if s == 1 or rng.random() < 0.6:
            kk, i = rng.randrange(d), rng.randrange(s)
            old = int(G[kk, i])
            new = rng.randrange(M)
            if new == old:
                continue
            G[kk, i] = new
            _gcol(nbr, kk, sig, sinv, G, s, M, grp)
            c = _cost(nbr, sources, D)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur = c
            else:
                G[kk, i] = old
                _gcol(nbr, kk, sig, sinv, G, s, M, grp)
        else:
            kk = rng.randrange(d)
            a, b = rng.sample(range(s), 2)
            _swap(sig, sinv, kk, a, b)
            _gcol(nbr, kk, sig, sinv, G, s, M, grp)
            c = _cost(nbr, sources, D)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur = c
            else:
                _swap(sig, sinv, kk, a, b)
                _gcol(nbr, kk, sig, sinv, G, s, M, grp)
    return nbr if cur == 0 else None


def _nbr_edges(nbr):
    """Deduplicated edge list from a neighbour table."""
    n, d = nbr.shape
    xs = np.repeat(np.arange(n, dtype=np.int64), d)
    ys = nbr.reshape(-1)
    lo = np.minimum(xs, ys)
    hi = np.maximum(xs, ys)
    keys = np.unique(lo * n + hi)
    return [(int(x // n), int(x % n)) for x in keys.tolist()]


def _lift_try(s, M, d, D, rng, deadline):
    """Try a few random presentations of order M. Returns edge list or None."""
    pres = _presentations(M, rng, 4)
    for _ in range(RETRIES):
        if time.monotonic() >= deadline:
            break
        m, k, r = rng.choice(pres)
        grp = _Grp(m, k, r)
        nbr = _lift_anneal(s, M, grp, d, D, rng, deadline, ITERS_G)
        if nbr is not None:
            return _nbr_edges(nbr)
    return None


def _lift_search(s, d, D, rng, deadline, cap):
    """Doubling then bisection over group order M for a fixed base size s. Returns (n, edges) or None."""
    best = None
    lo, hi = 0, None
    M = max(2, d)
    while time.monotonic() < deadline:
        if 2 * s * M > cap:
            if lo == 0:
                break
            hi = M
        else:
            edges = _lift_try(s, M, d, D, rng, deadline)
            if edges is not None:
                lo = M
                best = (2 * s * M, edges)
            elif lo == 0:
                M *= 2
                continue
            else:
                hi = M
        if hi is None:
            M = 2 * M
        else:
            if hi - lo <= max(1, lo // 16):
                break
            M = (lo + hi) // 2
    return best


# ---------------------------------------------------------------- bi-Cayley graphs

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


def _uncovered(tab, invs, S, N, D):
    """Number of (source, vertex) pairs not within distance D, over sources (e, L) and (e, R)."""
    fwd = [tab[s] for s in S]
    bwd = [tab[invs[s]] for s in S]
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


def _anneal_bc(N, tab, invs, d, D, rng, budget_end):
    """Search a connection set S of size d with zero uncovered pairs. Returns S or None."""
    if d > N:
        return None
    S = rng.sample(range(N), d)
    cur = _uncovered(tab, invs, S, N, D)
    start = time.monotonic()
    span = max(1e-3, budget_end - start)
    while cur > 0:
        now = time.monotonic()
        if now >= budget_end:
            break
        frac = (now - start) / span
        temp = 1.0 * (1.0 - frac) + 0.05
        i = rng.randrange(d)
        t = rng.randrange(N)
        if t in S:
            continue
        T = S[:]
        T[i] = t
        c = _uncovered(tab, invs, T, N, D)
        if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
            S, cur = T, c
    return S if cur == 0 else None


def _bc_graph(N, tab, S):
    """Bi-Cayley graph: left x joined to right N + x*s for s in S."""
    edges = []
    for s in S:
        row = tab[s].tolist()
        for x in range(N):
            edges.append((x, N + row[x]))
    return 2 * N, edges


def _try_order(N, d, D, rng, end):
    """Try to realise a valid bi-Cayley graph of group order N over a few presentations."""
    pres = _presentations(N, rng, BC_GROUPS_PER_ORDER)
    for idx, (m, k, r) in enumerate(pres):
        now = time.monotonic()
        if now >= end:
            break
        per_end = now + (end - now) / (len(pres) - idx)
        _, tab, invs = _group_tables(m, k, r)
        S = _anneal_bc(N, tab, invs, d, D, rng, per_end)
        if S is not None:
            return _bc_graph(N, tab, S)
    return None


def _bicayley_best(d, D, rng, deadline):
    """Binary search over group orders, then probe a few larger orders with leftover time."""
    moore = lib._moore_bound(d, D)
    N_hi = min(N_CAP // 2, moore // 2, BC_N_MAX)
    N_lo = max(d, N_hi // 3)
    if N_hi < N_lo or N_hi < d:
        return None
    orders = list(range(N_lo, N_hi + 1))
    best, best_idx = None, -1
    lo, hi = 0, len(orders) - 1
    while lo <= hi and time.monotonic() < deadline - 0.2:
        mid = (lo + hi) // 2
        N = orders[mid]
        now = time.monotonic()
        budget_end = min(deadline, now + max(0.5, 0.25 * (deadline - now)))
        g = _try_order(N, d, D, rng, budget_end)
        if g is not None:
            if best is None or g[0] > best[0]:
                best, best_idx = g, mid
            lo = mid + 1
        else:
            hi = mid - 1
    if best is not None:
        idx, probes = best_idx + 1, 0
        while (idx < len(orders) and probes < BC_PROBE_MAX
               and time.monotonic() < deadline - 0.2):
            N = orders[idx]
            now = time.monotonic()
            budget_end = min(deadline, now + max(0.3, 0.15 * (deadline - now)))
            g = _try_order(N, d, D, rng, budget_end)
            if g is not None and g[0] > best[0]:
                best = g
            idx += 1
            probes += 1
    return best


# ---------------------------------------------------------------- pipeline A

def _pipe_a(d, D, seed, time_limit):
    """Algebraic base + extension, Haar, bi-Cayley, semidirect-group lifts."""
    start = time.monotonic()
    deadline = start + max(0.5, TIME_FRAC_A * time_limit - 1.0)
    rng = random.Random(seed)
    cap = min(N_CAP, lib._moore_bound(d, D))
    pool = [lib.haar_graph(d, range(d))]

    def add(c):
        if c is None:
            return
        pool.append(c)
        pool.sort(key=lambda item: -item[0])
        del pool[POOL_KEEP:]

    pg = _safe(_pg_base, d) if D == 3 else None
    gq = _safe(_best_gq, d) if D >= 4 else None
    base = pg if D == 3 else gq
    if base is not None:
        add(base)
        alg_end = min(deadline, time.monotonic()
                      + ALG_FRAC * max(0.0, deadline - time.monotonic()))
        aug = _augment(base[0], base[1], d, seed)
        add(aug)
        for h in (base, aug):
            now = time.monotonic()
            if now >= alg_end:
                break
            add(_safe(_extend_best, h[0], h[1], d, D, rng,
                      min(alg_end, now + EXTEND_SLICE)))
        now = time.monotonic()
        if now < alg_end:
            add(_safe(_grow_alt, aug[0], aug[1], d, D, rng,
                      min(alg_end, now + EXTEND_SLICE)))

    now = time.monotonic()
    haar_end = now + HAAR_FRAC * max(0.0, deadline - now)
    haar_m, haar_miss, haar_best = d + 1, 0, None
    while time.monotonic() < haar_end and haar_miss < 4 and 2 * haar_m <= cap:
        S = _safe(_search_haar, d, D, haar_m, rng, haar_end, 120)
        if S is not None:
            haar_best = lib.haar_graph(haar_m, S)
            haar_miss = 0
        else:
            haar_miss += 1
        haar_m += 1
    add(haar_best)

    if d >= 4 and D >= 4:
        now = time.monotonic()
        bc_end = now + BC_FRAC * max(0.0, deadline - now)
        add(_safe(_bicayley_best, d, D, rng, bc_end))

    post_reserve = POST_FRAC_A * max(0.0, deadline - start)
    lift_end = deadline - post_reserve
    for idx, s in enumerate(S_LIST):
        now = time.monotonic()
        if now >= lift_end:
            break
        slice_end = now + (lift_end - now) / (len(S_LIST) - idx)
        add(_safe(_lift_search, s, d, D, rng, slice_end, cap))

    if pool:
        top = pool[0]
        add(_safe(_extend_best, top[0], top[1], d, D, rng, deadline, tries=2))

    return _finish(pool, d, D)


# ---------------------------------------------------------------- pipeline B

def _pipe_b(d, D, seed, time_limit):
    """Polarity / projective / GQ bases, cyclic annealing lifts, repair, ILS."""
    start = time.monotonic()
    deadline = start + max(0.5, TIME_FRAC_B * time_limit - 1.0)
    post_end = start + max(0.5, POST_FRAC_B * time_limit - 1.0)
    ils_end = start + max(0.5, ILS_FRAC * time_limit - 1.0)
    rng = random.Random(seed)

    cands = [lib.haar_graph(d, range(d))]

    if d >= 3:
        base = _safe(_pg_base, d)
        if base is not None:
            cands.append(base)
            aug = _augment(base[0], base[1], d, seed)
            for g in (base, aug):
                cands.extend(_growth_variants(g, d, D, rng,
                                              min(deadline, time.monotonic() + 2 * GROW_SLICE),
                                              GROW_SLICE))
        if D == 3:
            er = _safe(_er_base, d)
            if er is not None:
                cands.append(er)
                er_aug = _augment(er[0], er[1], d, seed + 1)
                for g in (er, er_aug):
                    cands.extend(_growth_variants(g, d, D, rng,
                                                  min(deadline, time.monotonic() + 2 * GROW_SLICE),
                                                  GROW_SLICE))

    if D >= 4:
        gq = _safe(_best_gq, d)
        if gq is not None:
            cands.append(gq)
            aug = _augment(gq[0], gq[1], d, seed)
            for g in (gq, aug):
                cands.extend(_growth_variants(g, d, D, rng,
                                              min(deadline, time.monotonic() + 2 * GROW_SLICE),
                                              GROW_SLICE))

    cap = min(N_CAP, lib._moore_bound(d, D))

    now = time.monotonic()
    haar_frac = 0.2 if D <= 4 else 0.1
    haar_end = now + haar_frac * max(0.0, deadline - now)
    haar_best, haar_m, haar_miss = None, d + 1, 0
    while time.monotonic() < haar_end and haar_miss < 4:
        S = _safe(_search_haar, d, D, haar_m, rng, haar_end, 120)
        if S is not None:
            haar_best = lib.haar_graph(haar_m, S)
            haar_miss = 0
        else:
            haar_miss += 1
        haar_m += 1
    if haar_best is not None:
        cands.append(haar_best)

    lifts = []
    nears = []
    for idx, s in enumerate(S_LIST):
        now = time.monotonic()
        if now >= deadline:
            break
        slice_end = now + (deadline - now) / (len(S_LIST) - idx)
        res, near = _search(s, d, D, rng, slice_end, cap)
        if near is not None:
            nears.append((s, near))
        if res is not None:
            m, P, V = res
            g = _graph(s, m, P, V, d)
            cands.append(g)
            lifts.append(g)

    lifts.sort(key=lambda g: -g[0])
    for g in lifts[:POST_LIFTS]:
        if time.monotonic() >= post_end:
            break
        aug = _augment(g[0], g[1], d, seed)
        cands.append(aug)
        cands.extend(_growth_variants(aug, d, D, rng, post_end, POST_SLICE))

    rep_end = min(post_end, time.monotonic() + REPAIR_FRAC * time_limit)
    for s, (ratio, m, P, V) in nears:
        if time.monotonic() >= rep_end:
            break
        n0, e0 = _graph(s, m, P, V, d)
        n1, e1 = _repair(n0, e0, d, D, rng, rep_end)
        n1, e1 = _grow(n1, e1, d, D, rng, rep_end)
        cands.append((n1, e1))

    if D >= 3 and time.monotonic() < ils_end:
        best = _best_valid(cands, d, D)
        if best is not None:
            cands.append(_ils(best[0], best[1], d, D, rng, ils_end))

    return _finish(cands, d, D)


# ---------------------------------------------------------------- driver

def _build(d, D, seed, time_limit):
    # Trivial cases.
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D                                  # even cycle: bipartite, diameter D
        return L, [(i, (i + 1) % L) for i in range(L)]
    if D == 2:
        return lib.haar_graph(d, range(d))         # K_{d,d} is extremal for D = 2

    # Moore-extremal shortcuts (calibration cases return immediately).
    if D == 3 and lib.is_prime_power(d - 1):
        base = _safe(_pg_base, d)
        if base is not None:
            return _finish([base], d, D)
    if D == 4 and lib.is_prime_power(d - 1) and d - 1 <= GQ_Q_MAX:
        gq = _safe(_gq_w, d - 1)
        if gq is not None:
            return _finish([gq], d, D)

    total = max(1.0, TOTAL_FRAC * time_limit - 0.5)
    share_a = SPLIT_A * total
    share_b = total - share_a

    # Each pipeline receives its share scaled so that its internal end-time matches it.
    ca = _safe(_pipe_a, d, D, seed, share_a / TIME_FRAC_A)
    cb = _safe(_pipe_b, d, D, seed, share_b / ILS_FRAC)

    cands = [c for c in (ca, cb) if c is not None]
    return _finish(cands + [lib.haar_graph(d, range(d))], d, D)


def build(d, D, seed, time_limit):
    res = _safe(_build, d, D, seed, time_limit)
    if res is None:
        if d < 1 or D < 1:
            return 1, []
        if d == 1 or D == 1:
            return 2, [(0, 1)]
        return lib.haar_graph(d, range(d))
    return res
