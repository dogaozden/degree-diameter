import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Safe fallbacks: projective plane incidence graphs and their arc extensions.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _pg_data(q):
    """Return (m, edges, point_lines, line_points, index, pts) for PG(2, q)."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, point_lines, line_points, index, pts


def _loads_ok(S, s, m, point_lines, line_points):
    """True if every line holds <= s points of S and every point lies on <= s lines indexed by S."""
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
    """Randomized greedy choice of S with all loads <= s; returns the largest found."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        cl = [0] * m
        cp = [0] * m
        S = []
        for P in order:
            if all(cl[L] < s for L in point_lines[P]) and all(cp[Q] < s for Q in line_points[P]):
                S.append(P)
                for L in point_lines[P]:
                    cl[L] += 1
                for Q in line_points[P]:
                    cp[Q] += 1
        if len(S) > len(best):
            best = S
    return best


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    """Old PG incidence plus a new A and a new B vertex per element of S."""
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _arc_extensions(d, deadline, rng):
    """Return a list of (n, edges) candidates, one per prime power q with q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        cands = []
        if s >= 1:
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 40, deadline))
        if s >= 2:
            F = lib.GF(q)
            cs = _conic_set(q, index, F)
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len, default=[])
        if not S or not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


# ----------------------------------------------------------------------------
# New bold family for diameter 3: Haar graphs of groups from difference covers.
#
# For a finite group G and S with |S| = d, the bipartite graph with parts A_g, B_h
# and edges A_g ~ B_{g*s} (s in S) has diameter <= 3 iff S * S^{-1} = G.
# Same-side pairs are at distance 2 iff g^{-1}g' in S S^{-1}; opposite-side pairs
# are at distance 1 or 3 because S S^{-1} S covers G whenever S S^{-1} does.
# So we search for small "difference covers" in groups of order m, with m as
# large as possible (Moore-type ceiling: m <= d(d-1)+1, i.e. order 2m <= 2(d^2-d+1)).
# Annealing maximizes coverage with incremental counts, which is fast in Python.
# ----------------------------------------------------------------------------

def _group_options(m, rng):
    """Return (a, k, r) triples describing groups of order m: cyclic and a few semidirect products."""
    opts = [(m, 1, 1)]
    divs = [k for k in range(2, m) if m % k == 0 and m // k >= 2]
    rng.shuffle(divs)
    for k in divs[:3]:
        a = m // k
        rs = [r for r in range(1, a) if math.gcd(r, a) == 1 and pow(r, k, a) == 1 % a]
        if rs:
            opts.append((a, k, rng.choice(rs)))
    return opts


def _tables(order, mul, inv):
    """Multiplication and inverse tables for a group with elements 0..order-1 (identity 0)."""
    M = [[mul(x, y) for y in range(order)] for x in range(order)]
    I = [inv(x) for x in range(order)]
    return M, I


def _apply(S, cnt, M, I, i, v, zc):
    """Replace S[i] by v, updating the ordered-difference counts cnt and the zero counter zc[0]."""
    x = S[i]
    d = len(S)
    for j in range(d):
        if j == i:
            continue
        o = S[j]
        a = M[x][I[o]]
        cnt[a] -= 1
        if cnt[a] == 0:
            zc[0] += 1
        b = M[o][I[x]]
        cnt[b] -= 1
        if cnt[b] == 0:
            zc[0] += 1
    e = M[x][I[x]]
    cnt[e] -= 1
    if cnt[e] == 0:
        zc[0] += 1
    S[i] = v
    for j in range(d):
        if j == i:
            continue
        o = S[j]
        a = M[v][I[o]]
        if cnt[a] == 0:
            zc[0] -= 1
        cnt[a] += 1
        b = M[o][I[v]]
        if cnt[b] == 0:
            zc[0] -= 1
        cnt[b] += 1
    e = M[v][I[v]]
    if cnt[e] == 0:
        zc[0] -= 1
    cnt[e] += 1


def _anneal_cover(G, M, I, d, rng, budget):
    """Search S (|S| = d, identity included) with S S^{-1} = G. Returns S or None."""
    if G <= d or d < 2:
        return None
    t0 = time.monotonic()
    deadline = t0 + budget
    S = [0] + rng.sample(range(1, G), d - 1)
    cnt = [0] * G
    for x in S:
        for y in S:
            cnt[M[x][I[y]]] += 1
    zc = [sum(1 for c in cnt if c == 0)]
    if zc[0] == 0:
        return list(S)
    T = 1.0
    it = 0
    while True:
        it += 1
        if it & 255 == 0:
            now = time.monotonic()
            if now >= deadline:
                break
            frac = (now - t0) / max(budget, 1e-9)
            T = 0.05 ** frac
        i = rng.randrange(1, d)
        x = S[i]
        y = None
        if zc[0] > 0 and rng.random() < 0.6:
            # Guided move: pick an uncovered element u and try to create a difference equal to u.
            u = None
            for _ in range(20):
                g = rng.randrange(G)
                if cnt[g] == 0:
                    u = g
                    break
            if u is not None:
                j = rng.randrange(d)
                while j == i:
                    j = rng.randrange(d)
                o = S[j]
                cand = M[u][o] if rng.random() < 0.5 else M[I[u]][o]
                if cand not in S:
                    y = cand
        if y is None:
            y = rng.randrange(G)
            while y in S:
                y = rng.randrange(G)
        before = zc[0]
        _apply(S, cnt, M, I, i, y, zc)
        delta = zc[0] - before
        if delta > 0 and rng.random() >= math.exp(-delta / T):
            _apply(S, cnt, M, I, i, x, zc)
        if zc[0] == 0:
            return list(S)
    return None


def _haar_from_group(order, M, S):
    """Bipartite graph with parts A_g = g and B_h = order + h; edges A_g ~ B_{g*s} for s in S."""
    n = 2 * order
    edges = []
    for g in range(order):
        for s in S:
            edges.append((g, order + M[g][s]))
    return n, edges


def _search_haar(d, D, rng, deadline, consider):
    """Climb through group orders m, each time annealing a difference cover of size d."""
    maxm = d * (d - 1) + 1
    cap = min(maxm, 260)
    m = max(d + 1, maxm // 2)
    retries = 0
    while m <= cap and time.monotonic() < deadline:
        rem = deadline - time.monotonic()
        budget = min(max(0.3, 0.3 * rem), 12.0)
        opts = _group_options(m, rng)
        found = None
        for a, k, r in opts:
            if time.monotonic() >= deadline:
                break
            order, mul, inv = lib.semidirect_group(a, k, r)
            M, I = _tables(order, mul, inv)
            S = _anneal_cover(order, M, I, d, rng, budget / len(opts))
            if S is not None:
                found = (order, M, S)
                break
        if found is not None:
            order, M, S = found
            n, e = _haar_from_group(order, M, S)
            consider(n, e)
            m += 1
            retries = 0
        else:
            if retries >= 1:
                break
            retries += 1


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1:
        return 2, [(0, 1)]
    if D == 2:
        return lib.haar_graph(d, range(d))

    # Safe fallback: K_{d,d} has diameter 2, valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        for n_c, e_c in _arc_extensions(d, start + 0.2 * time_limit,
                                        random.Random(seed * 7919 + d)):
            consider(n_c, e_c)
        _search_haar(d, D, rng, deadline, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
