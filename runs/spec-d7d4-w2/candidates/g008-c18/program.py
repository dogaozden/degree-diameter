"""Bold variant for d = 7, D = 4: cyclic voltage lifts of small bipartite base graphs.

Instead of expanding a projective-plane or quadrangle base by twin packing and cover
growth, this program searches directly for Z_m-lifts of a bipartite base multigraph
with k vertices per side and degree d. Each candidate is scored by the number of
vertex pairs farther than D apart, using only one source per base vertex (Z_m acts
transitively on each fibre). A hill-climb over voltages drives that count to zero.
The largest verified lift wins. Fallbacks are K_{d,d} and the generalized quadrangle
W(q) for D = 4, the projective plane / Araujo-Pardo-Lopez graph for D = 3.
Every returned graph is checked with lib.is_valid.
"""
import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Fixed bases (fallbacks / seeds).
# ----------------------------------------------------------------------------

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


def _pg_base(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1, or None."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Z_m voltage lifts of a k + k bipartite base with d darts per base vertex.
#   dart (t, i) joins A-vertex (i, g) to B-vertex (perms[t][i], g + V[t][i]).
#   Vertex ids: A (i, g) -> i*m + g; B (j, h) -> k*m + j*m + h.
# ----------------------------------------------------------------------------

def _lift_adj(k, m, d, perms, V):
    n = 2 * k * m
    off = k * m
    adj = [[] for _ in range(n)]
    for t in range(d):
        P = perms[t]
        Vt = V[t]
        for i in range(k):
            j = P[i]
            s = Vt[i]
            ba = i * m
            bb = off + j * m
            for g in range(m):
                a = ba + g
                b = bb + (g + s) % m
                adj[a].append(b)
                adj[b].append(a)
    return n, adj


def _bad(n, adj, D, sources):
    """Number of vertices NOT within distance D of the given sources (bitset BFS).

    Translation by Z_m is an automorphism, so one source per base vertex suffices:
    zero here means the whole lift has diameter <= D.
    """
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            x = reach[v]
            for u in adj[v]:
                x |= reach[u]
            new[v] = x
        reach = new
    return sum(n - reach[s].bit_count() for s in sources)


def _climb(k, m, d, D, deadline, rng):
    """Hill-climb voltages (with plateau moves) until the lift has diameter <= D."""
    perms = [rng.sample(range(k), k) for _ in range(d)]
    V = [[rng.randrange(m) for _ in range(k)] for _ in range(d)]
    sources = [i * m for i in range(k)] + [k * m + j * m for j in range(k)]
    n, adj = _lift_adj(k, m, d, perms, V)
    cur = _bad(n, adj, D, sources)
    while cur > 0:
        if time.monotonic() >= deadline:
            return None
        t = rng.randrange(d)
        i = rng.randrange(k)
        old = V[t][i]
        V[t][i] = rng.randrange(m)
        n, adj = _lift_adj(k, m, d, perms, V)
        nb = _bad(n, adj, D, sources)
        if nb <= cur:
            cur = nb
        else:
            V[t][i] = old
    return perms, V


def _lift_edges(k, m, d, perms, V):
    off = k * m
    E = set()
    for t in range(d):
        for i in range(k):
            j = perms[t][i]
            s = V[t][i]
            for g in range(m):
                E.add((i * m + g, off + j * m + (g + s) % m))
    return 2 * k * m, sorted(E)


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = float(time_limit)
    deadline = start + max(0.5, 0.85 * T - 0.5)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        # Even cycle C_{2D}: bipartite, degree 2, diameter D.
        return 2 * D, [(i, (i + 1) % (2 * D)) for i in range(2 * D)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 2:
        return best
    if best[0] >= lib.moore_bound(d, D):
        return best

    # Known bases.
    if D == 3:
        pg = _pg_base(d)
        if pg is not None:
            consider(pg[0], pg[1])
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                ab = lib.araujo_lopez_graph(d - 2)
                consider(ab[0], ab[1])
            except Exception:
                pass
    elif D == 4:
        for q in range(min(d - 1, 9), 1, -1):
            if lib.is_prime_power(q):
                try:
                    gq = _gq_w(q)
                    consider(gq[0], gq[1])
                except Exception:
                    pass
                break

    if best[0] >= lib.moore_bound(d, D):
        return best

    # Main search: Z_m lifts of k + k base graphs, round-robin over k.
    ks = [2, 3, 4, 5, 6, 8]
    slice_len = max(1.5, (deadline - time.monotonic()) / 10.0)
    mcur = {}
    try:
        while time.monotonic() < deadline:
            for k in ks:
                now = time.monotonic()
                if now >= deadline:
                    break
                # Smallest m giving a lift strictly larger than the current best.
                m = max(mcur.get(k, 0), best[0] // (2 * k) + 1)
                mcur[k] = m
                end = min(deadline, now + slice_len)
                res = _climb(k, m, d, D, end, rng)
                if res is not None:
                    perms, V = res
                    n, e = _lift_edges(k, m, d, perms, V)
                    consider(n, e)
                    mcur[k] = m + 1
                    if best[0] >= lib.moore_bound(d, D):
                        return best
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
