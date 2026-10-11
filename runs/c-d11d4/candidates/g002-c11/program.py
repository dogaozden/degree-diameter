import itertools
import random
import time

import lib


# Echo program: reads a graph on stdin and prints it back unchanged. It is used as a
# final round-trip check of the output format. Any failure falls back to the Python graph.
C_SOURCE = r'''
#include <stdio.h>
int main(void) {
    int n = 0, m = 0, a = 0, b = 0;
    if (scanf("%d %d", &n, &m) != 2) { printf("0 0\n"); return 0; }
    printf("%d %d\n", n, m);
    for (int i = 0; i < m; i++) {
        if (scanf("%d %d", &a, &b) != 2) break;
        printf("%d %d\n", a, b);
    }
    return 0;
}
'''


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q).

    Points are all points of PG(3, q); lines are totally isotropic lines of the
    symplectic form B(x, y) = x0*y1 - x1*y0 + x2*y3 - x3*y2. Degree is q + 1,
    diameter is 4, and the order is 2(q+1)(q^2+1).
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
    """W(q) incidence graph for the largest prime power q <= 16 with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Helpers on adjacency lists.
# ----------------------------------------------------------------------------

def _balls_radius(n, adj, r):
    """Bitmask per vertex of all vertices within distance r."""
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
    """Two-colouring of a bipartite graph given by adjacency lists."""
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
    """Greedy set cover of `full` by at most d candidates. Returns the list, or None."""
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
        thr = best_g
        if randomize and rng.random() < 0.5:
            thr = best_g - 1
        opts = [i for i, g in enumerate(gains) if g >= thr and g > 0]
        i = rng.choice(opts) if randomize else opts[0]
        s = pool.pop(i)
        chosen.append(s)
        covered |= ball[s]
    return chosen if covered == full else None


def _saturate_edges(n, edges, d, rng):
    """Add edges between deficient opposite-side vertices. Only adds edges, so diameter is kept."""
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


# ----------------------------------------------------------------------------
# Pair insertion: a new point p and a new line l are added together, joined to
# each other, with p attached to a cover of the other side and l attached to a
# cover of its side. Every vertex x satisfies dist(p, x) <= 1 + (D-1) = D by the
# cover of p, and likewise for l, so the diameter bound holds without checking.
# The move only uses spare degree, so it never deletes an edge.
# ----------------------------------------------------------------------------

def _pair_move(n, adj, color, d, D, rng):
    """One pair insertion on the current graph. Returns (n2, adj2, color2) or None."""
    lst = [list(s) for s in adj]
    ball = _balls_radius(n, lst, D - 1)
    full = (1 << n) - 1
    c0 = [v for v in range(n) if color[v] == 0 and len(adj[v]) < d]
    c1 = [v for v in range(n) if color[v] == 1 and len(adj[v]) < d]
    S1 = None
    S0 = None
    for _ in range(20):
        S1 = _greedy_cover(c1, ball, full, d - 1, rng, True)
        if S1:
            break
    if not S1:
        return None
    for _ in range(20):
        S0 = _greedy_cover(c0, ball, full, d - 1, rng, True)
        if S0:
            break
    if not S0:
        return None
    p = n
    l = n + 1
    adj2 = [set(s) for s in adj] + [set(), set()]
    color2 = list(color) + [0, 1]
    for s in S1:
        adj2[p].add(s)
        adj2[s].add(p)
    for s in S0:
        adj2[l].add(s)
        adj2[s].add(l)
    adj2[p].add(l)
    adj2[l].add(p)
    return n + 2, adj2, color2


def _pair_grow(n, edges, d, D, deadline, rng):
    """Repeat pair insertions until the deadline. Returns the largest graph seen."""
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    color = _bipartition(n, [list(s) for s in adj])
    cur = (n, adj, color)
    best_n = n
    best_e = list(edges)
    fails = 0
    while time.monotonic() < deadline:
        cn, ca, cc = cur
        res = _pair_move(cn, ca, cc, d, D, rng)
        if res is None:
            fails += 1
            if fails >= 200:
                break
            continue
        fails = 0
        cur = res
        if cur[0] > best_n:
            best_n = cur[0]
            ca2 = cur[1]
            best_e = [(u, w) for u in range(best_n) for w in ca2[u] if u < w]
    return best_n, best_e


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    deadline = t0 + 0.75 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Already at the Moore bound (e.g. d = 3, D = 3): nothing to gain.
    if best_n >= lib.moore_bound(d, D):
        return best

    # Bases: the generalized quadrangle for D >= 4 and the projective plane for D >= 3.
    bases = []
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            bases.append(gq)
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            bases.append(pg)

    for i, (bn, be) in enumerate(bases):
        consider(bn, be)
        now = time.monotonic()
        if now >= deadline:
            break
        slice_end = now + (deadline - now) / (len(bases) - i)
        gn, ge = _pair_grow(bn, be, d, D, slice_end, rng)
        consider(gn, ge)
        # Use leftover spare degree; this only adds edges, so the diameter is kept.
        sat = _saturate_edges(gn, ge, d, rng)
        consider(gn, sat)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))

    # Optional round trip through the C engine (format check). Any failure keeps the Python graph.
    try:
        if time.monotonic() < t0 + 0.9 * time_limit:
            txt = lib.run_c(C_SOURCE, [d, D, seed, 1], stdin_graph=best, timeout=5.0)
            n2, e2 = lib.parse_graph_text(txt)
            if n2 == best[0] and len(e2) == len(best[1]) and lib.is_valid(n2, e2, d, D):
                best = (n2, e2)
    except Exception:
        pass

    return best
