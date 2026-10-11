import math
import random
import time

import lib


C_SOURCE = r"""
#include <stdio.h>
int main(void) {
    /* Pass-through placeholder: echo the start graph ("n m" then m edge lines). */
    long n, m;
    if (scanf("%ld %ld", &n, &m) != 2) { printf("0 0\n"); return 0; }
    printf("%ld %ld\n", n, m);
    for (long i = 0; i < m; i++) {
        long u, v;
        if (scanf("%ld %ld", &u, &v) != 2) break;
        printf("%ld %ld\n", u, v);
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3). Baseline only.
# ----------------------------------------------------------------------------

def _pg_data(q):
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
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
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
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, S, line_points):
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
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 20, deadline))
        if s >= 2:
            F = lib.GF(q)
            cs = _conic_set(q, index, F)
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len, default=[])
        if not S or not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, S, line_points))
    return out


# ----------------------------------------------------------------------------
# Bi-Cayley Haar graphs over groups of order G.
#
# Vertices a_g = g and b_g = G + g. Each a_g is joined to b_{g*s} for s in S,
# with |S| = d. Same-side distances are 2 exactly when S*S^{-1} = G, and
# opposite-side distances are at most 3 under the same condition. So the graph
# is valid for diameter 3 iff S*S^{-1} covers the whole group. The order is 2G,
# and G <= d(d-1)+1 gives the Moore-type ceiling 2(d^2-d+1).
# ----------------------------------------------------------------------------

def _group_options(G, rng):
    """Return (mul_table, inv_list) for a cyclic group and a few semidirect products of order G."""
    opts = []
    _, mul, inv = lib.cyclic_group(G)
    opts.append((mul, inv))
    cand = []
    for k in range(2, G):
        if G % k:
            continue
        M = G // k
        if M < 3:
            continue
        for r in range(2, M):
            if math.gcd(r, M) == 1 and pow(r, k, M) == 1:
                cand.append((M, k, r))
    rng.shuffle(cand)
    for M, k, r in cand[:4]:
        _, mul2, inv2 = lib.semidirect_group(M, k, r)
        opts.append((mul2, inv2))
    tables = []
    for mul_f, inv_f in opts:
        T = [[mul_f(x, y) for y in range(G)] for x in range(G)]
        I = [inv_f(x) for x in range(G)]
        tables.append((T, I))
    return tables


def _search_cover(G, d, T, I, rng, deadline, iters):
    """Simulated annealing for a d-subset S with S*S^{-1} = G. Returns S or None."""
    if d > G:
        return None
    S = rng.sample(range(G), d)

    def cost(S_):
        return G - len({T[s][I[t]] for s in S_ for t in S_})

    c = cost(S)
    temp = 0.6
    for it in range(iters):
        if c == 0:
            return S
        if (it & 127) == 0 and time.monotonic() > deadline:
            break
        i = rng.randrange(d)
        new = rng.randrange(G)
        if new in S:
            continue
        old = S[i]
        S[i] = new
        c2 = cost(S)
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / temp):
            c = c2
        else:
            S[i] = old
        temp = max(0.12, temp * 0.9995)
    return S if c == 0 else None


def _haar_search(d, D, base_m, deadline, rng, consider):
    """Try G = base_m+1, base_m+2, ... ; stop at the first order where no cover is found in its slice."""
    m_hi = d * (d - 1) + 1
    G = base_m + 1
    while G <= m_hi:
        now = time.monotonic()
        if now >= deadline:
            break
        slice_end = now + 0.45 * (deadline - now)
        pool = _group_options(G, rng)
        found = None
        attempt = 0
        while time.monotonic() < slice_end and found is None:
            T, I = pool[attempt % len(pool)]
            attempt += 1
            found = _search_cover(G, d, T, I, rng, slice_end, 30000)
            if found is not None:
                T_used = T
        if found is None:
            break
        edges = []
        for g in range(G):
            for s in found:
                edges.append((g, G + T_used[g][s]))
        consider(2 * G, edges)
        G += 1


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    state = {"best": lib.haar_graph(d, range(d))}

    def consider(n, e):
        if n > state["best"][0] and lib.is_valid(n, e, d, D):
            state["best"] = (n, e)

    if D >= 3:
        # Baseline: arc-extended PG(2,q) graphs (valid for diameter 3).
        arc_deadline = start + 0.2 * time_limit
        for n_c, e_c in _arc_extensions(d, arc_deadline, random.Random(seed * 7919 + d)):
            consider(n_c, e_c)

        # Main search: Haar graphs over groups of order just above the baseline half-order.
        base_m = state["best"][0] // 2
        _haar_search(d, D, base_m, deadline, random.Random(seed * 104729 + d), consider)

    best = state["best"]
    if not lib.is_valid(best[0], best[1], d, D):
        return lib.haar_graph(d, range(d))
    return best
