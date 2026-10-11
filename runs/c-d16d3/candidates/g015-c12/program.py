import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: penalty-driven local search with vertex insertion.
#
# State: a bipartite graph with max degree d. Cost = number of unordered vertex
# pairs at distance > D (unreachable pairs count). Moves:
#   * greedy fill: add an edge between spare-capacity vertices on opposite sides;
#   * rewire: move one end of an edge to another vertex on the same side;
#   * insert: when cost is 0, add a new A-B vertex pair attached to spare vertices.
# Rewires are accepted by simulated annealing. A stagnating search restores the
# last valid graph and tries a different insertion.
# Output: the largest valid graph seen, as "n m" followed by m edge lines.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 4096
#define MAXD 64
#define MAXE (MAXN * MAXD / 2)

static int N, DEGMAX, DIAM;
static int adjn[MAXN];
static int adj[MAXN][MAXD];
static int side[MAXN];
static uint64_t rs = 88172645463325252ULL;
static int distq[MAXN], que[MAXN];

static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int n) { return (int)(rnd() % (uint64_t)n); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int has_arc(int u, int v) {
    for (int i = 0; i < adjn[u]; i++) if (adj[u][i] == v) return 1;
    return 0;
}
static void del_arc(int u, int v) {
    for (int i = 0; i < adjn[u]; i++) if (adj[u][i] == v) { adj[u][i] = adj[u][--adjn[u]]; return; }
}
static void add_edge(int u, int v) { adj[u][adjn[u]++] = v; adj[v][adjn[v]++] = u; }
static void del_edge(int u, int v) { del_arc(u, v); del_arc(v, u); }

/* Number of unordered pairs at distance > DIAM (or unreachable). */
static long long bad_pairs(void) {
    long long total = 0;
    for (int s = 0; s < N; s++) {
        for (int i = 0; i < N; i++) distq[i] = -1;
        int h = 0, t = 0, reached = 1;
        que[t++] = s;
        distq[s] = 0;
        while (h < t) {
            int u = que[h++];
            if (distq[u] >= DIAM) continue;
            for (int i = 0; i < adjn[u]; i++) {
                int v = adj[u][i];
                if (distq[v] < 0) { distq[v] = distq[u] + 1; que[t++] = v; reached++; }
            }
        }
        total += N - reached;
    }
    return total / 2;
}

static int snapN = 0, snapM = 0;
static int su[MAXE], sv[MAXE];
static int have_valid = 0;

static void take_snapshot(void) {
    snapN = N;
    snapM = 0;
    for (int u = 0; u < N; u++)
        for (int i = 0; i < adjn[u]; i++) {
            int v = adj[u][i];
            if (u < v && snapM < MAXE) { su[snapM] = u; sv[snapM] = v; snapM++; }
        }
    have_valid = 1;
}

static void load_snapshot(void) {
    N = snapN;
    for (int u = 0; u < N; u++) adjn[u] = 0;
    for (int e = 0; e < snapM; e++) add_edge(su[e], sv[e]);
}

/* Insert a new side-0 vertex x and side-1 vertex y joined by an edge, then attach
   each to random spare vertices of the opposite side. */
static void insert_pair(int att) {
    int x = N, y = N + 1;
    side[x] = 0;
    side[y] = 1;
    adjn[x] = 0;
    adjn[y] = 0;
    int old = N;
    N += 2;
    add_edge(x, y);
    static int C0[MAXN], C1[MAXN];
    int n0 = 0, n1 = 0;
    for (int u = 0; u < old; u++) {
        if (adjn[u] >= DEGMAX) continue;
        if (side[u] == 1) C1[n1++] = u; else C0[n0++] = u;
    }
    for (int i = n1 - 1; i > 0; i--) { int j = rint_(i + 1); int t = C1[i]; C1[i] = C1[j]; C1[j] = t; }
    for (int i = n0 - 1; i > 0; i--) { int j = rint_(i + 1); int t = C0[i]; C0[i] = C0[j]; C0[j] = t; }
    int k1 = n1 < att ? n1 : att;
    int k0 = n0 < att ? n0 : att;
    for (int i = 0; i < k1; i++) add_edge(x, C1[i]);
    for (int i = 0; i < k0; i++) add_edge(y, C0[i]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    DEGMAX = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    rs = strtoull(argv[3], NULL, 10) * 2654435761ULL + 88172645463325252ULL;
    if (rs == 0) rs = 1;
    double tl = atof(argv[4]);
    if (DEGMAX < 1) DEGMAX = 1;
    if (DEGMAX > MAXD) DEGMAX = MAXD;

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) { printf("0 0\n"); return 0; }
    if (n <= 0 || n > MAXN - 2) { printf("0 0\n"); return 0; }
    N = n;
    for (int u = 0; u < N; u++) adjn[u] = 0;
    for (int e = 0; e < m; e++) {
        int a, b;
        if (scanf("%d %d", &a, &b) != 2) break;
        if (a < 0 || b < 0 || a >= N || b >= N || a == b) continue;
        if (has_arc(a, b) || adjn[a] >= DEGMAX || adjn[b] >= DEGMAX) continue;
        add_edge(a, b);
    }

    /* Bipartition by BFS colouring. */
    for (int i = 0; i < N; i++) side[i] = -1;
    for (int s = 0; s < N; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int h = 0, t = 0;
        que[t++] = s;
        while (h < t) {
            int u = que[h++];
            for (int i = 0; i < adjn[u]; i++) {
                int v = adj[u][i];
                if (side[v] < 0) { side[v] = 1 - side[u]; que[t++] = v; }
            }
        }
    }

    clock_t c0 = clock();
    const double T = 0.8;
    const int STAG = 4000;
    long long cur = bad_pairs();
    if (cur == 0) take_snapshot();
    long long since = 0;

    while (1) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (el >= tl) break;

        /* Greedy fill: add one edge between spare vertices on opposite sides. */
        {
            static int A[MAXN], B[MAXN];
            int na = 0, nb = 0;
            for (int u = 0; u < N; u++) {
                if (adjn[u] >= DEGMAX) continue;
                if (side[u] == 0) A[na++] = u; else B[nb++] = u;
            }
            int added = 0;
            for (int tr = 0; tr < 30 && na > 0 && nb > 0 && !added; tr++) {
                int a = A[rint_(na)], b = B[rint_(nb)];
                if (has_arc(a, b)) continue;
                add_edge(a, b);
                added = 1;
            }
            if (added) cur = bad_pairs();
        }

        if (cur == 0) {
            if (!have_valid || N > snapN) take_snapshot();
            if (N + 2 <= MAXN) {
                int att = DEGMAX - 1 - rint_(3);
                if (att < 1) att = 1;
                insert_pair(att);
                cur = bad_pairs();
                since = 0;
            }
            continue;
        }

        /* Annealing rewire: move one endpoint of an edge within its side. */
        for (int tr = 0; tr < 30; tr++) {
            int u = rint_(N);
            if (adjn[u] == 0) continue;
            int v = adj[u][rint_(adjn[u])];
            int w = rint_(N);
            if (w == v || w == u || side[w] != side[v] || adjn[w] >= DEGMAX || has_arc(u, w)) continue;
            del_edge(u, v);
            add_edge(u, w);
            long long nb = bad_pairs();
            long long delta = nb - cur;
            if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
                cur = nb;
            } else {
                del_edge(u, w);
                add_edge(u, v);
            }
            break;
        }
        since++;

        if (since > STAG && have_valid) {
            load_snapshot();
            cur = 0;
            since = 0;
        }
    }

    if (!have_valid) { printf("0 0\n"); return 0; }
    printf("%d %d\n", snapN, snapM);
    for (int e = 0; e < snapM; e++) printf("%d %d\n", su[e], sv[e]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q). Old vertices have degree q+1, so
# with spare s = d - q - 1, choose a point set S such that every line meets S
# in at most s points and every point lies on at most s lines through S. Add an
# A-vertex per P in S (joined to the lines through P) and a B-vertex per j in S
# (joined to the points on line j). Diameter stays 3.
# ----------------------------------------------------------------------------

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
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
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


def _arc_candidates(d, rng, deadline):
    """Return a list of (n, edges) arc-extended graphs, one per prime power q with q + 1 < d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q) or time.monotonic() > deadline:
            continue
        s = d - q - 1
        if s < 1:
            continue
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        cands = [_greedy_arc(m, s, point_lines, line_points, rng, 40, deadline)]
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len)
        if not S or not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


# ----------------------------------------------------------------------------
# Generalized quadrangle baseline (D = 4).
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


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _has_spare(n, edges, d):
    """True if some vertex has degree below d."""
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
    return any(x < d for x in deg)


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    end = t0 + time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        for n_c, e_c in _arc_candidates(d, rng, t0 + 0.2 * time_limit):
            consider(n_c, e_c)

    if D >= 4 and time.monotonic() < t0 + 0.2 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # C local search with vertex insertion, started from the best construction.
    elapsed = time.monotonic() - t0
    spend = 0.8 * time_limit - elapsed - 0.5
    if spend > 1.0 and _has_spare(best[0], best[1], d):
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{spend:.2f}"],
                            stdin_graph=best,
                            timeout=max(1.0, 0.9 * time_limit - (time.monotonic() - t0)))
            n2, e2 = lib.parse_graph_text(out)
            consider(n2, e2)
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
