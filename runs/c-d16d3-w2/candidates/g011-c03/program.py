import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing over edge swaps on a FIXED vertex set.
#
# Input: a bipartite start graph plus `extra` new vertices, each joined to
# spare vertices of the opposite side. The cost is the number of unordered
# vertex pairs at distance > D (computed with radius-D bitsets). Moves:
#   - add a cross edge between two spare vertices (never increases cost),
#   - 2-swap a-b, c-d -> a-d, c-b (preserves all degrees and bipartiteness).
# The engine stops at cost 0 and prints that graph, or "0 0" on failure.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>

#define MAXN 1024
#define MAXD 40
#define MAXW (MAXN / 64)

static int n, d, D, W;
static int deg[MAXN];
static int adj[MAXN][MAXD];
static int col[MAXN];
static uint64_t RB[2][MAXN][MAXW];
static uint64_t rs = 88172645463325252ULL;
static int sn;
static int su[MAXN * MAXD], sv[MAXN * MAXD];
static int sm;

static uint32_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return (uint32_t)(rs >> 16);
}

static double urand(void) {
    return (rnd() & 0xFFFFFF) / 16777216.0;
}

static int popc(uint64_t x) {
    int c = 0;
    while (x) { x &= x - 1; c++; }
    return c;
}

static int has_edge(int u, int v) {
    for (int i = 0; i < deg[u]; i++) if (adj[u][i] == v) return 1;
    return 0;
}

static void add_edge(int u, int v) {
    adj[u][deg[u]++] = v;
    adj[v][deg[v]++] = u;
}

static void drop(int u, int v) {
    for (int i = 0; i < deg[u]; i++) {
        if (adj[u][i] == v) {
            adj[u][i] = adj[u][--deg[u]];
            break;
        }
    }
}

static void del_edge(int u, int v) {
    drop(u, v);
    drop(v, u);
}

/* Number of unordered pairs at distance > D. */
static long bad_pairs(void) {
    W = (n + 63) >> 6;
    int cur = 0;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) RB[0][v][w] = 0;
        RB[0][v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < D; r++) {
        int nx = 1 - cur;
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < W; w++) RB[nx][v][w] = RB[cur][v][w];
            for (int i = 0; i < deg[v]; i++) {
                int u = adj[v][i];
                for (int w = 0; w < W; w++) RB[nx][v][w] |= RB[cur][u][w];
            }
        }
        cur = nx;
    }
    long tot = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(RB[cur][v][w]);
        tot += n - c;
    }
    return tot / 2;
}

static void snapshot(void) {
    sn = n;
    sm = 0;
    for (int u = 0; u < n; u++)
        for (int i = 0; i < deg[u]; i++)
            if (adj[u][i] > u) {
                su[sm] = u;
                sv[sm] = adj[u][i];
                sm++;
            }
}

int main(int argc, char **argv) {
    if (argc < 6) { printf("0 0\n"); return 0; }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    int extra = atoi(argv[5]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXD || D < 2 || extra < 0) { printf("0 0\n"); return 0; }

    int N0, M0;
    if (scanf("%d %d", &N0, &M0) != 2) { printf("0 0\n"); return 0; }
    if (N0 < 1 || N0 + extra > MAXN) { printf("0 0\n"); return 0; }
    n = N0;
    for (int i = 0; i < M0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) continue;
        if (deg[u] >= d || deg[v] >= d || has_edge(u, v)) continue;
        add_edge(u, v);
    }

    static int qu[MAXN];
    for (int s = 0; s < n; s++) col[s] = -1;
    int bip = 1;
    for (int s = 0; s < n; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int h = 0, t = 0;
        qu[t++] = s;
        while (h < t) {
            int u = qu[h++];
            for (int i = 0; i < deg[u]; i++) {
                int v = adj[u][i];
                if (col[v] < 0) {
                    col[v] = 1 - col[u];
                    qu[t++] = v;
                } else if (col[v] == col[u]) {
                    bip = 0;
                }
            }
        }
    }
    if (!bip) { printf("0 0\n"); return 0; }

    for (int k = 0; k < extra; k++) {
        int s = (int)(rnd() & 1u);
        int w = n++;
        deg[w] = 0;
        col[w] = s;
        static int cand[MAXN];
        int nc = 0;
        for (int u = 0; u < w; u++)
            if (col[u] == 1 - s && deg[u] < d) cand[nc++] = u;
        for (int i = nc - 1; i > 0; i--) {
            int j = (int)(rnd() % (uint32_t)(i + 1));
            int t = cand[i]; cand[i] = cand[j]; cand[j] = t;
        }
        for (int i = 0; i < nc && deg[w] < d; i++) add_edge(cand[i], w);
    }

    snapshot();
    long cur = bad_pairs();
    long best = cur;
    const double T0 = 2.0;
    double T = T0;
    clock_t t0 = clock();
    long it = 0;

    while (cur > 0) {
        if ((it & 31) == 0) {
            double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
            if (el > budget) break;
            T = T0 * (1.0 - el / budget) + 0.05;
        }
        it++;

        if (urand() < 0.2) {
            int a = (int)(rnd() % (uint32_t)n);
            int b = (int)(rnd() % (uint32_t)n);
            if (col[a] == col[b] || deg[a] >= d || deg[b] >= d || has_edge(a, b)) continue;
            add_edge(a, b);
            cur = bad_pairs();
            if (cur < best) { best = cur; snapshot(); }
            continue;
        }

        int a = (int)(rnd() % (uint32_t)n);
        if (deg[a] == 0) continue;
        int b = adj[a][rnd() % (uint32_t)deg[a]];
        int c = (int)(rnd() % (uint32_t)n);
        if (c == a || col[c] != col[a] || deg[c] == 0) continue;
        int dd = adj[c][rnd() % (uint32_t)deg[c]];
        if (dd == b || has_edge(a, dd) || has_edge(c, b)) continue;

        del_edge(a, b);
        del_edge(c, dd);
        add_edge(a, dd);
        add_edge(c, b);
        long nc = bad_pairs();
        long delta = nc - cur;
        if (delta <= 0 || urand() < exp(-(double)delta / T)) {
            cur = nc;
            if (cur < best) { best = cur; snapshot(); }
        } else {
            del_edge(a, dd);
            del_edge(c, b);
            add_edge(a, b);
            add_edge(c, dd);
        }
    }

    if (best == 0) {
        printf("%d %d\n", sn, sm);
        for (int i = 0; i < sm; i++) printf("%d %d\n", su[i], sv[i]);
    } else {
        printf("0 0\n");
    }
    return 0;
}
"""


def _c_sa(graph, d, D, seed, budget, extra):
    """Run the C annealer on graph with `extra` new vertices; return (n, edges) or None."""
    if graph is None or budget < 0.5 or extra < 0 or graph[0] + extra > 1000 or d > 32:
        return None
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), extra],
                        stdin_graph=(graph[0], graph[1]), timeout=budget + 6.0)
        n2, e2 = lib.parse_graph_text(out)
    except Exception:
        return None
    if n2 < 1 or not e2:
        return None
    return n2, e2


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from PG(2, q) incidence (points 0..m-1, lines m..2m-1). Each old vertex
# has degree q+1, so spare s = d - q - 1. A-side vertices attach to lines
# through chosen points, B-side vertices attach to points on chosen lines.
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


def _loads_ok(S, s, m, nbr):
    """True if every target is hit by <= s elements of S."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomized greedy choice so that every target is hit <= s times."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        load = [0] * m
        S = []
        for x in order:
            if all(load[t] < s for t in nbr[x]):
                S.append(x)
                for t in nbr[x]:
                    load[t] += 1
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


def _arc_graph(m, edges, point_lines, line_points, SA, SB):
    """Old PG incidence plus one new A-vertex per SA point and one new B-vertex per SB line."""
    na, nb = len(SA), len(SB)
    n = 2 * m + na + nb
    E = list(edges)
    for t, P in enumerate(SA):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(SB):
        b = 2 * m + na + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _arc_extensions(d, deadline, rng):
    """Return (n, edges) candidates for each prime power q with q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)

        SA = _greedy_side(m, s, point_lines, rng, 40, deadline)
        SB = _greedy_side(m, s, line_points, rng, 40, deadline)
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if len(cs) > len(SA) and _loads_ok(cs, s, m, point_lines):
                SA = cs
            if len(cs) > len(SB) and _loads_ok(cs, s, m, line_points):
                SB = cs

        if not (_loads_ok(SA, s, m, point_lines) and _loads_ok(SB, s, m, line_points)):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, SA, SB))
    return out


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) incidence graph (diameter 4), used as a start for D >= 4.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q)."""
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


# ----------------------------------------------------------------------------
# Driver.
#   - Fallback: K_{d,d} (valid for every D >= 2).
#   - D >= 3: best arc-extended PG graph, then GQ for D >= 4 if it is larger.
#   - Then repeated C annealing rounds that add a few vertices and try to reach
#     diameter D by edge swaps. Every accepted graph is checked with lib.is_valid.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    end = start + 0.88 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    def consider(g):
        nonlocal best
        if g is None:
            return
        n, e = g
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        for g in _arc_extensions(d, start + 0.12 * time_limit,
                                 random.Random(seed * 7919 + d)):
            consider(g)

    if D >= 4 and time.monotonic() < start + 0.2 * time_limit:
        consider(_best_gq(d))

    if D >= 3:
        extras = [4, 2, 1]
        k = 0
        r = 0
        while r < 200:
            remaining = end - time.monotonic()
            if remaining < 1.0:
                break
            budget = min(remaining, max(3.0, 0.12 * time_limit))
            res = _c_sa(best, d, D, seed * 1009 + r, budget, extras[k % len(extras)])
            r += 1
            if res is not None and res[0] > best[0] and lib.is_valid(res[0], res[1], d, D):
                best = res
            else:
                k += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
