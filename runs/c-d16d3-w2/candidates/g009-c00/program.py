import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing on bipartite graphs for diameter 3.
#
# The graph keeps its colour classes. A move is a degree-preserving double edge
# swap (a,b),(a2,b2) -> (a,b2),(a2,b) between two vertices on the same side.
# Cost = number of vertex pairs violating the distance bound: same-side pairs
# must be within distance 2, opposite-side pairs within distance 3. Cost 0 means
# the graph is valid. The engine repeatedly adds one vertex to the best valid
# graph, greedily fills its spare degree, and anneals until the cost reaches 0.
# It outputs the largest valid graph it reached.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1024
#define MAXD 32
#define MAXW (MAXN / 64)
#define MAXE (MAXN * MAXD / 2)
#define LEVEL_ITERS 8000

static int n, d;
static int deg[MAXN];
static int adj[MAXN][MAXD];
static int col[MAXN];
static uint64_t B1[MAXN][MAXW], B2[MAXN][MAXW], B3[MAXN][MAXW];
static uint64_t sidem[2][MAXW];
static uint64_t rs = 88172645463325252ULL;
static double endc;

static int bn, bm;
static int bcol[MAXN];
static int bu[MAXE], bv[MAXE];

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndi(int k) { return (int)(rnd64() % (uint64_t)k); }

static double rndu(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int isadj(int u, int v) {
    for (int i = 0; i < deg[u]; i++) if (adj[u][i] == v) return 1;
    return 0;
}

static void addE(int u, int v) {
    adj[u][deg[u]++] = v;
    adj[v][deg[v]++] = u;
}

static void repl(int u, int old, int nw) {
    for (int i = 0; i < deg[u]; i++) {
        if (adj[u][i] == old) { adj[u][i] = nw; return; }
    }
}

/* (a,b),(a2,b2) -> (a,b2),(a2,b). Undo with swap2(a,b2,a2,b). */
static void swap2(int a, int b, int a2, int b2) {
    repl(a, b, b2);
    repl(b2, a2, a);
    repl(a2, b2, b);
    repl(b, a, a2);
}

static long cost(void) {
    int W = (n + 63) >> 6;
    for (int s = 0; s < 2; s++)
        for (int w = 0; w < W; w++) sidem[s][w] = 0;
    for (int v = 0; v < n; v++)
        sidem[col[v]][v >> 6] |= 1ULL << (v & 63);
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) B1[v][w] = 0;
        B1[v][v >> 6] |= 1ULL << (v & 63);
        for (int i = 0; i < deg[v]; i++) {
            int u = adj[v][i];
            B1[v][u >> 6] |= 1ULL << (u & 63);
        }
    }
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) B2[v][w] = B1[v][w];
        for (int i = 0; i < deg[v]; i++) {
            int u = adj[v][i];
            for (int w = 0; w < W; w++) B2[v][w] |= B1[u][w];
        }
    }
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) B3[v][w] = B2[v][w];
        for (int i = 0; i < deg[v]; i++) {
            int u = adj[v][i];
            for (int w = 0; w < W; w++) B3[v][w] |= B2[u][w];
        }
    }
    long c = 0;
    for (int v = 0; v < n; v++) {
        int s = col[v], o = 1 - s;
        for (int w = 0; w < W; w++)
            c += popc(sidem[s][w] & ~B2[v][w]) + popc(sidem[o][w] & ~B3[v][w]);
    }
    return c / 2;
}

static void add_vertex(int side) {
    int w = n++;
    col[w] = side;
    deg[w] = 0;
    int cand[MAXN], nc = 0;
    for (int u = 0; u < w; u++)
        if (col[u] != side && deg[u] < d) cand[nc++] = u;
    for (int i = nc - 1; i > 0; i--) {
        int j = rndi(i + 1);
        int t = cand[i]; cand[i] = cand[j]; cand[j] = t;
    }
    for (int i = 0; i < nc && deg[w] < d; i++) {
        int u = cand[i];
        if (deg[u] < d) addE(u, w);
    }
}

static void fill_all(void) {
    for (int u = 0; u < n; u++) {
        if (deg[u] >= d) continue;
        for (int v = u + 1; v < n && deg[u] < d; v++)
            if (col[v] != col[u] && deg[v] < d && !isadj(u, v)) addE(u, v);
    }
}

static void save_best(void) {
    bn = n;
    bm = 0;
    for (int u = 0; u < n; u++) {
        bcol[u] = col[u];
        for (int i = 0; i < deg[u]; i++) {
            if (adj[u][i] > u && bm < MAXE) {
                bu[bm] = u;
                bv[bm] = adj[u][i];
                bm++;
            }
        }
    }
}

static void load_best(void) {
    n = bn;
    for (int v = 0; v < n; v++) {
        deg[v] = 0;
        col[v] = bcol[v];
    }
    for (int i = 0; i < bm; i++) addE(bu[i], bv[i]);
}

static int anneal(long iters, double T0) {
    long c = cost();
    for (long it = 0; it < iters && c > 0; it++) {
        if ((it & 127) == 0 && (double)clock() > endc) break;
        double T = T0 * (1.0 - (double)it / (double)iters) + 0.03;
        int a = rndi(n);
        if (deg[a] == 0) continue;
        int a2 = -1;
        for (int t = 0; t < 8; t++) {
            int x = rndi(n);
            if (x != a && col[x] == col[a] && deg[x] > 0) { a2 = x; break; }
        }
        if (a2 < 0) continue;
        int b = adj[a][rndi(deg[a])];
        int b2 = adj[a2][rndi(deg[a2])];
        if (b == b2 || isadj(a, b2) || isadj(a2, b)) continue;
        swap2(a, b, a2, b2);
        long c2 = cost();
        if (c2 <= c || rndu() < exp(-(double)(c2 - c) / T)) {
            c = c2;
        } else {
            swap2(a, b2, a2, b);
        }
    }
    return c == 0;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    int D = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 10; i++) rnd64();

    int N0, M0;
    if (scanf("%d %d", &N0, &M0) != 2 || d < 1 || d > MAXD || D != 3 ||
        N0 < 1 || N0 >= MAXN - 2) {
        printf("0 0\n");
        return 0;
    }
    n = N0;
    for (int i = 0; i < n; i++) deg[i] = 0;
    for (int i = 0; i < M0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) continue;
        if (deg[u] >= d || deg[v] >= d || isadj(u, v)) continue;
        addE(u, v);
    }

    for (int i = 0; i < n; i++) col[i] = -1;
    static int q[MAXN];
    for (int s = 0; s < n; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int h = 0, t = 0;
        q[t++] = s;
        while (h < t) {
            int u = q[h++];
            for (int i = 0; i < deg[u]; i++) {
                int v = adj[u][i];
                if (col[v] < 0) {
                    col[v] = 1 - col[u];
                    q[t++] = v;
                } else if (col[v] == col[u]) {
                    printf("0 0\n");
                    return 0;
                }
            }
        }
    }

    endc = (double)clock() + budget * CLOCKS_PER_SEC;

    if (cost() == 0) save_best();
    else if (anneal(20000, 1.0)) save_best();
    if (bn == 0) {
        printf("0 0\n");
        return 0;
    }

    int fails = 0;
    while ((double)clock() < endc && fails < 400 && bn < MAXN - 2) {
        load_best();
        add_vertex(rndi(2));
        fill_all();
        if (anneal(LEVEL_ITERS, 0.9)) {
            save_best();
            fails = 0;
        } else {
            fails++;
        }
    }

    printf("%d %d\n", bn, bm);
    for (int i = 0; i < bm; i++) printf("%d %d\n", bu[i], bv[i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from PG(2, q) incidence (points 0..m-1, lines m..2m-1). Each old vertex
# has degree q+1, so spare s = d - q - 1. New A-vertices (side of points) are
# attached to the full pencil of lines through a chosen point; new B-vertices
# are attached to the full set of points on a chosen line. Each line may take
# at most s new A-attachments, and each point at most s new B-attachments.
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
    """Randomized greedy choice of elements so that every target is hit <= s times."""
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
# Driver. The arc constructions give the starting graph. For D = 3 and d >= 6,
# the C annealer then tries to add vertices one at a time while keeping the
# graph valid. Every candidate is checked with lib.is_valid before it is kept.
# ----------------------------------------------------------------------------

def _c_anneal(graph, d, seed, budget):
    """Run the C annealer on graph (n, edges); return (n, edges) or None on any failure."""
    if graph is None or budget < 1.0:
        return None
    try:
        out = lib.run_c(C_SOURCE, [d, 3, seed, round(budget, 2)],
                        stdin_graph=(graph[0], graph[1]), timeout=budget + 6.0)
        n2, e2 = lib.parse_graph_text(out)
    except Exception:
        return None
    if n2 < 1:
        return None
    return n2, e2


def build(d, D, seed, time_limit):
    start = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def elapsed():
        return time.monotonic() - start

    def consider(g):
        nonlocal best
        if g is None:
            return
        n, e = g
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        arcs = _arc_extensions(d, start + 0.10 * time_limit,
                               random.Random(seed * 7919 + d))
        arcs.sort(key=lambda t: -t[0])
        for g in arcs:
            consider(g)

    if D == 3 and d >= 6:
        budget = 0.80 * time_limit - elapsed() - 3.0
        if budget >= 2.0:
            consider(_c_anneal(best, d, seed, budget))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
