import itertools
import time

import lib


# ----------------------------------------------------------------------------
# C engine: deficiency-guided annealing with cover growth, kill/regrow, and pruning.
#
# State: a bipartite graph with max degree d. Cost = number of vertex pairs at
# distance > D, computed exactly with bitset balls. Moves:
#   * add a vertex on one side, joined to a greedy cover of the other side
#     (stealing an edge from a full neighbour when needed),
#   * fill: add cross-side edges between deficient vertices (never hurts),
#   * deficiency-guided double-edge switches (degrees and bipartition preserved);
#     the first endpoint is picked by a tournament on per-vertex bad-pair counts,
#     so switches concentrate on the vertices that are farthest from the rest,
#   * kill 1-2 vertices and regrow,
#   * prune redundant edges (keeping cost 0) to free degree for the next growth.
# Only cost-0 states are accepted as the current graph, so the output is valid.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 2048
#define MAXD 16
#define MAXW ((MAXN + 63) / 64)
#define ITERS 1200

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    int col[MAXN];
} Graph;

static Graph GCUR, GWORK, GBEST;
static uint64_t BUF[2][MAXN * MAXW];
static int defv[MAXN];
static int dd, DD;
static clock_t deadline;
static uint64_t rs = 0x9E3779B97F4A7C15ULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int m) { return (int)(rnd64() % (uint64_t)m); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static int timeup(void) { return clock() >= deadline; }

static int pop64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(const Graph *g, int a, int b) {
    for (int i = 0; i < g->deg[a]; i++) if (g->adj[a][i] == b) return 1;
    return 0;
}

static int add_edge(Graph *g, int a, int b) {
    if (a == b || g->deg[a] >= dd || g->deg[b] >= dd || has_edge(g, a, b)) return 0;
    g->adj[a][g->deg[a]++] = b;
    g->adj[b][g->deg[b]++] = a;
    return 1;
}

static void del_from(Graph *g, int a, int b) {
    for (int i = 0; i < g->deg[a]; i++) {
        if (g->adj[a][i] == b) {
            g->adj[a][i] = g->adj[a][--g->deg[a]];
            return;
        }
    }
}

static void del_edge(Graph *g, int a, int b) {
    del_from(g, a, b);
    del_from(g, b, a);
}

static int color_graph(Graph *g) {
    static int stack[MAXN];
    for (int v = 0; v < g->n; v++) g->col[v] = -1;
    for (int s = 0; s < g->n; s++) {
        if (g->col[s] != -1) continue;
        g->col[s] = 0;
        int sp = 0;
        stack[sp++] = s;
        while (sp > 0) {
            int u = stack[--sp];
            for (int i = 0; i < g->deg[u]; i++) {
                int v = g->adj[u][i];
                if (g->col[v] == -1) {
                    g->col[v] = 1 - g->col[u];
                    stack[sp++] = v;
                } else if (g->col[v] == g->col[u]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

/* Bitset balls of radius r; returns a pointer to n*W words (vertex v at v*W). */
static uint64_t *balls(const Graph *g, int r) {
    int n = g->n, W = (n + 63) >> 6;
    uint64_t *A = BUF[0], *B = BUF[1];
    memset(A, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++) A[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int s = 0; s < r; s++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = B + (size_t)v * W;
            const uint64_t *src = A + (size_t)v * W;
            for (int w = 0; w < W; w++) dst[w] = src[w];
            for (int i = 0; i < g->deg[v]; i++) {
                const uint64_t *nb = A + (size_t)g->adj[v][i] * W;
                for (int w = 0; w < W; w++) dst[w] |= nb[w];
            }
        }
        uint64_t *t = A;
        A = B;
        B = t;
    }
    return A;
}

/* Bad pairs at distance > DD (unreachable counts). Also fills defv[v] = bad pairs at v. */
static long cost(const Graph *g) {
    int n = g->n, W = (n + 63) >> 6;
    uint64_t *R = balls(g, DD);
    long tot = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        const uint64_t *row = R + (size_t)v * W;
        for (int w = 0; w < W; w++) c += pop64(row[w]);
        defv[v] = n - c;
        tot += n - c;
    }
    return tot / 2;
}

static void shuffle_int(int *a, int m) {
    for (int i = m - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = a[i];
        a[i] = a[j];
        a[j] = t;
    }
}

/* Add a vertex on side s joined to a greedy cover of the opposite side. */
static int add_vertex(Graph *g, int s) {
    int n = g->n;
    if (n + 1 > MAXN) return -1;
    int W = (n + 63) >> 6;
    uint64_t *B3 = balls(g, DD - 1);
    uint64_t U[MAXW];
    memset(U, 0, sizeof U);
    for (int v = 0; v < n; v++) U[v >> 6] |= 1ULL << (v & 63);
    static char used[MAXN];
    memset(used, 0, sizeof(char) * (size_t)n);
    int chosen[MAXD], nc = 0;
    for (int k = 0; k < dd; k++) {
        int bv = -1;
        double bs = -1e18;
        for (int u = 0; u < n; u++) {
            if (g->col[u] != 1 - s || used[u]) continue;
            int gain = 0;
            const uint64_t *row = B3 + (size_t)u * W;
            for (int w = 0; w < W; w++) gain += pop64(row[w] & U[w]);
            double sc = gain + 0.9 * rnd01();
            if (g->deg[u] >= dd) sc -= 1.5;
            if (sc > bs) {
                bs = sc;
                bv = u;
            }
        }
        if (bv < 0) break;
        used[bv] = 1;
        chosen[nc++] = bv;
        const uint64_t *row = B3 + (size_t)bv * W;
        for (int w = 0; w < W; w++) U[w] &= ~row[w];
    }
    int v = n;
    g->n = n + 1;
    g->deg[v] = 0;
    g->col[v] = s;
    for (int i = 0; i < nc; i++) {
        int u = chosen[i];
        if (g->deg[u] >= dd) {
            int t = g->adj[u][rndint(g->deg[u])];
            del_edge(g, u, t);
        }
        add_edge(g, u, v);
    }
    return v;
}

/* Add cross-side edges between deficient vertices (only shortens distances). */
static void fill(Graph *g) {
    static int L[MAXN], R[MAXN];
    int nl = 0, nr = 0;
    for (int v = 0; v < g->n; v++) {
        if (g->deg[v] >= dd) continue;
        if (g->col[v] == 0) L[nl++] = v;
        else R[nr++] = v;
    }
    shuffle_int(L, nl);
    shuffle_int(R, nr);
    for (int i = 0; i < nl; i++) {
        int a = L[i];
        for (int j = 0; j < nr; j++) {
            if (g->deg[a] >= dd) break;
            int b = R[j];
            if (g->deg[b] < dd && !has_edge(g, a, b)) add_edge(g, a, b);
        }
    }
}

static void remove_vertex(Graph *g, int x) {
    int last = g->n - 1;
    for (int i = 0; i < g->deg[x]; i++) del_from(g, g->adj[x][i], x);
    g->deg[x] = 0;
    if (x != last) {
        for (int i = 0; i < g->deg[last]; i++) {
            int z = g->adj[last][i];
            for (int j = 0; j < g->deg[z]; j++) {
                if (g->adj[z][j] == last) g->adj[z][j] = x;
            }
        }
        g->deg[x] = g->deg[last];
        for (int i = 0; i < g->deg[last]; i++) g->adj[x][i] = g->adj[last][i];
        g->col[x] = g->col[last];
    }
    g->deg[last] = 0;
    g->n = last;
}

/* Deficiency-guided bipartite double-edge switches minimising bad pairs. Returns final cost. */
static long anneal(Graph *g, int iters, double T0, double T1) {
    long cur = cost(g);
    static int side[MAXN];
    int ns = 0;
    for (int v = 0; v < g->n; v++) {
        if (g->col[v] == 0 && g->deg[v] > 0) side[ns++] = v;
    }
    if (ns == 0) return cur;
    for (int it = 0; it < iters && cur > 0; it++) {
        if ((it & 31) == 0 && timeup()) break;
        double T = T0 + (T1 - T0) * it / (double)iters;
        int a;
        if (rnd01() < 0.5) {
            a = side[rndint(ns)];
            for (int t = 0; t < 2; t++) {
                int c2 = side[rndint(ns)];
                if (defv[c2] > defv[a]) a = c2;
            }
        } else {
            a = side[rndint(ns)];
        }
        if (g->deg[a] == 0) continue;
        int b = g->adj[a][rndint(g->deg[a])];
        int c = side[rndint(ns)];
        if (c == a || g->deg[c] == 0) continue;
        int e = g->adj[c][rndint(g->deg[c])];
        if (has_edge(g, a, e) || has_edge(g, c, b)) continue;
        del_edge(g, a, b);
        del_edge(g, c, e);
        add_edge(g, a, e);
        add_edge(g, c, b);
        long nw = cost(g);
        if (nw <= cur || rnd01() < exp(-(double)(nw - cur) / T)) {
            cur = nw;
        } else {
            del_edge(g, a, e);
            del_edge(g, c, b);
            add_edge(g, a, b);
            add_edge(g, c, e);
        }
    }
    return cur;
}

/* Delete redundant edges (cost stays 0), up to a budget of tests. */
static void prune(Graph *g, int budget) {
    static int ea[MAXN * MAXD], eb[MAXN * MAXD], idx[MAXN * MAXD];
    int m = 0;
    for (int a = 0; a < g->n; a++) {
        for (int i = 0; i < g->deg[a]; i++) {
            int b = g->adj[a][i];
            if (a < b) {
                ea[m] = a;
                eb[m] = b;
                idx[m] = m;
                m++;
            }
        }
    }
    shuffle_int(idx, m);
    int tests = 0;
    for (int k = 0; k < m && tests < budget; k++) {
        if ((k & 15) == 0 && timeup()) break;
        int i = idx[k], a = ea[i], b = eb[i];
        if (!has_edge(g, a, b)) continue;
        tests++;
        del_edge(g, a, b);
        if (cost(g) != 0) add_edge(g, a, b);
    }
}

static int count_edges(const Graph *g) {
    int s = 0;
    for (int v = 0; v < g->n; v++) s += g->deg[v];
    return s / 2;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    dd = atoi(argv[1]);
    DD = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    if (dd < 1 || dd > MAXD || DD < 1) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)seed * 0x2545F4914F6CDD1DULL + 0x9E3779B9ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 16; i++) rnd64();
    deadline = clock() + (clock_t)(tl * CLOCKS_PER_SEC);

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN - 64 || m < 0) {
        printf("0 0\n");
        return 0;
    }
    memset(&GCUR, 0, sizeof GCUR);
    GCUR.n = n;
    int ok = 1;
    for (int i = 0; i < m && ok; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) {
            ok = 0;
            break;
        }
        if (u < 0 || v < 0 || u >= n || v >= n || !add_edge(&GCUR, u, v)) ok = 0;
    }
    if (!ok || !color_graph(&GCUR)) {
        printf("0 0\n");
        return 0;
    }

    int have_best = 0;
    if (cost(&GCUR) != 0) anneal(&GCUR, 20000, 0.8, 0.05);
    if (cost(&GCUR) == 0) {
        GBEST = GCUR;
        have_best = 1;
    }

    while (!timeup()) {
        GWORK = GCUR;
        if (rndint(4) == 0 && GWORK.n > 10) {
            int k = 1 + rndint(2);
            for (int j = 0; j < k; j++) remove_vertex(&GWORK, rndint(GWORK.n));
            fill(&GWORK);
        }
        int s = rndint(2);
        if (add_vertex(&GWORK, s) < 0) continue;
        fill(&GWORK);
        long c = anneal(&GWORK, ITERS, 0.7, 0.05);
        if (c == 0 && GWORK.n >= GCUR.n - 1) {
            prune(&GWORK, 100);
            GCUR = GWORK;
            if (!have_best || GCUR.n > GBEST.n) {
                GBEST = GCUR;
                have_best = 1;
            }
        }
        if (have_best && GCUR.n < GBEST.n - 2) GCUR = GBEST;
    }

    if (!have_best || cost(&GBEST) != 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", GBEST.n, count_edges(&GBEST));
    for (int a = 0; a < GBEST.n; a++) {
        for (int i = 0; i < GBEST.deg[a]; i++) {
            int b = GBEST.adj[a][i];
            if (a < b) printf("%d %d\n", a, b);
        }
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions: start graphs for the C engine.
# ----------------------------------------------------------------------------

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
    """Generalized quadrangle incidence graph W(q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q <= 9 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    base = None
    if D >= 4:
        base = _best_gq(d)
    if base is None and D >= 3:
        base = _best_pg(d)
    if base is not None:
        n0, e0 = base
        if n0 > best_n and lib.is_valid(n0, e0, d, D):
            best_n, best_e = n0, list(e0)

    if D < 2 or d > 16 or best_n > 1900 or best_n >= lib.moore_bound(d, D):
        return best_n, list(best_e)

    elapsed = time.monotonic() - t0
    budget = max(1.0, 0.85 * time_limit - elapsed - 1.5)
    timeout = max(2.0, 0.95 * time_limit - elapsed)
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                        stdin_graph=(best_n, best_e), timeout=timeout)
        n, e = lib.parse_graph_text(out)
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)
    except Exception:
        pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
