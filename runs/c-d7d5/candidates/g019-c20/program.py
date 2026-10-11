import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact baselines.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


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


# ----------------------------------------------------------------------------
# C engine.
#
# Phase 1: bi-Cayley search with breakout local search (clause weighting), as
# before. Vertices A_{i,g} = i*G+g, B_{j,h} = (K+j)*G+h, dart (l, i) joins
# A_{i,g} to B_{P[l][i], g*S[l][i]}.
#
# Phase 2 (new): splice-and-repair. Take the best valid graph G0 on n vertices
# (from phase 1, or from stdin). Pick a random edge x-y (x in side A, y in
# side B) and subdivide it by two new vertices a (side B) and b (side A):
# x-a, a-b, b-y. This gives n+2 vertices, with two vertices of spare degree.
# A simulated-annealing repair then looks for a graph with bad-pair count 0
# (degree <= d, bipartite, diameter <= D), using three moves:
#   * switch: degree-preserving double edge swap across the bipartition,
#   * deficit move: move one endpoint of an edge onto a vertex with spare degree,
#   * greedy fill: add any edge between non-adjacent spare-degree vertices on
#     opposite sides (adding an edge never increases the bad-pair count).
# The bad-pair count is computed with 64-bit bitset ball expansion. If the
# repair succeeds, the graph grows by two vertices and becomes the new base.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>

#define MAXD 64
#define MAXK 3
#define PEN 1000
#define POLISH_T 80
#define STUCK 50
#define BREAK_ITERS 25000
#define MAXV 4096
#define MAXW (MAXV / 64)
#define REPAIR_ITERS 800
#define REPAIR_T0 3.0
#define PHASE1_FRAC 0.6

typedef struct {
    int K, G;
    int P[MAXD][MAXK];
    int S[MAXD][MAXK];
} Cfg;

typedef struct {
    int n;
    int side[MAXV];
    int deg[MAXV];
    int nb[MAXV * MAXD];   /* flat, row v starts at v*Dd */
} Graph;

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rint_(int n) { return (int)(rnd() % (uint64_t)n); }

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int Dd = 3, DD = 3;
static int GM = 1, GK = 1, GG = 1;
static int gpow[64];
static double deadline = 0.0;

static void set_group(int m, int k, int r) {
    GM = m;
    GK = k;
    GG = m * k;
    long long p = 1 % m;
    for (int b = 0; b < k; b++) {
        gpow[b] = (int)p;
        p = (p * r) % m;
    }
}

static int gmul(int x, int y) {
    int a = x / GK, b = x % GK;
    int c = y / GK, d = y % GK;
    long long t = ((long long)a + (long long)gpow[b] * (long long)c) % GM;
    return (int)t * GK + (b + d) % GK;
}

static int cap = 0;
static int *g_adj = NULL, *g_cnt = NULL, *g_vis = NULL, *g_q = NULL;
static long long *g_w = NULL;
static int g_stamp = 0;
static long long g_rawcost = 0;
static int g_dup = 0;

static void ensure_cap(int N) {
    if (N <= cap) return;
    free(g_adj);
    free(g_cnt);
    free(g_vis);
    free(g_q);
    free(g_w);
    cap = N;
    g_adj = malloc(sizeof(int) * (size_t)N * (size_t)Dd);
    g_cnt = malloc(sizeof(int) * (size_t)N);
    g_vis = calloc((size_t)N, sizeof(int));
    g_q = malloc(sizeof(int) * (size_t)N);
    g_w = malloc(sizeof(long long) * (size_t)4 * (size_t)N);
    if (!g_adj || !g_cnt || !g_vis || !g_q || !g_w) {
        fprintf(stderr, "out of memory\n");
        exit(1);
    }
    g_stamp = 0;
}

static void reset_weights(int K, int N) {
    long long total = (long long)2 * K * N;
    for (long long j = 0; j < total; j++) g_w[j] = 1;
}

static long long cost_of(const Cfg *c, int bump) {
    int K = c->K, G = c->G, N = 2 * K * G;
    memset(g_cnt, 0, sizeof(int) * (size_t)N);
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) {
            int j = c->P[l][i], s = c->S[l][i];
            for (int g = 0; g < G; g++) {
                int a = i * G + g;
                int b = (K + j) * G + gmul(g, s);
                g_adj[a * Dd + g_cnt[a]++] = b;
                g_adj[b * Dd + g_cnt[b]++] = a;
            }
        }
    }
    int dup = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < Dd; l1++)
            for (int l2 = l1 + 1; l2 < Dd; l2++)
                if (c->P[l1][i] == c->P[l2][i] && c->S[l1][i] == c->S[l2][i])
                    dup++;

    long long wsum = 0, raw = 0;
    for (int r = 0; r < 2 * K; r++) {
        int src = r * G;
        g_stamp++;
        int head = 0, tail = 0;
        g_vis[src] = g_stamp;
        g_q[tail++] = src;
        for (int lvl = 0; lvl < DD; lvl++) {
            int end = tail;
            if (head == end) break;
            while (head < end) {
                int u = g_q[head++];
                for (int t = 0; t < Dd; t++) {
                    int v = g_adj[u * Dd + t];
                    if (g_vis[v] != g_stamp) {
                        g_vis[v] = g_stamp;
                        g_q[tail++] = v;
                    }
                }
            }
        }
        long long *w = g_w + (size_t)r * (size_t)N;
        for (int v = 0; v < N; v++) {
            if (g_vis[v] != g_stamp) {
                raw++;
                wsum += w[v];
                if (bump) w[v]++;
            }
        }
    }
    g_dup = dup;
    g_rawcost = raw + (long long)PEN * dup;
    return wsum + (long long)PEN * dup;
}

static void random_cfg(Cfg *c) {
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < c->K; i++) c->P[l][i] = i;
        for (int i = c->K - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = c->P[l][i];
            c->P[l][i] = c->P[l][j];
            c->P[l][j] = t;
        }
        for (int i = 0; i < c->K; i++) c->S[l][i] = rint_(GG);
    }
}

static long long breakout(Cfg *c, long iters) {
    long long wc = cost_of(c, 0);
    long long rc = g_rawcost;
    long long bestraw = rc;
    Cfg bc = *c;
    int stuck = 0;
    for (long t = 0; t < iters && wc != 0; t++) {
        if ((t & 127) == 0 && now_s() > deadline) break;
        int l = rint_(Dd);
        int i = rint_(c->K);
        int kind = (c->K >= 2 && rint_(4) == 0);
        int old_s = 0, i2 = 0;
        if (kind) {
            i2 = rint_(c->K - 1);
            if (i2 >= i) i2++;
            int tmp = c->P[l][i];
            c->P[l][i] = c->P[l][i2];
            c->P[l][i2] = tmp;
        } else {
            old_s = c->S[l][i];
            c->S[l][i] = rint_(GG);
        }
        long long wc2 = cost_of(c, 0);
        if (wc2 <= wc) {
            if (wc2 < wc) stuck = 0;
            else stuck++;
            wc = wc2;
            rc = g_rawcost;
            if (rc < bestraw) {
                bestraw = rc;
                bc = *c;
            }
        } else {
            if (kind) {
                int tmp = c->P[l][i];
                c->P[l][i] = c->P[l][i2];
                c->P[l][i2] = tmp;
            } else {
                c->S[l][i] = old_s;
            }
            stuck++;
        }
        if (stuck >= STUCK) {
            cost_of(c, 1);
            wc = cost_of(c, 0);
            rc = g_rawcost;
            stuck = 0;
        }
    }
    *c = bc;
    return bestraw;
}

static long long polish(Cfg *c) {
    long long cost = cost_of(c, 0);
    int improved = 1;
    while (improved && cost != 0) {
        improved = 0;
        for (int l = 0; l < Dd && cost != 0; l++) {
            for (int i = 0; i < c->K; i++) {
                if (now_s() > deadline) return cost;
                int old = c->S[l][i];
                int bestv = old;
                long long bestc = cost;
                for (int s = 0; s < GG; s++) {
                    if (s == old) continue;
                    c->S[l][i] = s;
                    long long c2 = cost_of(c, 0);
                    if (c2 < bestc) {
                        bestc = c2;
                        bestv = s;
                    }
                }
                c->S[l][i] = bestv;
                if (bestv != old) {
                    cost = bestc;
                    improved = 1;
                    if (cost == 0) break;
                }
            }
        }
    }
    return cost;
}

static long long gcdll(long long a, long long b) {
    while (b) {
        long long t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static long long powmod(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static const int KF[] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16,
                         18, 20, 21, 24, 27, 28, 30, 32, 36, 40};

static void sample_group(long long target, int *oM, int *oK, int *oR) {
    int nk = (int)(sizeof(KF) / sizeof(KF[0]));
    int k = KF[rint_(nk)];
    long long m = (target + k - 1) / k;
    if (m < 2) m = 2;
    int r = 1;
    if (k > 1 && m > 2) {
        for (int t = 0; t < 200; t++) {
            long long c = 2 + (long long)rint_((int)(m - 2));
            if (gcdll(c, m) == 1 && powmod(c, k, m) == 1 % m) {
                r = (int)c;
                break;
            }
        }
    }
    *oM = (int)m;
    *oK = k;
    *oR = r;
}

/* ------------------------------------------------------------------------ */
/* Phase 2: general bipartite graph, splice-and-repair.                      */
/* ------------------------------------------------------------------------ */

static uint64_t RA[MAXV * MAXW], RB[MAXV * MAXW];
static Graph GBEST, GWORK, GTRY, GIN, GTMP;
static int DEFV[MAXV], LAV[MAXV], LBV[MAXV], QV[MAXV];

static int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Number of ordered vertex pairs at distance > DD (0 iff valid). */
static long long bad_count(const Graph *g) {
    int n = g->n;
    int W = (n + 63) >> 6;
    size_t words = (size_t)n * (size_t)W;
    uint64_t *R = RA, *T = RB;
    memset(R, 0, sizeof(uint64_t) * words);
    for (int v = 0; v < n; v++)
        R[(size_t)v * W + (size_t)(v >> 6)] |= 1ULL << (v & 63);
    for (int it = 0; it < DD; it++) {
        memcpy(T, R, sizeof(uint64_t) * words);
        for (int v = 0; v < n; v++) {
            uint64_t *tv = T + (size_t)v * W;
            const int *row = g->nb + v * Dd;
            for (int k = 0; k < g->deg[v]; k++) {
                const uint64_t *ru = R + (size_t)row[k] * W;
                for (int w = 0; w < W; w++) tv[w] |= ru[w];
            }
        }
        uint64_t *tmp = R;
        R = T;
        T = tmp;
    }
    long long bad = 0;
    for (int v = 0; v < n; v++) {
        const uint64_t *rv = R + (size_t)v * W;
        int c = 0;
        for (int w = 0; w < W; w++) c += popc64(rv[w]);
        bad += n - c;
    }
    return bad;
}

static int g_has(const Graph *g, int x, int y) {
    const int *row = g->nb + x * Dd;
    for (int k = 0; k < g->deg[x]; k++)
        if (row[k] == y) return 1;
    return 0;
}

static void g_unlink(Graph *g, int x, int y) {
    int *row = g->nb + x * Dd;
    for (int k = 0; k < g->deg[x]; k++) {
        if (row[k] == y) {
            row[k] = row[g->deg[x] - 1];
            g->deg[x]--;
            return;
        }
    }
}

static void g_link(Graph *g, int x, int y) {
    g->nb[x * Dd + g->deg[x]++] = y;
    g->nb[y * Dd + g->deg[y]++] = x;
}

static void g_cut(Graph *g, int x, int y) {
    g_unlink(g, x, y);
    g_unlink(g, y, x);
}

static void g_copy(Graph *dst, const Graph *src) {
    dst->n = src->n;
    memcpy(dst->side, src->side, sizeof(int) * (size_t)src->n);
    memcpy(dst->deg, src->deg, sizeof(int) * (size_t)src->n);
    memcpy(dst->nb, src->nb, sizeof(int) * (size_t)src->n * (size_t)Dd);
}

/* Sets side[] by BFS 2-colouring; returns 1 if the graph is bipartite. */
static int g_colour(Graph *g) {
    int n = g->n;
    for (int v = 0; v < n; v++) g->side[v] = -1;
    for (int s = 0; s < n; s++) {
        if (g->side[s] != -1) continue;
        g->side[s] = 0;
        int head = 0, tail = 0;
        QV[tail++] = s;
        while (head < tail) {
            int u = QV[head++];
            for (int k = 0; k < g->deg[u]; k++) {
                int v = g->nb[u * Dd + k];
                if (g->side[v] == -1) {
                    g->side[v] = 1 - g->side[u];
                    QV[tail++] = v;
                } else if (g->side[v] == g->side[u]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

/* Reads "n m" and m edges from stdin; returns 1 if a simple, bounded-degree, bipartite graph was read. */
static int read_stdin_graph(Graph *g) {
    long long n, m;
    if (scanf("%lld %lld", &n, &m) != 2) return 0;
    if (n <= 0 || n > MAXV || m < 0) return 0;
    g->n = (int)n;
    for (int v = 0; v < g->n; v++) g->deg[v] = 0;
    for (long long i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return 0;
        if (u < 0 || u >= g->n || v < 0 || v >= g->n || u == v) return 0;
        if (g->deg[u] >= Dd || g->deg[v] >= Dd) return 0;
        if (g_has(g, u, v)) return 0;
        g_link(g, u, v);
    }
    return g_colour(g);
}

static void cfg_to_graph(const Cfg *c, Graph *g) {
    int K = c->K, G = c->G, n = 2 * K * G;
    g->n = n;
    for (int v = 0; v < n; v++) {
        g->deg[v] = 0;
        g->side[v] = (v < K * G) ? 0 : 1;
    }
    for (int l = 0; l < Dd; l++)
        for (int i = 0; i < K; i++) {
            int j = c->P[l][i], s = c->S[l][i];
            for (int gg = 0; gg < G; gg++) {
                int u = i * G + gg;
                int v = (K + j) * G + gmul(gg, s);
                if (g->deg[u] < Dd && g->deg[v] < Dd) g_link(g, u, v);
            }
        }
}

static void build_kdd(Graph *g) {
    int d = Dd;
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) {
        g->deg[v] = 0;
        g->side[v] = (v < d) ? 0 : 1;
    }
    for (int i = 0; i < d; i++)
        for (int j = 0; j < d; j++) g_link(g, i, d + j);
}

/* Add every possible edge between spare-degree vertices on opposite sides. */
static void greedy_fill(Graph *g) {
    int na = 0, nbq = 0;
    for (int v = 0; v < g->n; v++) {
        if (g->deg[v] < Dd) {
            if (g->side[v] == 0) LAV[na++] = v;
            else LBV[nbq++] = v;
        }
    }
    for (int i = 0; i < na; i++) {
        int x = LAV[i];
        for (int j = 0; j < nbq && g->deg[x] < Dd; j++) {
            int y = LBV[j];
            if (g->deg[y] >= Dd || g_has(g, x, y)) continue;
            g_link(g, x, y);
        }
    }
}

/* Degree-preserving double edge swap across the bipartition. */
static int switch_move(Graph *g) {
    for (int tries = 0; tries < 30; tries++) {
        int x1 = rint_(g->n);
        if (g->deg[x1] == 0) continue;
        int x2 = rint_(g->n);
        if (x2 == x1 || g->side[x2] != g->side[x1] || g->deg[x2] == 0) continue;
        int y1 = g->nb[x1 * Dd + rint_(g->deg[x1])];
        int y2 = g->nb[x2 * Dd + rint_(g->deg[x2])];
        if (y1 == y2 || g_has(g, x1, y2) || g_has(g, x2, y1)) continue;
        g_cut(g, x1, y1);
        g_cut(g, x2, y2);
        g_link(g, x1, y2);
        g_link(g, x2, y1);
        return 1;
    }
    return 0;
}

/* Move one endpoint of an edge onto a spare-degree vertex z (keeps the other end x). */
static int move_deficit(Graph *g) {
    int nd = 0;
    for (int v = 0; v < g->n; v++)
        if (g->deg[v] < Dd) DEFV[nd++] = v;
    if (nd == 0) return 0;
    for (int tries = 0; tries < 30; tries++) {
        int z = DEFV[rint_(nd)];
        int want = 1 - g->side[z];
        int x = rint_(g->n);
        if (g->side[x] != want || g->deg[x] == 0 || g_has(g, x, z)) continue;
        int y = g->nb[x * Dd + rint_(g->deg[x])];
        if (y == z) continue;
        g_cut(g, x, y);
        g_link(g, x, z);
        return 1;
    }
    return 0;
}

/* Subdivide a random edge (x in A, y in B) by two new vertices a (B) and b (A). */
static int splice(Graph *g) {
    if (g->n + 2 > MAXV || g->n < 2) return 0;
    int x = -1;
    for (int tries = 0; tries < 100000; tries++) {
        int c = rint_(g->n);
        if (g->side[c] == 0 && g->deg[c] > 0) {
            x = c;
            break;
        }
    }
    if (x < 0) return 0;
    int y = g->nb[x * Dd + rint_(g->deg[x])];
    int a = g->n, b = g->n + 1;
    g->side[a] = 1;
    g->deg[a] = 0;
    g->side[b] = 0;
    g->deg[b] = 0;
    g->n += 2;
    g_cut(g, x, y);
    g_link(g, x, a);
    g_link(g, a, b);
    g_link(g, b, y);
    return 1;
}

/* Simulated-annealing repair. Returns 1 if cur becomes valid (bad_count 0). */
static int repair(Graph *cur, int iters) {
    long long c = bad_count(cur);
    for (int t = 0; t < iters && c > 0; t++) {
        if ((t & 63) == 0 && now_s() > deadline) break;
        g_copy(&GTRY, cur);
        int moved;
        if (rint_(2) == 0) moved = switch_move(&GTRY);
        else moved = move_deficit(&GTRY);
        if (!moved) continue;
        greedy_fill(&GTRY);
        long long c2 = bad_count(&GTRY);
        int accept = (c2 <= c);
        if (!accept) {
            double T = REPAIR_T0 * (1.0 - (double)t / (double)iters) + 1e-9;
            double p = exp(-(double)(c2 - c) / T);
            accept = (rnd() % 1000000ULL) < (uint64_t)(p * 1000000.0);
        }
        if (accept) {
            g_copy(cur, &GTRY);
            c = c2;
        }
    }
    return c == 0;
}

static void phase2(void) {
    while (now_s() < deadline) {
        if (GBEST.n + 2 > MAXV) break;
        g_copy(&GWORK, &GBEST);
        if (!splice(&GWORK)) break;
        greedy_fill(&GWORK);
        if (repair(&GWORK, REPAIR_ITERS)) {
            g_copy(&GBEST, &GWORK);
        }
    }
}

static void print_graph(const Graph *g) {
    long long m = 0;
    for (int v = 0; v < g->n; v++) m += g->deg[v];
    m /= 2;
    printf("%d %lld\n", g->n, m);
    for (int v = 0; v < g->n; v++) {
        if (g->side[v] != 0) continue;
        for (int k = 0; k < g->deg[v]; k++)
            printf("%d %d\n", v, g->nb[v * Dd + k]);
    }
}

int main(int argc, char **argv) {
    Dd = argc > 1 ? atoi(argv[1]) : 3;
    DD = argc > 2 ? atoi(argv[2]) : 3;
    unsigned long long seed = argc > 3 ? strtoull(argv[3], NULL, 10) : 1ULL;
    double tl = argc > 4 ? atof(argv[4]) : 10.0;
    int min_n = argc > 5 ? atoi(argv[5]) : 0;

    if (Dd < 1 || Dd > MAXD || DD < 1) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 4; w++) rnd();

    double t0 = now_s();

    int have_best = 0;
    if (read_stdin_graph(&GIN) && bad_count(&GIN) == 0) {
        g_copy(&GBEST, &GIN);
        have_best = 1;
    }

    /* Phase 1: symmetric bi-Cayley search, must beat the best known order. */
    deadline = t0 + PHASE1_FRAC * tl;
    int best_n = min_n;
    if (have_best && GBEST.n > best_n) best_n = GBEST.n;
    int have = 0;
    int bM = 1, bK = 1, bR = 1;
    int fails = 0;
    Cfg cur, best_cfg;
    memset(&cur, 0, sizeof(cur));
    memset(&best_cfg, 0, sizeof(best_cfg));

    while (now_s() < deadline) {
        int K = (rint_(100) < 75) ? 1 : 2;
        long long g0 = (long long)best_n / (2 * K) + 1;
        long long span = g0 / 25 + 6 + (long long)(fails / 40) * (g0 / 50 + 1);
        if (span > g0 / 3 + 6) span = g0 / 3 + 6;
        long long g = g0 + (long long)rint_((int)span);

        int M, Kk, R;
        sample_group(g, &M, &Kk, &R);
        set_group(M, Kk, R);
        if (GG > 6000) continue;
        int N = 2 * K * GG;
        if (N > MAXV) continue;
        if (N <= best_n) continue;

        cur.K = K;
        cur.G = GG;
        ensure_cap(N);
        random_cfg(&cur);
        reset_weights(K, N);
        breakout(&cur, BREAK_ITERS);
        cost_of(&cur, 0);
        if (g_rawcost > 0 && g_rawcost <= POLISH_T) {
            reset_weights(K, N);
            polish(&cur);
        }
        cost_of(&cur, 0);
        if (g_rawcost == 0) {
            best_n = N;
            best_cfg = cur;
            bM = M;
            bK = Kk;
            bR = R;
            have = 1;
            fails = 0;
        } else {
            fails++;
        }
    }

    if (have) {
        set_group(bM, bK, bR);
        cfg_to_graph(&best_cfg, &GTMP);
        if (GTMP.n <= MAXV && bad_count(&GTMP) == 0 &&
            (!have_best || GTMP.n > GBEST.n)) {
            g_copy(&GBEST, &GTMP);
            have_best = 1;
        }
    }
    if (!have_best) build_kdd(&GBEST);

    /* Phase 2: splice-and-repair growth from the best valid graph. */
    deadline = t0 + tl;
    phase2();
    print_graph(&GBEST);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python glue: exact constructions first, then the C search.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(3.0, min(0.88 * time_limit, time_limit - 5.0))

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # C search: symmetric search, then splice-and-repair from the best graph.
    # The best exact construction is passed on stdin as the start graph.
    if d >= 3 and D >= 3:
        c_budget = deadline - time.monotonic() - 1.5
        if c_budget >= 2.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{c_budget:.2f}", best_n],
                                stdin_graph=best, timeout=time_limit - 3.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
