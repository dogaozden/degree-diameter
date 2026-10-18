"""Combined search: exact constructions in Python, then a C engine that runs bi-Cayley voltage-lift
annealing over semidirect groups Z_m x| Z_k (layer-permutation moves plus voltage moves), with a
grow-by-two squeeze at the end. Every returned graph is checked with lib.is_valid, and a valid
fallback is always kept.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search core (bi-Cayley anneal + grow-by-two).
 *
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v": a valid start graph, or "0 0".
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * Search:
 *   1. Bi-Cayley lifts over Z_m x|_r Z_k2. k base vertices per side; layer l maps A-block i
 *      to B-block LAY[l][i] with voltage SV[l][i] (A_{i,g} ~ B_{j, g*s}). Every layer is a
 *      permutation, so the graph is d-regular and bipartite. Anneal the layers and voltages to
 *      minimise unreached (representative, vertex) pairs plus a duplicate-edge penalty.
 *      Left multiplication is an automorphism, so the 2k block representatives certify
 *      diameter <= D.
 *   2. Grow by two: insert one vertex per side with spare degree from edge swaps, then anneal
 *      edge swaps until the diameter is at most D.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 8192
#define MAXD 32
#define MAXW (MAXN / 64)
#define MAXK 4
#define PENALTY 1000L

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static double t_end;

/* ------------------------------------------------------------------ utilities */

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rng_state = 88172645463325252ULL;
static uint64_t rnd(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return rng_state;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int gcd(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static long powmod(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

/* Upper bound on the order of a bipartite graph with max degree d and diameter D. */
static long moore_bound(void) {
    if (D <= 0 || d <= 0) return 1;
    if (d == 1) return 2;
    if (d == 2) return 2L * D;
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        if (s > 100000000L) return 200000000L;
        p *= (d - 1);
    }
    return 2 * s;
}

/* ------------------------------------------------------------------ graph basics */

static int has_edge(const Graph *g, int u, int v) {
    for (int i = 0; i < g->deg[u]; i++)
        if (g->adj[u][i] == v) return 1;
    return 0;
}

static void add_edge(Graph *g, int u, int v) {
    g->adj[u][g->deg[u]++] = v;
    g->adj[v][g->deg[v]++] = u;
}

static void del_half(Graph *g, int u, int v) {
    for (int i = 0; i < g->deg[u]; i++)
        if (g->adj[u][i] == v) {
            g->adj[u][i] = g->adj[u][--g->deg[u]];
            return;
        }
}

static void del_edge(Graph *g, int u, int v) {
    del_half(g, u, v);
    del_half(g, v, u);
}

static void copy_graph(Graph *dst, const Graph *src) {
    dst->n = src->n;
    for (int v = 0; v < src->n; v++) {
        dst->deg[v] = src->deg[v];
        dst->side[v] = src->side[v];
        memcpy(dst->adj[v], src->adj[v], sizeof(int) * src->deg[v]);
    }
}

/* ------------------------------------------------------------------ distance check */

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static int badv[MAXN];

/* Number of unordered pairs at distance > D (0 means diameter <= D and connected). */
static long bad_pairs(const Graph *g) {
    int n = g->n, W = (n + 63) / 64;
    uint64_t *cur = RA, *nxt = RB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            const uint64_t *src = cur + (size_t)v * W;
            for (int w = 0; w < W; w++) dst[w] = src[w];
            for (int i = 0; i < g->deg[v]; i++) {
                const uint64_t *s = cur + (size_t)g->adj[v][i] * W;
                for (int w = 0; w < W; w++) dst[w] |= s[w];
            }
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
    }
    long total = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        const uint64_t *s = cur + (size_t)v * W;
        for (int w = 0; w < W; w++) c += __builtin_popcountll(s[w]);
        badv[v] = n - c;
        total += n - c;
    }
    return total / 2;
}

static int is_valid(const Graph *g) {
    if (g->n <= 0 || g->n > MAXN) return 0;
    for (int v = 0; v < g->n; v++) {
        if (g->deg[v] > d) return 0;
        for (int i = 0; i < g->deg[v]; i++) {
            int u = g->adj[v][i];
            if (u < 0 || u >= g->n || u == v || g->side[u] == g->side[v]) return 0;
            for (int j = 0; j < i; j++)
                if (g->adj[v][j] == u) return 0;
        }
    }
    return bad_pairs(g) == 0;
}

/* ------------------------------------------------------------------ input / output */

static void read_start(Graph *g) {
    int n, m;
    g->n = 0;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN || m < 0) return;
    g->n = n;
    for (int v = 0; v < n; v++) { g->deg[v] = 0; g->side[v] = 255; }
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= n || v >= n || u == v ||
            g->deg[u] >= MAXD || g->deg[v] >= MAXD) { g->n = 0; return; }
        add_edge(g, u, v);
    }
    static int queue[MAXN];
    for (int s = 0; s < n; s++) {
        if (g->side[s] != 255) continue;
        int head = 0, tail = 0;
        g->side[s] = 0;
        queue[tail++] = s;
        while (head < tail) {
            int v = queue[head++];
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[v][i];
                if (g->side[u] == 255) { g->side[u] = 1 - g->side[v]; queue[tail++] = u; }
                else if (g->side[u] == g->side[v]) { g->n = 0; return; }
            }
        }
    }
    if (!is_valid(g)) g->n = 0;
}

static void print_graph(const Graph *g) {
    long m = 0;
    for (int u = 0; u < g->n; u++)
        for (int i = 0; i < g->deg[u]; i++)
            if (u < g->adj[u][i]) m++;
    printf("%d %ld\n", g->n, m);
    for (int u = 0; u < g->n; u++)
        for (int i = 0; i < g->deg[u]; i++)
            if (u < g->adj[u][i]) printf("%d %d\n", u, g->adj[u][i]);
}

static void complete_bipartite(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= d; }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

/* ------------------------------------------------------------------ groups */

/* Z_GM x|_GR Z_GK: element (a, b) is the int a*GK + b, (a,b)(c,e) = (a + r^b c, b + e). */
static int GM, GK, GR, GN;
static int GRP[MAXN]; /* GRP[b] = r^b mod m */

static int gmul(int x, int y) {
    int a = x / GK, b = x % GK, c = y / GK, e = y % GK;
    return (int)((a + (long)GRP[b] * c) % GM) * GK + (b + e) % GK;
}

static int ginv(int x) {
    int a = x / GK, b = x % GK;
    int nb = (GK - b) % GK;
    int c = (int)((GM - ((long)GRP[nb] * a) % GM) % GM);
    return c * GK + nb;
}

static const int K2_CHOICES[20] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36};

/* Random semidirect product of order about target. Returns 1 and sets the globals on success. */
static int sample_group(long target) {
    for (int tries = 0; tries < 200; tries++) {
        int k2 = K2_CHOICES[rndint(20)];
        long mm = (target + k2 - 1) / k2;
        if (mm < 2) mm = 2;
        if (mm * k2 > MAXN) continue;
        int m = (int)mm;
        int r = 1 % m;
        if (k2 == 2 && rnd01() < 0.3) {
            r = m - 1; /* dihedral type: r^2 = 1 mod m always holds */
        } else if (k2 > 1) {
            int found = -1;
            for (int t = 0; t < 60; t++) {
                int c = m > 2 ? 2 + rndint(m - 2) : 1;
                if (gcd(c, m) == 1 && powmod(c, k2, m) == 1 % m) { found = c; break; }
            }
            if (found < 0) continue;
            r = found;
        }
        GM = m;
        GK = k2;
        GR = r;
        GN = m * k2;
        GRP[0] = 1 % m;
        for (int b = 1; b < k2; b++) GRP[b] = (int)((long)GRP[b - 1] * r % m);
        return 1;
    }
    return 0;
}

static int pick_k(const int *trials, const int *wins) {
    if (rnd01() < 0.2) return 1 + rndint(MAXK);
    int bk = 1;
    double bv = -1.0;
    for (int k = 1; k <= MAXK; k++) {
        double v = (wins[k] + 1.0) / (trials[k] + 2.0) + 0.02 * rnd01();
        if (v > bv) { bv = v; bk = k; }
    }
    return bk;
}

/* ------------------------------------------------------------------ bi-Cayley state */

static int BK, BN;
static int LAY[MAXD][MAXK];      /* LAY[l][i]  = B-block hit by A-block i in layer l */
static int PINV[MAXD][MAXK];     /* PINV[l][j] = A-block hitting B-block j in layer l */
static int SV[MAXD][MAXK];       /* voltages */
static int NBR[MAXD][MAXN];      /* NBR[l][u] = neighbour of u in layer l */
static uint64_t RCUR[MAXN], RCAND[MAXN], RTMP[MAXN];

/* Recompute the neighbour table of layer l from LAY and SV. */
static void rebuild_layer(int l) {
    int K = BK, G = GN;
    for (int i = 0; i < K; i++) {
        int j = LAY[l][i], s = SV[l][i];
        int si = ginv(s);
        int *ra = NBR[l] + i * G;
        int *rb = NBR[l] + (K + j) * G;
        for (int g = 0; g < G; g++) {
            ra[g] = (K + j) * G + gmul(g, s);
            rb[g] = i * G + gmul(g, si);
        }
    }
}

static void swap_layer(int l, int i1, int i2) {
    int t = LAY[l][i1];
    LAY[l][i1] = LAY[l][i2];
    LAY[l][i2] = t;
    PINV[l][LAY[l][i1]] = i1;
    PINV[l][LAY[l][i2]] = i2;
    rebuild_layer(l);
}

/* Number of duplicated (i, j, s) keys. Duplicates would create multi-edges. */
static long dup_count(void) {
    int K = BK, tot = d * K, cnt = 0;
    for (int p = 0; p < tot; p++) {
        int l1 = p / K, i1 = p % K;
        for (int q = p + 1; q < tot; q++) {
            int l2 = q / K, i2 = q % K;
            if (i1 == i2 && LAY[l1][i1] == LAY[l2][i2] && SV[l1][i1] == SV[l2][i2]) cnt++;
        }
    }
    return cnt;
}

/* Cost = unreached (block representative, vertex) pairs + penalty * duplicates.
 * Writes the reachability masks into dst. */
static long eval_cost(uint64_t *dst) {
    int N = BN, K = BK;
    uint64_t *cur = dst, *nxt = RTMP;
    memset(cur, 0, sizeof(uint64_t) * (size_t)N);
    for (int b = 0; b < 2 * K; b++) cur[(size_t)b * GN] = 1ULL << b;
    for (int r = 0; r < D; r++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint64_t x = cur[v];
            for (int l = 0; l < d; l++) x |= cur[NBR[l][v]];
            nxt[v] = x;
            changed |= (x != cur[v]);
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
        if (!changed) break;
    }
    if (cur != dst) memcpy(dst, cur, sizeof(uint64_t) * (size_t)N);
    long unreached = 0;
    for (int v = 0; v < N; v++) unreached += 2 * K - __builtin_popcountll(dst[v]);
    return unreached + PENALTY * dup_count();
}

static int accept(long c2, long cost, double temp) {
    if (c2 <= cost) return 1;
    return rnd01() < exp(-(double)(c2 - cost) / temp);
}

/* Anneal layers and voltages for the current BK and group. Returns 1 when cost reaches 0. */
static int anneal(int iters, int patience, double deadline) {
    const int K = BK, G = GN, N = BN;
    const uint64_t full = (1ULL << (2 * K)) - 1;
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < K; i++) LAY[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1), s = LAY[l][i];
            LAY[l][i] = LAY[l][j];
            LAY[l][j] = s;
        }
        for (int i = 0; i < K; i++) PINV[l][LAY[l][i]] = i;
        for (int i = 0; i < K; i++) SV[l][i] = rndint(G);
        rebuild_layer(l);
    }
    long cost = eval_cost(RCUR);
    double c0 = cost > 1 ? (double)cost : 1.0;
    long best_cost = cost;
    int last = 0;
    for (int t = 0; t < iters && cost != 0; t++) {
        if (t - last > patience) break;
        if ((t & 7) == 0 && now() > deadline) break;
        double temp = 0.01 * c0 * (1.0 - (double)t / iters);
        if (temp < 0.5) temp = 0.5;

        if (K >= 2 && rnd01() < 0.25) {
            int l = rndint(d);
            int i1 = rndint(K), i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            swap_layer(l, i1, i2);
            long c2 = eval_cost(RCAND);
            if (accept(c2, cost, temp)) {
                cost = c2;
                memcpy(RCUR, RCAND, sizeof(uint64_t) * (size_t)N);
                if (cost < best_cost) { best_cost = cost; last = t; }
            } else {
                swap_layer(l, i1, i2);
            }
            continue;
        }

        int l = rndint(d), i = rndint(K);
        if (rnd01() < 0.4) {
            /* defect-targeted: pick a vertex that is not yet fully reached */
            for (int tries = 0; tries < 64; tries++) {
                int u = rndint(N);
                if (RCUR[u] != full) {
                    int block = u / G;
                    if (block < K) i = block;
                    else i = PINV[l][block - K];
                    break;
                }
            }
        }
        int old = SV[l][i];
        int nw = rndint(G);
        if (nw == old) continue;
        SV[l][i] = nw;
        rebuild_layer(l);
        long c2 = eval_cost(RCAND);
        if (accept(c2, cost, temp)) {
            cost = c2;
            memcpy(RCUR, RCAND, sizeof(uint64_t) * (size_t)N);
            if (cost < best_cost) { best_cost = cost; last = t; }
        } else {
            SV[l][i] = old;
            rebuild_layer(l);
        }
    }
    return cost == 0;
}

static void build_bicayley_graph(Graph *g) {
    int K = BK, G = GN, N = BN;
    g->n = N;
    for (int v = 0; v < N; v++) {
        g->deg[v] = 0;
        g->side[v] = v >= K * G;
    }
    for (int l = 0; l < d; l++)
        for (int u = 0; u < K * G; u++) add_edge(g, u, NBR[l][u]);
}

static void bicayley_search(Graph *best, double until) {
    static Graph cand;
    int trials[MAXK + 1] = {0}, wins[MAXK + 1] = {0};
    long moore = moore_bound();
    while (now() < until) {
        int k = pick_k(trials, wins);
        long base = best->n / (2 * k);
        long target = base + 1 + rndint((int)(base / 8 + 2));
        if (target < 2) target = 2;
        if (!sample_group(target)) continue;
        long N = 2L * k * GN;
        if (N <= best->n || N > moore || N > MAXN) continue;
        BK = k;
        BN = (int)N;
        trials[k]++;
        if (anneal(4000, 1200, until)) {
            wins[k]++;
            build_bicayley_graph(&cand);
            if (cand.n > best->n && is_valid(&cand)) copy_graph(best, &cand);
        }
    }
}

/* ------------------------------------------------------------------ grow by two */

static int grow_once(const Graph *best, Graph *work, double until) {
    int n = best->n;
    if (n + 2 > moore_bound() || n + 2 > MAXN) return 0;
    copy_graph(work, best);
    int x = n, y = n + 1;
    work->n = n + 2;
    work->deg[x] = work->deg[y] = 0;
    work->side[x] = 0;
    work->side[y] = 1;
    add_edge(work, x, y);
    static int used[MAXN];
    static int stamp = 0;
    stamp++;
    used[x] = used[y] = stamp;
    for (int k = 0, tries = 0; k < d - 1 && tries < 100000; tries++) {
        int a = rndint(n);
        if (work->side[a] != 0 || used[a] == stamp || work->deg[a] == 0) continue;
        int b = work->adj[a][rndint(work->deg[a])];
        if (used[b] == stamp || b >= n) continue;
        del_edge(work, a, b);
        add_edge(work, x, b);
        add_edge(work, y, a);
        used[a] = used[b] = stamp;
        k++;
    }
    long bad = bad_pairs(work);
    double T = 1.0;
    long it = 0;
    while (bad > 0) {
        if ((++it & 15) == 0 && now() > until) return 0;
        int v = rndint(work->n);
        for (int tries = 0; tries < 30 && badv[v] == 0; tries++) v = rndint(work->n);
        if (work->deg[v] == 0) continue;
        int u = work->adj[v][rndint(work->deg[v])];
        int s = rndint(work->n);
        if (work->side[s] != work->side[v] || s == v || work->deg[s] == 0) continue;
        int t = work->adj[s][rndint(work->deg[s])];
        if (t == u || has_edge(work, v, t) || has_edge(work, s, u)) continue;
        del_edge(work, v, u);
        del_edge(work, s, t);
        add_edge(work, v, t);
        add_edge(work, s, u);
        long nb = bad_pairs(work);
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) {
            bad = nb;
        } else {
            del_edge(work, v, t);
            del_edge(work, s, u);
            add_edge(work, v, u);
            add_edge(work, s, t);
        }
        T *= 0.9995;
        if (T < 0.05) T = 1.0;
    }
    return is_valid(work);
}

static void grow_search(Graph *best, double until) {
    static Graph work;
    while (now() < until && best->n + 2 <= moore_bound() && best->n + 2 <= MAXN) {
        double left = until - now();
        double slice = left < 4.0 ? left : (left / 4 > 4.0 ? left / 4 : 4.0);
        if (grow_once(best, &work, now() + slice)) copy_graph(best, &work);
    }
}

/* ------------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit < start_graph\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit * 0.92;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 1 || d > MAXD) { printf("0 0\n"); return 0; }

    static Graph best;
    read_start(&best);
    if (best.n == 0) {
        if (D < 2) { printf("0 0\n"); return 0; }
        complete_bipartite(&best);
    }
    if (!is_valid(&best)) {
        if (D < 2) { printf("0 0\n"); return 0; }
        complete_bipartite(&best);
    }

    if (D >= 2 && best.n < moore_bound() && now() < t_end) {
        double span = t_end - t0;
        bicayley_search(&best, t0 + span * 0.9);
        grow_search(&best, t_end);
    }
    if (!is_valid(&best)) {
        if (D < 2) { printf("0 0\n"); return 0; }
        complete_bipartite(&best);
    }
    print_graph(&best);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Exact constructions (Python).
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


def _known_start(d, D):
    """Best valid exact construction Python can build for (d, D), as (n, edges)."""
    cands = [lib.haar_graph(d, range(d))]          # K_{d,d}: diameter 2
    if D >= 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                cands.append(lib.projective_plane_incidence(q))
                break
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            cands.append(lib.araujo_lopez_graph(d - 2))
        except ValueError:
            pass
    if D >= 4 and time_ok_for_gq():
        for q in range(min(d - 1, 9), 1, -1):
            if lib.is_prime_power(q):
                cands.append(_gq_w(q))
                break
    best = None
    for n, e in cands:
        if lib.is_valid(n, e, d, D) and (best is None or n > best[0]):
            best = (n, e)
    return best


def time_ok_for_gq():
    """Generalized quadrangle construction is only attempted when the case has enough time."""
    return True


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = _known_start(d, D)
    if best is None:
        best = lib.haar_graph(d, range(d))
    if best[0] >= lib.moore_bound(d, D):
        return best   # Moore graph: nothing can beat it

    budget = min(0.85 * time_limit, time_limit - 4.0) - (time.monotonic() - t0)
    if budget < 1.0 or d > 32:
        return best

    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=best, timeout=budget + 15)
        n, e = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
    except Exception:
        pass
    return best
