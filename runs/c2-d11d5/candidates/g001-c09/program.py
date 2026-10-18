"""Combined program: known constructions in Python, then one C engine run.

The C engine (C_SOURCE) does three things in order:
  1. Bi-Cayley lifts over semidirect products Z_m x| Z_k. Each base size k gives k
     A-blocks and k B-blocks joined by d permutation layers with group voltages. Simulated
     annealing on the voltages and layer permutations minimises unreached (block, vertex)
     pairs. A bandit over k picks the base size and group order.
  2. Each success is checked exactly and becomes the new target, so the order climbs.
  3. With the remaining time, grow-by-two repair: insert one vertex per side from spare
     degree, then anneal degree-preserving edge swaps until the diameter is <= D.
Python builds the best known start graph and keeps a valid fallback.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search core.
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v" (valid start graph), or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 12288
#define MAXD 32
#define MAXW (MAXN / 64)
#define MAXK 4
#define MAXG 6144
#define MAXRP 64
#define PEN 1000L

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static double t_end;

/* ------------------------------------------------------------ utilities */

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

/* Largest possible order of a bipartite graph with max degree d and diameter D. */
static long moore_bound(void) {
    if (D <= 0 || d <= 0) return 1;
    if (d == 1) return 2;
    if (d == 2) return 2L * D;
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        if (s > 100000000L) break;
        p *= (d - 1);
    }
    return 2 * s;
}

/* ------------------------------------------------------------ graph basics */

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

/* ------------------------------------------------------------ distance check */

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static int badv[MAXN];

/* Number of unordered pairs at distance > D. Zero means diameter <= D (and connected). */
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

/* ------------------------------------------------------------ input / output */

static void read_start(Graph *g) {
    int n, m;
    g->n = 0;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN || m < 0) return;
    g->n = n;
    for (int v = 0; v < n; v++) { g->deg[v] = 0; g->side[v] = 255; }
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= n || v >= n ||
            u == v || g->deg[u] >= MAXD || g->deg[v] >= MAXD) { g->n = 0; return; }
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

/* K_{d,d}: valid for D >= 2. */
static void complete_bipartite(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= d; }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

/* ------------------------------------------------------------ groups */

/* Z_m x|_r Z_k: element (a, b) is the int a*k + b; (a,b)(c,e) = (a + r^b c mod m, b + e mod k). */
typedef struct {
    int m, k, r;
    int rp[MAXRP]; /* rp[b] = r^b mod m */
} Grp;

static long gmul(const Grp *G, long x, long y) {
    long a = x / G->k, b = x % G->k, c = y / G->k, e = y % G->k;
    return ((a + (long)G->rp[b] * c) % G->m) * G->k + (b + e) % G->k;
}

/* Inverse of (a, b) is (-r^(k-b) a, -b). */
static long ginv_elem(const Grp *G, long x) {
    long a = x / G->k, b = x % G->k;
    long nb = (G->k - b) % G->k;
    long c = (G->m - ((long)G->rp[nb] * a) % G->m) % G->m;
    return c * G->k + nb;
}

static const int K2_CHOICES[20] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36};

/* Random Z_m x| Z_k2 with m*k2 >= target (and <= MAXG). Returns 1 on success. */
static int sample_group(long target, Grp *G) {
    for (int tries = 0; tries < 200; tries++) {
        int k2 = K2_CHOICES[rndint(20)];
        long m = (target + k2 - 1) / k2;
        if (m < 2) m = 2;
        if (m * k2 > MAXG) continue;
        long r = -1;
        if (k2 == 1) {
            r = 1;
        } else if (k2 == 2 && rnd01() < 0.3) {
            r = m - 1;
            if (gcd((int)r, (int)m) != 1 || powmod(r, 2, m) != 1 % m) continue;
        } else {
            for (int u = 0; u < 60 && r < 0; u++) {
                long c = (m > 2) ? 2 + rndint((int)(m - 2)) : 1;
                if (gcd((int)c, (int)m) == 1 && powmod(c, k2, m) == 1 % m) r = c;
            }
            if (r < 0) continue;
        }
        G->m = (int)m;
        G->k = k2;
        G->r = (int)r;
        G->rp[0] = 1 % G->m;
        for (int b = 1; b < k2; b++) G->rp[b] = (int)((long)G->rp[b - 1] * r % m);
        return 1;
    }
    return 0;
}

/* ------------------------------------------------------------ bi-Cayley lifts */

typedef struct {
    int d, k, G, N;
    Grp grp;
    int layers[MAXD][MAXK];   /* layers[l][i] = B-block joined to A-block i in layer l */
    int S[MAXD][MAXK];        /* voltage of that dart */
    int ginv[MAXG];
    int nbr[MAXD][MAXN];
} Bic;

static Bic BI;
static uint32_t BUF_A[MAXN], BUF_B[MAXN], RCH[MAXN], RTMP[MAXN];

/* A-block i (vertices i*G + x) joins B-block j (vertices (k+j)*G + h) with g*s = h. */
static void set_dart(Bic *B, int l, int i, int j, int s) {
    int k = B->k, G = B->G;
    int *row = B->nbr[l];
    for (int x = 0; x < G; x++)
        row[i * G + x] = (k + j) * G + (int)gmul(&B->grp, x, s);
    int si = B->ginv[s];
    for (int h = 0; h < G; h++)
        row[(k + j) * G + h] = i * G + (int)gmul(&B->grp, h, si);
}

/* Reachability bitmasks: bit b of cur[v] set iff dist(v, rep_b) <= D, where rep_b = b*G.
 * Returns the number of unreached (rep, vertex) pairs; the reach array goes to RTMP. */
static long reach_compute(const Bic *B) {
    int N = B->N, k = B->k, G = B->G, dd = B->d;
    uint32_t *cur = BUF_A, *nxt = BUF_B;
    memset(cur, 0, sizeof(uint32_t) * (size_t)N);
    for (int b = 0; b < 2 * k; b++) cur[b * G] |= 1u << b;
    for (int r = 0; r < D; r++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint32_t x = cur[v];
            for (int l = 0; l < dd; l++) x |= cur[B->nbr[l][v]];
            nxt[v] = x;
            changed |= (x != cur[v]);
        }
        uint32_t *t = cur;
        cur = nxt;
        nxt = t;
        if (!changed) break;
    }
    long unr = 0;
    for (int v = 0; v < N; v++) unr += 2 * k - __builtin_popcount(cur[v]);
    memcpy(RTMP, cur, sizeof(uint32_t) * (size_t)N);
    return unr;
}

/* Number of darts repeating an earlier (i, j, s) key; those would be multi-edges. */
static long dup_count(const Bic *B) {
    int X = B->d * B->k;
    long keys[MAXD * MAXK];
    int c = 0;
    for (int l = 0; l < B->d; l++)
        for (int i = 0; i < B->k; i++)
            keys[c++] = ((long)i * B->k + B->layers[l][i]) * B->G + B->S[l][i];
    long dup = 0;
    for (int a = 0; a < X; a++)
        for (int b = 0; b < a; b++)
            if (keys[a] == keys[b]) { dup++; break; }
    return dup;
}

/* Simulated annealing over layers and voltages. Returns 1 with a valid lift in B on success. */
static int anneal(Bic *B, double until, long iters, long patience) {
    int k = B->k, G = B->G, N = B->N, dd = B->d;
    uint32_t full = (1u << (2 * k)) - 1;
    for (int l = 0; l < dd; l++) {
        int perm[MAXK];
        for (int i = 0; i < k; i++) perm[i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int s = perm[i]; perm[i] = perm[j]; perm[j] = s;
        }
        for (int i = 0; i < k; i++) B->layers[l][i] = perm[i];
    }
    for (int l = 0; l < dd; l++)
        for (int i = 0; i < k; i++) B->S[l][i] = rndint(G);
    for (int l = 0; l < dd; l++)
        for (int i = 0; i < k; i++) set_dart(B, l, i, B->layers[l][i], B->S[l][i]);

    long cost = reach_compute(B) + PEN * dup_count(B);
    memcpy(RCH, RTMP, sizeof(uint32_t) * (size_t)N);
    double c0 = cost > 1 ? (double)cost : 1.0;
    long best_cost = cost, last = 0;

    for (long t = 0; t < iters && cost > 0; t++) {
        if ((t & 31) == 0 && now() > until) break;
        if (t - last > patience) break;
        double temp = 0.01 * c0 * (1.0 - (double)t / (double)iters);
        if (temp < 0.5) temp = 0.5;

        if (k >= 2 && rnd01() < 0.25) {
            /* layer-swap: exchange the B-targets of two A-blocks in one layer */
            int l = rndint(dd);
            int i1 = rndint(k), i2 = rndint(k - 1);
            if (i2 >= i1) i2++;
            int tmp = B->layers[l][i1];
            B->layers[l][i1] = B->layers[l][i2];
            B->layers[l][i2] = tmp;
            set_dart(B, l, i1, B->layers[l][i1], B->S[l][i1]);
            set_dart(B, l, i2, B->layers[l][i2], B->S[l][i2]);
            long c2 = reach_compute(B) + PEN * dup_count(B);
            if (c2 <= cost || rnd01() < exp((double)(cost - c2) / temp)) {
                cost = c2;
                memcpy(RCH, RTMP, sizeof(uint32_t) * (size_t)N);
                if (cost < best_cost) { best_cost = cost; last = t; }
            } else {
                tmp = B->layers[l][i1];
                B->layers[l][i1] = B->layers[l][i2];
                B->layers[l][i2] = tmp;
                set_dart(B, l, i1, B->layers[l][i1], B->S[l][i1]);
                set_dart(B, l, i2, B->layers[l][i2], B->S[l][i2]);
            }
            continue;
        }

        /* voltage move: defect-targeted with probability 0.4, otherwise uniform */
        int u = -1;
        if (rnd01() < 0.4) {
            for (int tr = 0; tr < 20; tr++) {
                int v = rndint(N);
                if (RCH[v] != full) { u = v; break; }
            }
        }
        int l, i;
        if (u >= 0) {
            int block = u / G;
            l = rndint(dd);
            if (block < k) {
                i = block;
            } else {
                int j = block - k;
                i = 0;
                for (int q = 0; q < k; q++)
                    if (B->layers[l][q] == j) { i = q; break; }
            }
        } else {
            l = rndint(dd);
            i = rndint(k);
        }
        int old = B->S[l][i];
        int nw = rndint(G);
        if (nw == old) continue;
        B->S[l][i] = nw;
        set_dart(B, l, i, B->layers[l][i], nw);
        long c2 = reach_compute(B) + PEN * dup_count(B);
        if (c2 <= cost || rnd01() < exp((double)(cost - c2) / temp)) {
            cost = c2;
            memcpy(RCH, RTMP, sizeof(uint32_t) * (size_t)N);
            if (cost < best_cost) { best_cost = cost; last = t; }
        } else {
            B->S[l][i] = old;
            set_dart(B, l, i, B->layers[l][i], old);
        }
    }
    return cost == 0;
}

static void bic_to_graph(const Bic *B, Graph *g) {
    int kG = B->k * B->G;
    g->n = B->N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= kG; }
    for (int u = 0; u < kG; u++)
        for (int l = 0; l < B->d; l++) add_edge(g, u, B->nbr[l][u]);
}

static void bic_search(Graph *best, double until) {
    static Graph cand;
    long moore = moore_bound();
    long trials[MAXK + 1], wins[MAXK + 1];
    for (int k = 0; k <= MAXK; k++) { trials[k] = 0; wins[k] = 0; }
    while (now() < until) {
        int k;
        if (rnd01() < 0.2) {
            k = 1 + rndint(MAXK);
        } else {
            double bv = -1.0;
            k = 1;
            for (int kk = 1; kk <= MAXK; kk++) {
                double v = (wins[kk] + 1.0) / (trials[kk] + 2.0) + 0.02 * rnd01();
                if (v > bv) { bv = v; k = kk; }
            }
        }
        long base = best->n / (2 * k);
        long range = base / 8 + 1;
        if (range < 2) range = 2;
        long target = base + 1 + rndint((int)range);
        if (target < 2) target = 2;

        Grp g;
        if (!sample_group(target, &g)) continue;
        long G = (long)g.m * g.k;
        long N = 2L * k * G;
        if (N <= best->n || N > moore || N > MAXN || G > MAXG) continue;

        trials[k]++;
        Bic *B = &BI;
        B->d = d;
        B->k = k;
        B->G = (int)G;
        B->N = (int)N;
        B->grp = g;
        for (long x = 0; x < G; x++) B->ginv[x] = (int)ginv_elem(&g, x);
        if (anneal(B, until, 20000, 3000)) {
            wins[k]++;
            bic_to_graph(B, &cand);
            if (cand.n > best->n && is_valid(&cand)) copy_graph(best, &cand);
        }
    }
}

/* ------------------------------------------------------------ grow by two */

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
    while (now() < until && best->n + 2 <= moore_bound()) {
        double left = until - now();
        double slice = left < 4.0 ? left : (left / 4 > 4.0 ? left / 4 : 4.0);
        if (grow_once(best, &work, now() + slice)) copy_graph(best, &work);
    }
}

/* ------------------------------------------------------------ main */

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

    if (d < 1 || d > MAXD || D < 2) { printf("1 0\n"); return 0; }

    static Graph best;
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (!is_valid(&best)) complete_bipartite(&best);

    if (best.n < moore_bound())
        bic_search(&best, t0 + (t_end - t0) * 0.8);
    if (best.n + 2 <= moore_bound() && best.n + 2 <= MAXN)
        grow_search(&best, t_end);

    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python constructions (validated before use).
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
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _consider(best, cand, d, D):
    n, e = cand
    if n > best[0] and lib.is_valid(n, e, d, D):
        return cand
    return best


def known_start(d, D):
    """Best valid graph Python can build directly for (d, D); K_{d,d} as the floor."""
    best = lib.haar_graph(d, range(d))   # K_{d,d}: valid for D >= 2
    cands = []
    if D >= 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                cands.append(lib.projective_plane_incidence(q))
                break
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        cands.append(lib.araujo_lopez_graph(d - 2))
    if D == 4:
        g = _best_gq(d)
        if g is not None:
            cands.append(g)
    for c in cands:
        best = _consider(best, c, d, D)
    return best


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return (2, [(0, 1)]) if d >= 1 else (1, [])

    best = known_start(d, D)
    # Moore-optimal graphs need no search.
    if best[0] >= lib.moore_bound(d, D) or d < 2:
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.5
    if budget < 1.0:
        return best

    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=best, timeout=budget + 8.0)
        n, edges = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)
    except Exception:
        pass  # keep the valid Python fallback
    return best
