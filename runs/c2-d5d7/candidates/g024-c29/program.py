"""Multi-fibre voltage-lift search for the d=5, D=7 target.

The parent grew the hexagon start by vertex pairs and ran bi-Cayley annealing on top of it. This
version replaces the growth phase with a different construction: lifts with p fibres per side
(p = 1..6) over a semidirect group G of order N. Each fibre vertex is (i, x), and dart (i, j, g)
joins (i, x) to (p+j, x*g). For a random d-regular bipartite base multigraph on p+p vertices, the
voltages are annealed against an orbit-reduced diameter defect. Left multiplication by G is an
automorphism of the lift and is transitive on each fibre, so one BFS per fibre (2p in total) gives
the exact defect. The lift order 2pN is chosen just above the incumbent. A tabu/annealing
bi-Cayley phase (p = 1) then uses the remaining time. The hexagon incidence graph H(q), q = 4,
remains the fallback, and every result is checked in C and again in Python with lib.is_valid.
"""
import time

import itertools

import numpy as np

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search core, multi-fibre voltage-lift version.
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v", or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 6144
#define MAXD 32
#define MAXW (MAXN / 64)
#define MAXP 8
#define MAXH 2048
#define BC_SPAN 200
#define BC_STEPS 6000
#define BC_ATTEMPTS 8
#define BC_GROUPS 6
#define TABU_STEPS 1200
#define TABU_CAND 48
#define TABU_TENURE 8
#define MF_STEPS 15000
#define MF_ATTEMPTS 3
#define MF_SPAN 4
#define MF_MAXP 6

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static double t_end;

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

static long moore_bound(void) {
    if (D <= 0 || d <= 0) return 1;
    if (d == 1) return 2;
    if (d == 2) return 2L * D;
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 100000000L) break;
    }
    return 2 * s;
}

static void add_edge(Graph *g, int u, int v) {
    g->adj[u][g->deg[u]++] = v;
    g->adj[v][g->deg[v]++] = u;
}

static void copy_graph(Graph *dst, const Graph *src) {
    dst->n = src->n;
    for (int v = 0; v < src->n; v++) {
        dst->deg[v] = src->deg[v];
        dst->side[v] = src->side[v];
        memcpy(dst->adj[v], src->adj[v], sizeof(int) * src->deg[v]);
    }
}

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static int badv[MAXN];

/* Full all-pairs check by bitsets: number of unordered pairs at distance > D. */
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

static void read_start(Graph *g) {
    int n, m;
    g->n = 0;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN) return;
    g->n = n;
    for (int v = 0; v < n; v++) { g->deg[v] = 0; g->side[v] = 255; }
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= n || v >= n ||
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

/* Z_m x|_r Z_k: element a*k + b, (a,b)(c,e) = (a + r^b c mod m, b + e mod k). */
typedef struct {
    int m, k, r;
    int rp[MAXN];
} Grp;

static int gmul(const Grp *G, int x, int y) {
    int a = x / G->k, b = x % G->k, c = y / G->k, e = y % G->k;
    return (int)((a + (long)G->rp[b] * c) % G->m) * G->k + (b + e) % G->k;
}

/* Uniformly random admissible semidirect product of order N (reservoir sampling). */
static int random_group(int N, Grp *G) {
    long count = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        int rmax = m > 1 ? m : 2;
        for (int r = 1; r < rmax; r++) {
            if (m > 1 && gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            count++;
            if (rndint((int)(count < 2000000000L ? count : 2000000000L)) == 0) {
                G->m = m; G->k = k; G->r = r;
            }
        }
    }
    if (!count) return 0;
    G->rp[0] = 1 % G->m;
    for (int b = 1; b < G->k; b++) G->rp[b] = (int)((long)G->rp[b - 1] * G->r % G->m);
    return 1;
}

/* Prefer a non-abelian choice (r != 1, k > 1) when one is sampled quickly. */
static int pick_group_bc(int N, Grp *G) {
    for (int tries = 0; tries < 8; tries++) {
        if (!random_group(N, G)) return 0;
        if (G->m > 1 && G->k > 1 && G->r != 1) return 1;
    }
    return 1;
}

typedef struct { int i, j, g; } Dart;

/* Random d-regular bipartite base multigraph on p + p vertices, connected.
 * Each row and column of M sums to d, so the lift has exactly d*p darts. */
static void make_base(int p, int M[MAXP][MAXP]) {
    for (;;) {
        memset(M, 0, sizeof(int) * MAXP * MAXP);
        for (int t = 0; t < d; t++) {
            int perm[MAXP];
            for (int i = 0; i < p; i++) perm[i] = i;
            for (int i = p - 1; i > 0; i--) { int j = rndint(i + 1); int s = perm[i]; perm[i] = perm[j]; perm[j] = s; }
            for (int i = 0; i < p; i++) M[i][perm[i]]++;
        }
        int seen[2 * MAXP] = {0}, stack[2 * MAXP], top = 0, nseen = 1;
        seen[0] = 1;
        stack[top++] = 0;
        while (top) {
            int v = stack[--top];
            for (int u = 0; u < 2 * p; u++) {
                if (seen[u]) continue;
                int linked = v < p ? (u >= p && M[v][u - p]) : (u < p && M[u][v - p]);
                if (linked) { seen[u] = 1; nseen++; stack[top++] = u; }
            }
        }
        if (nseen == 2 * p) return;
    }
}

/* Vertex layout: A-fibre i, element x -> i*N + x; B-fibre j, element x -> (p+j)*N + x.
 * Dart (i, j, g) joins (i, x) to (p+j, x*g) for every x in G. */
static void build_lift(Graph *g, int p, int N, const Grp *G, const Dart *dt, int nd) {
    g->n = 2 * p * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= p * N; }
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, dt[t].i * N + x, p * N + dt[t].j * N + gmul(G, x, dt[t].g));
}

/* A voltage not already used by another dart on the same fibre pair (keeps the graph simple). */
static int fresh_voltage(const Dart *dt, int nd, int skip, int i, int j, int N) {
    for (;;) {
        int g = rndint(N), clash = 0;
        for (int t = 0; t < nd; t++)
            if (t != skip && dt[t].i == i && dt[t].j == j && dt[t].g == g) { clash = 1; break; }
        if (!clash) return g;
    }
}

static int dist_buf[MAXN], queue_buf[MAXN];

/* Orbit-reduced diameter defect of a lift. Left multiplication by G is an automorphism of the
 * lift and is transitive on each fibre, so one BFS per fibre from its identity element suffices.
 * Returns the total number of (representative, vertex) pairs at distance > D; 0 means valid. */
static long orbit_bad(const Graph *g, int p, int N) {
    int nv = g->n;
    long total = 0;
    for (int b = 0; b < 2 * p; b++) {
        int src = b * N;
        for (int v = 0; v < nv; v++) dist_buf[v] = -1;
        int head = 0, tail = 0;
        dist_buf[src] = 0;
        queue_buf[tail++] = src;
        while (head < tail) {
            int v = queue_buf[head++];
            if (dist_buf[v] >= D) continue;
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[v][i];
                if (dist_buf[u] < 0) {
                    dist_buf[u] = dist_buf[v] + 1;
                    queue_buf[tail++] = u;
                }
            }
        }
        total += nv - tail;
    }
    return total;
}

/* Anneal the voltages of one p-fibre lift over G. Temperature cools geometrically from 1.5 to
 * 0.1 over MF_STEPS moves. Returns the defect of the final state, which is 0 on success.
 * On return g matches dt. */
static long mf_anneal(Graph *g, int p, int N, const Grp *G, Dart *dt, int nd, double until) {
    build_lift(g, p, N, G, dt, nd);
    long bad = orbit_bad(g, p, N);
    double T = 1.5;
    const double alpha = pow(0.1 / 1.5, 1.0 / MF_STEPS);
    for (long s = 0; s < MF_STEPS && bad > 0; s++) {
        if ((s & 63) == 0 && now() > until) break;
        int t = rndint(nd);
        int old = dt[t].g;
        dt[t].g = fresh_voltage(dt, nd, t, dt[t].i, dt[t].j, N);
        build_lift(g, p, N, G, dt, nd);
        long nb = orbit_bad(g, p, N);
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) {
            bad = nb;
        } else {
            dt[t].g = old;
        }
        T *= alpha;
        if (T < 0.1) T = 0.1;
    }
    build_lift(g, p, N, G, dt, nd);
    return bad;
}

/* Multi-fibre search: repeatedly pick p in 1..MF_MAXP and a group of order N just above the
 * incumbent (2pN > best->n), anneal the voltages, and keep any valid lift that is larger. */
static void mf_search(Graph *best, double until) {
    static Graph cand;
    static Grp G;
    static Dart dt[MAXD * MAXP];
    long moore = moore_bound();
    while (now() < until) {
        int p = 1 + rndint(MF_MAXP);
        int Nlo = best->n / (2 * p) + 1;
        int N = Nlo + rndint(MF_SPAN);
        if (N < d + 1) N = d + 1;
        if (2L * p * N > moore || 2 * p * N > MAXN) {
            N = Nlo;
            if (N < d + 1) N = d + 1;
            if (2L * p * N > moore || 2 * p * N > MAXN) continue;
        }
        if (!pick_group_bc(N, &G)) continue;
        for (int a = 0; a < MF_ATTEMPTS && now() < until; a++) {
            int M[MAXP][MAXP];
            make_base(p, M);
            int nd = 0;
            for (int i = 0; i < p; i++)
                for (int j = 0; j < p; j++)
                    for (int c = 0; c < M[i][j]; c++) {
                        dt[nd].i = i;
                        dt[nd].j = j;
                        dt[nd].g = fresh_voltage(dt, nd, -1, i, j, N);
                        nd++;
                    }
            long bad = mf_anneal(&cand, p, N, &G, dt, nd, until);
            if (bad == 0 && cand.n > best->n && is_valid(&cand)) {
                copy_graph(best, &cand);
                break;
            }
        }
    }
}

/* ---------------- bi-Cayley lift search (p = 1 annealing with tabu) ----------------
 * Vertices: a_x = x (side 0), b_x = N + x (side 1), x in G.
 * Edges: a_x -- b_{x * g_t} for t = 0..d-1, with g_0 = e and distinct g_t.
 * Left multiplication is transitive on each side, so BFS from a_e and b_e suffices. */

static int MTAB[MAXH * MAXH];
static int INVT[MAXH];
static int NN;
static int dist_bc[2 * MAXH], seen_bc[2 * MAXH], q_bc[2 * MAXH];
static int stamp_bc = 0;

static void setup_group(int N, const Grp *G) {
    NN = N;
    for (int x = 0; x < N; x++) {
        int *row = MTAB + (size_t)x * N;
        for (int y = 0; y < N; y++) row[y] = gmul(G, x, y);
    }
    for (int x = 0; x < N; x++) {
        const int *row = MTAB + (size_t)x * N;
        for (int y = 0; y < N; y++)
            if (row[y] == 0) { INVT[x] = y; break; }
    }
}

static int used_upto(const int *gv, int cnt, int v) {
    for (int i = 0; i < cnt; i++)
        if (gv[i] == v) return 1;
    return 0;
}

/* Number of (source, vertex) pairs at distance > D, sources a_e and b_e. */
static long eval_bad(const int *gv) {
    int N = NN, V = 2 * N;
    int gi[MAXD];
    for (int t = 0; t < d; t++) gi[t] = INVT[gv[t]];
    long total = 0;
    for (int s = 0; s < 2; s++) {
        int src = s ? N : 0;
        int head = 0, tail = 0;
        stamp_bc++;
        seen_bc[src] = stamp_bc;
        dist_bc[src] = 0;
        q_bc[tail++] = src;
        while (head < tail) {
            int v = q_bc[head++];
            int dv = dist_bc[v];
            if (dv >= D) continue;
            if (v < N) {
                const int *row = MTAB + (size_t)v * N;
                for (int t = 0; t < d; t++) {
                    int u = N + row[gv[t]];
                    if (seen_bc[u] != stamp_bc) {
                        seen_bc[u] = stamp_bc;
                        dist_bc[u] = dv + 1;
                        q_bc[tail++] = u;
                    }
                }
            } else {
                const int *row = MTAB + (size_t)(v - N) * N;
                for (int t = 0; t < d; t++) {
                    int u = row[gi[t]];
                    if (seen_bc[u] != stamp_bc) {
                        seen_bc[u] = stamp_bc;
                        dist_bc[u] = dv + 1;
                        q_bc[tail++] = u;
                    }
                }
            }
        }
        total += V - tail;
    }
    return total;
}

/* Annealed voltage hill-climb; gv[0] = 0 is kept fixed. */
static long climb(int *gv, int *bestgv, double until) {
    long bad = eval_bad(gv);
    long bestb = bad;
    memcpy(bestgv, gv, sizeof(int) * d);
    double T = 2.0;
    const double alpha = pow(0.1, 1.0 / BC_STEPS);
    for (long s = 0; s < BC_STEPS && bad > 0; s++) {
        if ((s & 127) == 0 && now() > until) break;
        int t = 1 + rndint(d - 1);
        int old = gv[t], nv;
        do { nv = rndint(NN); } while (used_upto(gv, d, nv));
        gv[t] = nv;
        long nb = eval_bad(gv);
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) {
            bad = nb;
            if (bad < bestb) {
                bestb = bad;
                memcpy(bestgv, gv, sizeof(int) * d);
            }
        } else {
            gv[t] = old;
        }
        T *= alpha;
        if (T < 0.2) T = 0.2;
    }
    return bestb;
}

/* Tabu voltage search with aspiration; gv[0] = 0 is kept fixed. */
static long tabu_clock = 0;
static long tabu_until[MAXD][MAXH];

static long tabu_climb(int *gv, int *bestgv, double until) {
    long cur = eval_bad(gv);
    long bestb = cur;
    memcpy(bestgv, gv, sizeof(int) * d);
    for (long s = 0; s < TABU_STEPS && bestb > 0; s++) {
        if ((s & 15) == 0 && now() > until) break;
        tabu_clock++;
        long bnb = -1;
        int bt = -1, bv = -1;
        for (int c = 0; c < TABU_CAND; c++) {
            int t = 1 + rndint(d - 1);
            int nv;
            do { nv = rndint(NN); } while (used_upto(gv, d, nv));
            int old = gv[t];
            gv[t] = nv;
            long nb = eval_bad(gv);
            gv[t] = old;
            int is_tabu = tabu_until[t][nv] > tabu_clock;
            if (is_tabu && !(nb < bestb)) continue;
            if (bnb < 0 || nb < bnb) {
                bnb = nb;
                bt = t;
                bv = nv;
            }
        }
        if (bt < 0) continue;
        tabu_until[bt][gv[bt]] = tabu_clock + TABU_TENURE;
        gv[bt] = bv;
        cur = bnb;
        if (cur < bestb) {
            bestb = cur;
            memcpy(bestgv, gv, sizeof(int) * d);
        }
    }
    return bestb;
}

static void build_bc(Graph *g, int N, const int *gv) {
    g->n = 2 * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= N; }
    for (int x = 0; x < N; x++)
        for (int t = 0; t < d; t++)
            add_edge(g, x, N + MTAB[(size_t)x * N + gv[t]]);
}

static Graph bc_cand;

/* Search bi-Cayley lifts of order 2N > best->n, raising the bar on each success. */
static void bicayley_search(Graph *best, double until) {
    static int gv[MAXD], bestgv[MAXD], elite[MAXD];
    static Grp G;
    int Nlo = best->n / 2 + 1;
    if (Nlo < d + 1) Nlo = d + 1;
    long moore = moore_bound();
    long Nmax_l = moore / 2;
    if (Nmax_l > MAXH) Nmax_l = MAXH;
    if (Nmax_l > MAXN / 2) Nmax_l = MAXN / 2;
    int Nmax = (int)Nmax_l;
    while (now() < until && Nlo <= Nmax) {
        int span = Nmax - Nlo + 1;
        if (span > BC_SPAN) span = BC_SPAN;
        double u = rnd01();
        int N = Nlo + (int)(u * sqrt(u) * span);
        if (N > Nmax) N = Nmax;
        for (int grp = 0; grp < BC_GROUPS && now() < until; grp++) {
            if (!pick_group_bc(N, &G)) break;
            setup_group(N, &G);
            long elite_bad = -1;
            for (int att = 0; att < BC_ATTEMPTS && now() < until; att++) {
                if (elite_bad >= 0 && rnd01() < 0.6) {
                    memcpy(gv, elite, sizeof(int) * d);
                    int t = 1 + rndint(d - 1);
                    int nv;
                    do { nv = rndint(N); } while (used_upto(gv, d, nv));
                    gv[t] = nv;
                } else {
                    gv[0] = 0;
                    for (int t = 1; t < d; t++) {
                        int nv;
                        do { nv = rndint(N); } while (used_upto(gv, t, nv));
                        gv[t] = nv;
                    }
                }
                long b = (att & 1) ? tabu_climb(gv, bestgv, until) : climb(gv, bestgv, until);
                if (b == 0) {
                    build_bc(&bc_cand, N, bestgv);
                    if (bc_cand.n > best->n && is_valid(&bc_cand)) {
                        copy_graph(best, &bc_cand);
                        Nlo = N + 1;
                        return bicayley_search(best, until);
                    }
                    continue;
                }
                if (elite_bad < 0 || b < elite_bad) {
                    elite_bad = b;
                    memcpy(elite, bestgv, sizeof(int) * d);
                }
            }
        }
    }
}

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
    t_end = t0 + limit * 0.95;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best;
    if (d < 1 || D < 1 || d > MAXD) { complete_bipartite(&best); print_graph(&best); return 0; }
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (!is_valid(&best)) complete_bipartite(&best);

    double L = t_end - t0;
    if (D >= 2 && d >= 2 && best.n < moore_bound()) {
        /* Multi-fibre voltage lifts get most of the time; bi-Cayley annealing gets the rest. */
        mf_search(&best, t0 + L * 0.70);
        if (d >= 3 && best.n < moore_bound()) bicayley_search(&best, t_end);
    }
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


def _gq_w(q):
    """Incidence graph of points and lines of W(q): degree q+1, diameter 4."""
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


def _hexagon_incidence(q):
    """Incidence graph of the split Cayley hexagon H(q), q = 2 or 4.

    Order 2(q^6-1)/(q-1), degree q+1, bipartite, diameter 6, so it is valid for D = 6 and D = 7.
    Points: points of the quadric X0X4 + X1X5 + X2X6 = X3^2. Lines: quadric lines whose Grassmann
    coordinates satisfy p12=p34, p54=p32, p20=p35, p65=p30, p01=p36, p46=p31.
    Characteristic 2, so signs are irrelevant. The caller validates the result with lib.is_valid.
    """
    F = lib.GF(q)
    MT, AT = F.mul_table, F.add_table
    pts = []
    for v in itertools.product(range(q), repeat=7):
        if any(v) and next(c for c in v if c) == 1:
            s = AT[AT[MT[v[0], v[4]], MT[v[1], v[5]]], AT[MT[v[2], v[6]], MT[v[3], v[3]]]]
            if s == 0:
                pts.append(tuple(int(c) for c in v))
    N = len(pts)
    index = {v: i for i, v in enumerate(pts)}
    P = np.array(pts, dtype=np.int64)
    lines = set()
    for i in range(N - 1):
        x = P[i]
        Y = P[i + 1:]

        def pp(a, b):
            """Grassmann coordinate p_ab = x_a y_b - x_b y_a, for all y in Y."""
            return AT[MT[x[a], Y[:, b]], MT[x[b], Y[:, a]]]

        # Collinearity on the quadric: polar form B(x, y) = 0 (char 2 has no 2*x3*y3 term).
        s = np.zeros(len(Y), dtype=np.int64)
        for a, b in ((0, 4), (1, 5), (2, 6)):
            s = AT[s, AT[MT[x[a], Y[:, b]], MT[Y[:, a], x[b]]]]
        ok = (s == 0)
        ok &= pp(1, 2) == pp(3, 4)
        ok &= pp(5, 4) == pp(3, 2)
        ok &= pp(2, 0) == pp(3, 5)
        ok &= pp(6, 5) == pp(3, 0)
        ok &= pp(0, 1) == pp(3, 6)
        ok &= pp(4, 6) == pp(3, 1)
        for jj in np.nonzero(ok)[0]:
            y = Y[jj]
            # Points of the line: x, and t*x + y for t in GF(q).
            vecs = [tuple(int(c) for c in x)]
            for t in range(q):
                vecs.append(tuple(int(AT[MT[t, x[k]], y[k]]) for k in range(7)))
            idx = []
            for v in vecs:
                c = next(e for e in v if e)
                inv = F.inv(c)
                idx.append(index[tuple(F.mul(inv, e) for e in v)])
            lines.add(tuple(sorted(idx)))
    lines = sorted(lines)
    edges = [(pt, N + k) for k, L in enumerate(lines) for pt in L]
    return 2 * N, edges


def _largest_prime_power_le(x):
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def known_starts(d, D):
    """Algebraic candidates (may be empty); build() keeps only those that pass lib.is_valid."""
    out = []
    if D >= 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        out.append(lib.projective_plane_incidence(d - 1))
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        out.append(lib.araujo_lopez_graph(d - 2))
    if D >= 6 and d - 1 in (2, 4):
        try:
            out.append(_hexagon_incidence(d - 1))
        except Exception:
            pass
    if D >= 4:
        q = _largest_prime_power_le(min(d - 1, 9))
        if q is not None and q >= 2:
            out.append(_gq_w(q))
    return out


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D
        return L, [(i, (i + 1) % L) for i in range(L)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}: always valid for D >= 2
    for cand in known_starts(d, D):
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 31 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.9 * time_limit - (time.monotonic() - t0) - 1.0
    if budget <= 0.2:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, budget],
                         stdin_graph=best, timeout=budget + 6)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
