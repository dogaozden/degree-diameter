"""Combined program for D = 3: Haar graphs from difference covers, then augmentation and grow-by-two.

Stage 0: the best known construction (Moore graph, Araujo-Pardo-Lopez graph, or PG(2,q)).
Stage A (D = 3 only): the C engine C_HAAR searches for a subset S of a group G (cyclic or
semidirect Z_a x| Z_b) with S S^{-1} = G. The Haar graph (g,0)~(gs,1) for s in S is d-regular,
bipartite, of order 2|G|, and has diameter at most 3. Larger |G| is better.
Stage B: the augmented best graph is passed to the grow-by-two engine C_SOURCE.

build() always returns a graph that passes lib.is_valid, so a failed C run only costs time.
"""
import itertools
import random
import time

import lib

GQ_Q_MAX = 9      # largest q for which the generalized quadrangle W(q) is built in Python
TIME_FRAC = 0.95  # fraction of time_limit used in total (C stops at 97.5% of its budget)

C_HAAR = r'''
/* Haar-graph search for diameter 3.
 *
 * Group G of order M (semidirect Z_a x| Z_b, cyclic when a = 1 or r = 1), subset S with
 * |S| = d and S S^{-1} = G. The Haar graph (g,0)~(g s,1), s in S, is d-regular bipartite of
 * order 2M and has diameter <= 3 whenever S S^{-1} covers G.
 * Search: fix 0 in S, anneal the number of covered nonzero elements of S S^{-1}.
 * Usage:  prog d D seed time_limit     (stdin is ignored)
 * stdout: "n m" then m lines "u v", or "0 0" if nothing was found.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXM 1024
#define MAXDD 40
#define MAXG 512

static int d;
static double t_end;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

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

/* ------------------------------------------------------------ group tables */

static int M;                 /* group order */
static int mt[MAXM][MAXM];    /* multiplication table, identity 0 */
static int iv[MAXM];          /* inverses */

/* Element (x,y) of Z_a x| Z_b is the int x*b + y; (x,y)(u,v) = (x + r^y u, y + v). */
static void build_group(int a, int b, int r) {
    M = a * b;
    int rp[MAXM];
    rp[0] = 1 % a;
    for (int i = 1; i < b; i++) rp[i] = (int)((long)rp[i - 1] * r % a);
    for (int x = 0; x < M; x++) {
        int xa = x / b, xb = x % b;
        for (int y = 0; y < M; y++) {
            int ya = y / b, yb = y % b;
            mt[x][y] = (int)((xa + (long)rp[xb] * ya) % a) * b + (xb + yb) % b;
        }
    }
    for (int x = 0; x < M; x++)
        for (int y = 0; y < M; y++)
            if (mt[x][y] == 0) { iv[x] = y; break; }
}

/* ------------------------------------------------------------ covering state */

static int S[MAXDD];
static int inS[MAXM];
static int cnt[MAXM];   /* number of ordered pairs (s,t), s != t, with s t^{-1} = g */
static int ncov;        /* number of nonzero g with cnt[g] > 0 */

static void inc_pair(int a, int b) {
    int c1 = mt[a][iv[b]], c2 = mt[b][iv[a]];
    if (cnt[c1]++ == 0) ncov++;
    if (cnt[c2]++ == 0) ncov++;
}

static void dec_pair(int a, int b) {
    int c1 = mt[a][iv[b]], c2 = mt[b][iv[a]];
    if (--cnt[c1] == 0) ncov--;
    if (--cnt[c2] == 0) ncov--;
}

static void replace_at(int i, int y) {
    int x = S[i];
    for (int j = 0; j < d; j++)
        if (j != i) dec_pair(x, S[j]);
    S[i] = y;
    inS[x] = 0;
    inS[y] = 1;
    for (int j = 0; j < d; j++)
        if (j != i) inc_pair(y, S[j]);
}

static void init_random(void) {
    memset(inS, 0, sizeof inS);
    memset(cnt, 0, sizeof cnt);
    ncov = 0;
    S[0] = 0;
    inS[0] = 1;
    for (int i = 1; i < d; i++) {
        int y;
        do { y = 1 + rndint(M - 1); } while (inS[y]);
        S[i] = y;
        inS[y] = 1;
    }
    for (int i = 0; i < d; i++)
        for (int j = i + 1; j < d; j++)
            inc_pair(S[i], S[j]);
}

/* Annealing on the covered count. Returns 1 if S S^{-1} = G was reached before `until`. */
static int sa_search(double until) {
    init_random();
    double T = 0.6;
    long it = 0;
    while (ncov < M - 1) {
        if ((++it & 1023) == 0 && now() > until) return 0;
        int i = 1 + rndint(d - 1);
        int y;
        do { y = 1 + rndint(M - 1); } while (inS[y]);
        int old = S[i], before = ncov;
        replace_at(i, y);
        int after = ncov;
        if (after < before && rnd01() >= exp((double)(after - before) / T))
            replace_at(i, old);
        T *= 0.99995;
        if (T < 0.1) T = 0.6;
    }
    return 1;
}

/* ------------------------------------------------------------ group enumeration */

#define NONE -1
static int ga[MAXG], gb[MAXG], gr[MAXG];

/* All semidirect Z_a x| Z_b of order m (cyclic included). Returns the count. */
static int collect_groups(int m) {
    int ng = 0;
    for (int a = 1; a <= m; a++) {
        if (m % a) continue;
        int b = m / a;
        if (a == 1) {
            if (ng < MAXG) { ga[ng] = 1; gb[ng] = b; gr[ng] = 0; ng++; }
            continue;
        }
        for (int r = 1; r < a; r++) {
            if (gcd(r, a) != 1 || powmod(r, b, a) != 1) continue;
            if (ng < MAXG) { ga[ng] = a; gb[ng] = b; gr[ng] = r; ng++; }
        }
    }
    return ng;
}

static void swap_grp(int i, int j) {
    int t;
    t = ga[i]; ga[i] = ga[j]; ga[j] = t;
    t = gb[i]; gb[i] = gb[j]; gb[j] = t;
    t = gr[i]; gr[i] = gr[j]; gr[j] = t;
}

/* ------------------------------------------------------------ output and check */

static int adjl[2 * MAXM][MAXDD];
static int degl[2 * MAXM];

static int check_diam(int n) {
    static int dist[2 * MAXM], q[2 * MAXM];
    for (int s = 0; s < n; s++) {
        for (int v = 0; v < n; v++) dist[v] = -1;
        int h = 0, t = 0;
        q[t++] = s;
        dist[s] = 0;
        while (h < t) {
            int v = q[h++];
            for (int i = 0; i < degl[v]; i++) {
                int u = adjl[v][i];
                if (dist[u] < 0) { dist[u] = dist[v] + 1; q[t++] = u; }
            }
        }
        for (int v = 0; v < n; v++)
            if (dist[v] < 0 || dist[v] > 3) return 0;
    }
    return 1;
}

/* ------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    int D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit * 0.975;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 3 || D != 3 || d > MAXDD) {
        printf("0 0\n");
        return 0;
    }

    long Mmax = (long)d * (d - 1) + 1;   /* covering bound for |S| = d */
    if (Mmax > MAXM - 1) Mmax = MAXM - 1;
    long mstart = Mmax / 2;
    if (mstart < d + 1) mstart = d + 1;

    int bestM = 0, bestA = 0, bestB = 0, bestR = 0;
    int bestS[MAXDD];
    int fails = 0;

    for (long m = mstart; m <= Mmax && now() < t_end; m++) {
        int ng = collect_groups((int)m);
        if (ng == 0) { fails++; if (fails >= 3) break; continue; }
        for (int i = ng - 1; i > 0; i--) swap_grp(i, rndint(i + 1));
        for (int i = 0; i < ng; i++)
            if (ga[i] == (int)m) { swap_grp(0, i); break; }   /* cyclic group first */

        double remain = t_end - now();
        double slice = remain * 0.08;
        if (slice < 0.5) slice = 0.5;
        if (slice > 8.0) slice = 8.0;
        int tries = ng < 6 ? ng : 6;

        int found = 0;
        for (int t = 0; t < tries && !found && now() < t_end; t++) {
            double per = slice / tries;
            if (per < 0.2) per = 0.2;
            double until = now() + per;
            if (until > t_end) until = t_end;
            build_group(ga[t], gb[t], gr[t]);
            if (sa_search(until)) {
                found = 1;
                bestM = (int)m;
                bestA = ga[t];
                bestB = gb[t];
                bestR = gr[t];
                memcpy(bestS, S, sizeof(int) * (size_t)d);
            }
        }
        if (found) fails = 0;
        else if (++fails >= 3) break;
    }

    if (bestM == 0) {
        printf("0 0\n");
        return 0;
    }

    build_group(bestA, bestB, bestR);
    int n = 2 * M;
    memset(degl, 0, sizeof degl);
    for (int g = 0; g < M; g++) {
        for (int i = 0; i < d; i++) {
            int u = g, v = M + mt[g][bestS[i]];
            adjl[u][degl[u]++] = v;
            adjl[v][degl[v]++] = u;
        }
    }
    if (!check_diam(n)) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", n, M * d);
    for (int g = 0; g < M; g++)
        for (int i = 0; i < d; i++)
            printf("%d %d\n", g, M + mt[g][bestS[i]]);
    return 0;
}
'''

C_SOURCE = r'''
/* Bipartite degree-diameter search core.
 *
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v": a valid starting graph, or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * Search:
 *   1. Voltage lifts over semidirect products Z_m x| Z_k (short slice when a start exists).
 *   2. Grow by two: insert one vertex per side, then repair until every pair is within distance D.
 *      Insertion mode bit 2: greedy slot selection (each slot picks the rewired edge among a
 *      small candidate set that minimises the bad-pair count) instead of random selection.
 *      Repair mode bit 1: tabu search (batch of targeted swaps, best non-tabu applied) instead
 *      of annealing over random/targeted swaps.
 *      A targeted swap joins a bad-pair vertex v to a vertex t that lies within distance 1
 *      (same side) or 2 (opposite side) of its unreached partner w.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 4096
#define MAXD 32
#define MAXW (MAXN / 64)
#define MAXP 4

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

/* Largest possible order of a bipartite graph with max degree d and diameter D. */
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
/* Reach balls of the most recent bad_pairs call: bit w of ball v is set iff dist(v,w) <= D. */
static uint64_t *final_reach = RA;
static int final_W = 0;

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
    final_reach = cur;
    final_W = W;
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

/* True if dist(v, w) <= D according to the last bad_pairs call. */
static int reached(int v, int w) {
    return (int)((final_reach[(size_t)v * final_W + w / 64] >> (w % 64)) & 1ULL);
}

/* Full validity: simple, bipartite (by side labels), degree <= d, diameter <= D. */
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

/* K_{d,d}: always valid for D >= 2. */
static void complete_bipartite(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= d; }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

/* ------------------------------------------------------------------ groups */

/* Z_m x|_r Z_k: element (a, b) is the int a*k + b, (a,b)(c,e) = (a + r^b c mod m, b + e mod k). */
typedef struct {
    int m, k, r;
    int rp[MAXN];
} Grp;

static int gmul(const Grp *G, int x, int y) {
    int a = x / G->k, b = x % G->k, c = y / G->k, e = y % G->k;
    return (int)((a + (long)G->rp[b] * c) % G->m) * G->k + (b + e) % G->k;
}

/* Uniformly random (m, k, r) with m*k = N, gcd(r, m) = 1 and r^k = 1 mod m. */
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

/* ------------------------------------------------------------------ voltage lifts */

typedef struct { int i, j, g; } Dart;

/* Random d-regular bipartite base multigraph with p vertices per side, connected. */
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

static void build_lift(Graph *g, int p, int N, const Grp *G, const Dart *dt, int nd) {
    g->n = 2 * p * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= p * N; }
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, dt[t].i * N + x, p * N + dt[t].j * N + gmul(G, x, dt[t].g));
}

static int fresh_voltage(const Dart *dt, int nd, int skip, int i, int j, int N) {
    for (;;) {
        int g = rndint(N), clash = 0;
        for (int t = 0; t < nd; t++)
            if (t != skip && dt[t].i == i && dt[t].j == j && dt[t].g == g) { clash = 1; break; }
        if (!clash) return g;
    }
}

static int lift_try(Graph *g, int p, int N, const Grp *G, int steps) {
    int M[MAXP][MAXP];
    Dart dt[MAXD * MAXP];
    int nd = 0;
    make_base(p, M);
    for (int i = 0; i < p; i++)
        for (int j = 0; j < p; j++)
            for (int c = 0; c < M[i][j]; c++) {
                dt[nd].i = i; dt[nd].j = j;
                dt[nd].g = c == 0 ? 0 : fresh_voltage(dt, nd, -1, i, j, N);
                nd++;
            }
    build_lift(g, p, N, G, dt, nd);
    long bad = bad_pairs(g);
    for (int s = 0; s < steps && bad > 0; s++) {
        if ((s & 15) == 0 && now() > t_end) return 0;
        int t = rndint(nd);
        int old = dt[t].g;
        dt[t].g = fresh_voltage(dt, nd, t, dt[t].i, dt[t].j, N);
        build_lift(g, p, N, G, dt, nd);
        long nb = bad_pairs(g);
        if (nb <= bad || rnd01() < 0.01) bad = nb;
        else dt[t].g = old;
    }
    return bad == 0;
}

static void lift_search(Graph *best, double until) {
    static Graph cand;
    static Grp G;
    long moore = moore_bound();
    int fails = 0;
    while (now() < until) {
        int r = rndint(10);
        int p = r < 4 ? 1 : r < 7 ? 2 : r < 9 ? 3 : 4;
        long target = best->n + 2;
        if (target > moore) return;
        int N = (int)((target + 2 * p - 1) / (2 * p)) + rndint(2);
        if (best->n == 0) N = d + rndint(3);
        if (N < d || 2L * p * N > moore || 2 * p * N > MAXN) {
            if (++fails > 1000) return;
            continue;
        }
        if (!random_group(N, &G)) continue;
        int steps = 200 + 400000 / (2 * p * N);
        if (lift_try(&cand, p, N, &G, steps) && cand.n > best->n && is_valid(&cand))
            copy_graph(best, &cand);
    }
}

/* ------------------------------------------------------------------ grow by two */

/* Propose a degree-preserving swap (v,u),(s,t) -> (v,t),(s,u) with side(v) != side(t) and
 * side(s) == side(v). Random mode picks s uniformly; targeted mode picks t near an unreached
 * partner w of v (distance 1 if w is on v's side, 2 otherwise), so v gets a short route to w. */
static int propose(const Graph *g, int v, int *pu, int *ps, int *pt, int targeted) {
    int n = g->n;
    int u, s, t;
    if (g->deg[v] == 0) return 0;
    u = g->adj[v][rndint(g->deg[v])];
    if (!targeted) {
        s = rndint(n);
        if (g->side[s] != g->side[v] || g->deg[s] == 0) return 0;
        t = g->adj[s][rndint(g->deg[s])];
    } else {
        int w = -1;
        for (int tries = 0; tries < 64; tries++) {
            int c = rndint(n);
            if (c != v && !reached(v, c)) { w = c; break; }
        }
        if (w < 0) return 0;
        int L = g->side[w] == g->side[v] ? 1 : 2;
        t = w;
        for (int k = 0; k < L; k++) {
            if (g->deg[t] == 0) return 0;
            t = g->adj[t][rndint(g->deg[t])];
        }
        if (g->deg[t] == 0) return 0;
        s = g->adj[t][rndint(g->deg[t])];
    }
    if (s == v || t == u || g->side[t] == g->side[v] || g->side[s] != g->side[v]) return 0;
    if (has_edge(g, v, t) || has_edge(g, s, u)) return 0;
    *pu = u; *ps = s; *pt = t;
    return 1;
}

/* Apply the swap, accept or revert by the annealing rule. Returns the bad-pair count of the
 * resulting graph; badv and the reach balls are refreshed for whichever state is kept. */
static long apply_swap(Graph *work, int v, int u, int s, int t, long bad, double T) {
    del_edge(work, v, u);
    del_edge(work, s, t);
    add_edge(work, v, t);
    add_edge(work, s, u);
    long nb = bad_pairs(work);
    if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) return nb;
    del_edge(work, v, t);
    del_edge(work, s, u);
    add_edge(work, v, u);
    add_edge(work, s, t);
    bad_pairs(work);
    return bad;
}

/* Tabu repair. Each step samples a batch of swaps at bad vertices, scores each by its bad-pair
 * count, and applies the best one whose endpoints are not tabu, even when it does not improve.
 * The four endpoints of the applied swap are tabu for a short tenure, which stops the search
 * from undoing its last move. The best state seen is restored at the end. Returns 1 if the
 * final state has no bad pairs. */
static long tabu_mark[MAXN];

static int tabu_repair(Graph *work, long bad, double until) {
    static Graph bestg;
    const int K = 24, tenure = 7;
    long bestbad = bad;
    long it = 1;
    memset(tabu_mark, 0, sizeof(long) * (size_t)work->n);
    copy_graph(&bestg, work);
    while (bad > 0) {
        if ((it & 7) == 0 && now() > until) break;
        long cbest = -1;
        int bv = 0, bu = 0, bs = 0, bt = 0;
        for (int c = 0; c < K; c++) {
            int v = rndint(work->n);
            for (int tries = 0; tries < 30 && badv[v] == 0; tries++) v = rndint(work->n);
            int u, s, t;
            if (!propose(work, v, &u, &s, &t, rndint(3) != 0)) continue;
            if (tabu_mark[v] > it || tabu_mark[s] > it || tabu_mark[t] > it || tabu_mark[u] > it)
                continue;
            del_edge(work, v, u);
            del_edge(work, s, t);
            add_edge(work, v, t);
            add_edge(work, s, u);
            long nb = bad_pairs(work);
            del_edge(work, v, t);
            del_edge(work, s, u);
            add_edge(work, v, u);
            add_edge(work, s, t);
            bad_pairs(work);
            if (cbest < 0 || nb < cbest) { cbest = nb; bv = v; bu = u; bs = s; bt = t; }
        }
        it++;
        if (cbest < 0) continue;
        del_edge(work, bv, bu);
        del_edge(work, bs, bt);
        add_edge(work, bv, bt);
        add_edge(work, bs, bu);
        bad = bad_pairs(work);
        long stamp = it + tenure;
        tabu_mark[bv] = stamp;
        tabu_mark[bs] = stamp;
        tabu_mark[bt] = stamp;
        tabu_mark[bu] = stamp;
        if (bad < bestbad) {
            bestbad = bad;
            copy_graph(&bestg, work);
        }
    }
    copy_graph(work, &bestg);
    bad_pairs(work);
    return bestbad == 0;
}

/* Shared marks for the vertices already used in one insertion. */
static int used_mark[MAXN];
static int used_stamp = 0;

/* Greedy slot selection. The new vertices x (side 0) and y (side 1) are already joined. Each of
 * the d-1 remaining slots takes an edge (a,b), a on side 0 and b on side 1, which is rewired to
 * x-b and y-a. A small candidate set is collected per slot and the candidate giving the fewest
 * bad pairs after the rewiring is committed. Returns 0 if no candidate exists. */
static int greedy_insert(Graph *work, int n, int x, int y) {
    int stamp = ++used_stamp;
    used_mark[x] = used_mark[y] = stamp;
    for (int slot = 0; slot < d - 1; slot++) {
        int ca[8], cb[8], nc = 0;
        for (int tries = 0; tries < 4000 && nc < 8; tries++) {
            int a = rndint(n);
            if (work->side[a] != 0 || used_mark[a] == stamp || work->deg[a] == 0) continue;
            int b = work->adj[a][rndint(work->deg[a])];
            if (b >= n || used_mark[b] == stamp) continue;
            ca[nc] = a;
            cb[nc] = b;
            nc++;
        }
        if (nc == 0) return 0;
        long bestv = -1;
        int bi = 0;
        for (int c = 0; c < nc; c++) {
            int a = ca[c], b = cb[c];
            del_edge(work, a, b);
            add_edge(work, x, b);
            add_edge(work, y, a);
            long nb = bad_pairs(work);
            del_edge(work, x, b);
            del_edge(work, y, a);
            add_edge(work, a, b);
            if (bestv < 0 || nb < bestv) { bestv = nb; bi = c; }
        }
        int a = ca[bi], b = cb[bi];
        del_edge(work, a, b);
        add_edge(work, x, b);
        add_edge(work, y, a);
        used_mark[a] = used_mark[b] = stamp;
    }
    bad_pairs(work);
    return 1;
}

/* Insert one vertex per side, then repair. mode bit 2: greedy insertion (else random rewiring of
 * d-1 edges). mode bit 1: tabu repair (else annealing). */
static int grow_once(const Graph *best, Graph *work, double until, int mode) {
    int n = best->n;
    if (n + 2 > moore_bound() || n + 2 > MAXN) return 0;
    copy_graph(work, best);
    int x = n, y = n + 1;
    work->n = n + 2;
    work->deg[x] = work->deg[y] = 0;
    work->side[x] = 0;
    work->side[y] = 1;
    add_edge(work, x, y);
    if (mode & 2) {
        if (!greedy_insert(work, n, x, y)) return 0;
    } else {
        int stamp = ++used_stamp;
        used_mark[x] = used_mark[y] = stamp;
        for (int k = 0, tries = 0; k < d - 1 && tries < 100000; tries++) {
            int a = rndint(n);
            if (work->side[a] != 0 || used_mark[a] == stamp || work->deg[a] == 0) continue;
            int b = work->adj[a][rndint(work->deg[a])];
            if (used_mark[b] == stamp || b >= n) continue;
            del_edge(work, a, b);
            add_edge(work, x, b);
            add_edge(work, y, a);
            used_mark[a] = used_mark[b] = stamp;
            k++;
        }
    }
    long bad = bad_pairs(work);
    if (mode & 1) {
        tabu_repair(work, bad, until);
    } else {
        double T = 1.0;
        long it = 0;
        while (bad > 0) {
            if ((++it & 15) == 0 && now() > until) return 0;
            int v = rndint(work->n);
            for (int tries = 0; tries < 30 && badv[v] == 0; tries++) v = rndint(work->n);
            int u, s, t;
            int targeted = rndint(3) != 0;   /* two thirds of proposals are targeted */
            if (!propose(work, v, &u, &s, &t, targeted)) continue;
            bad = apply_swap(work, v, u, s, t, bad, T);
            T *= 0.9995;
            if (T < 0.05) T = 1.0;
        }
    }
    return is_valid(work);
}

/* Keep the (insertion, repair) mode that last succeeded; cycle through the four modes after
 * each failed attempt. */
static void grow_search(Graph *best, double until) {
    static Graph work;
    int mode = 0;
    while (now() < until && best->n + 2 <= moore_bound()) {
        double left = until - now();
        double slice = left < 4.0 ? left : (left / 2 > 4.0 ? left / 2 : 4.0);
        if (grow_once(best, &work, now() + slice, mode)) {
            copy_graph(best, &work);
        } else {
            mode = (mode + 1) & 3;
        }
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
    t_end = t0 + limit * 0.975;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best;
    if (d < 1 || D < 1 || d > MAXD) { complete_bipartite(&best); print_graph(&best); return 0; }
    read_start(&best);
    int had_start = best.n > 0;

    if (D >= 2 && best.n < moore_bound()) {
        /* With a valid start, all time goes to grow-by-two; lifts are only used from scratch. */
        double lift_share = had_start ? 0.0 : 0.6;
        lift_search(&best, t0 + (t_end - t0) * lift_share);
        if (best.n > 0) grow_search(&best, t_end);
    }
    if (best.n == 0) complete_bipartite(&best);
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


# ---------------------------------------------------------------- helpers

def _two_colour(n, edges):
    """Proper 2-colouring of a bipartite graph, component by component."""
    adj = lib.adjacency(n, edges)
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


def _augment(n, edges, d, seed):
    """Add edges between opposite colour classes using spare degree (keeps bipartite, shrinks distances)."""
    rng = random.Random(seed + 7)
    color = _two_colour(n, edges)
    deg = [0] * n
    adj = [set() for _ in range(n)]
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
        adj[u].add(v)
        adj[v].add(u)
    side0 = [u for u in range(n) if color[u] == 0]
    side1 = [v for v in range(n) if color[v] == 1]
    new_edges = list(edges)
    for _ in range(3):
        us = [u for u in side0 if deg[u] < d]
        rng.shuffle(us)
        for u in us:
            if deg[u] >= d:
                continue
            cands = [v for v in side1 if deg[v] < d and v not in adj[u]]
            if not cands:
                continue
            v = rng.choice(cands)
            adj[u].add(v)
            adj[v].add(u)
            deg[u] += 1
            deg[v] += 1
            new_edges.append((u, v))
    return n, new_edges


def _pg_base(d):
    """Incidence graph of PG(2,q), q the largest prime power <= d-1."""
    q = d - 1
    while q >= 2 and not lib.is_prime_power(q):
        q -= 1
    if q < 2:
        return None
    return lib.projective_plane_incidence(q)


def _gq_w(q):
    """Point-line incidence graph of the generalized quadrangle W(q): degree q+1, diameter 4."""
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
    """W(q) for the largest prime power q <= min(d-1, GQ_Q_MAX)."""
    for q in range(min(d - 1, GQ_Q_MAX), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def known_start(d, D):
    """Best known construction for (d, D) that Python can build directly, or None."""
    if D == 3:
        if lib.is_prime_power(d - 1):
            return lib.projective_plane_incidence(d - 1)     # Moore graph
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            return lib.araujo_lopez_graph(d - 2)             # record 2(q^2+q+5), q = d-2
        return _pg_base(d)                                   # fallback: PG(2,q), q < d-1
    if D >= 4:
        return _best_gq(d)                                   # diameter 4 <= D
    return None


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    t0 = time.monotonic()

    def left():
        """Seconds still available for C work, leaving a margin for overheads."""
        return TIME_FRAC * time_limit - (time.monotonic() - t0) - 1.0

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    kdd = lib.haar_graph(d, range(d))          # K_{d,d}: diameter 2, always valid
    if D == 2:
        return kdd

    best = None
    try:
        best = known_start(d, D)
    except Exception:
        best = None
    if best is None or not lib.is_valid(best[0], best[1], d, D):
        best = kdd

    if best[0] >= lib.moore_bound(d, D):
        return best                            # Moore graph: nothing to search for

    # Stage A (D = 3): Haar graphs from difference covers of groups of order M, graph order 2M.
    if D == 3 and d >= 3 and left() > 2.0:
        budget = round(0.5 * left(), 2)
        try:
            text = lib.run_c(C_HAAR, [d, D, seed, budget], stdin_graph=None, timeout=budget + 2)
            n, e = lib.parse_graph_text(text)
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
        except Exception:
            pass                               # keep the current best

    # Stage B: augment with spare degree, then grow by two from the best graph so far.
    start = best
    try:
        aug = _augment(best[0], best[1], d, seed)
        if lib.is_valid(aug[0], aug[1], d, D):
            start = aug
    except Exception:
        start = best

    budget = left()
    if budget > 1.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             stdin_graph=start, timeout=budget + 2)
            n, e = lib.parse_graph_text(text)
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
        except Exception:
            pass                               # keep the valid construction
    return best
