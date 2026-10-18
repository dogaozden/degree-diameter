"""Bi-Cayley search over metacyclic groups for bipartite degree-diameter graphs.

Stage 1 (new): for d >= 3, look for graphs on G x {0,1} (|G| = N, S = {e, s_2, ..., s_d}),
with edges (x,0)--(x*s,1). Left multiplication by G is an automorphism of each side,
so the diameter check needs only two BFS runs. Groups are semidirect products Z_m x| Z_k.
Stage 2 (old engine): the original search, started from the best graph so far.
Every stage keeps the best valid graph, so a failure only costs time.
"""
import time

import lib

C_BICAYLEY = r'''
/* Bi-Cayley search: vertices (x,0) = x and (y,1) = N + y for a group G of order N.
 * S = {s_1 = e, s_2, ..., s_d} (distinct), edges x -- N + x*s.
 * Left multiplication by G is an automorphism of each side, so
 *   diameter <= D  iff  BFS from (e,0) and from (e,1) reach everything within D.
 * Usage: prog d D seed time_limit [goal] [start_n]
 * stdout: "n m" + edges of the largest verified graph with n > start_n, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXH 512
#define MAXDEG 16
#define MAXV (2 * MAXH)
#define MAXGROUPS 4096

static int d, D;
static double t_end;
static int N;
static int MT[MAXH][MAXH];
static int INV[MAXH];
static int RP[MAXH];
static int SS[MAXDEG];

typedef struct { int m, k, r; } GDesc;
static GDesc groups[MAXGROUPS];
static int ngroups;

static GDesc found_g;
static int found_N = 0;
static int found_S[MAXDEG];

static int DIST[MAXV], QUE[MAXV];
static int ADJ[MAXV][MAXDEG];
static int DEGX[MAXV];

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

/* Multiplication table for Z_m x|_r Z_k, element (a,b) = a*k + b. */
static void build_group(GDesc g) {
    int m = g.m, k = g.k, r = g.r;
    N = m * k;
    RP[0] = 1 % m;
    for (int b = 1; b < k; b++) RP[b] = (int)((long)RP[b - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            MT[x][y] = (int)(((a + (long)RP[b] * c) % m) * k + (b + e) % k);
        }
    }
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (MT[x][y] == 0) { INV[x] = y; break; }
}

/* All semidirect groups of order n, in random order. */
static void enum_groups(int n) {
    ngroups = 0;
    for (int m = 1; m <= n; m++) {
        if (n % m) continue;
        int k = n / m;
        if (m == 1) {
            if (ngroups < MAXGROUPS) groups[ngroups++] = (GDesc){1, k, 0};
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            if (ngroups < MAXGROUPS) groups[ngroups++] = (GDesc){m, k, r};
        }
    }
    for (int i = ngroups - 1; i > 0; i--) {
        int j = rndint(i + 1);
        GDesc t = groups[i];
        groups[i] = groups[j];
        groups[j] = t;
    }
}

/* Fast test: BFS from (e,0) and from (e,1) using implicit neighbours. */
static int reach_ok(int src) {
    int tot = 2 * N;
    for (int i = 0; i < tot; i++) DIST[i] = -1;
    int h = 0, t = 0;
    DIST[src] = 0;
    QUE[t++] = src;
    while (h < t) {
        int v = QUE[h++];
        if (DIST[v] >= D) continue;
        for (int i = 0; i < d; i++) {
            int s = SS[i];
            int u = v < N ? N + MT[v][s] : MT[v - N][INV[s]];
            if (DIST[u] < 0) {
                DIST[u] = DIST[v] + 1;
                QUE[t++] = u;
            }
        }
    }
    return t == tot;
}

/* Full explicit verification: build adjacency, check degrees, simplicity, all-pairs distance. */
static int verify_explicit(void) {
    int tot = 2 * N;
    for (int v = 0; v < tot; v++) DEGX[v] = 0;
    for (int x = 0; x < N; x++)
        for (int i = 0; i < d; i++) {
            int u = N + MT[x][SS[i]];
            if (DEGX[x] >= MAXDEG || DEGX[u] >= MAXDEG) return 0;
            ADJ[x][DEGX[x]++] = u;
            ADJ[u][DEGX[u]++] = x;
        }
    for (int v = 0; v < tot; v++) {
        if (DEGX[v] != d) return 0;
        for (int i = 0; i < d; i++)
            for (int j = 0; j < i; j++)
                if (ADJ[v][i] == ADJ[v][j]) return 0;
    }
    for (int src = 0; src < tot; src++) {
        for (int v = 0; v < tot; v++) DIST[v] = -1;
        int h = 0, t = 0;
        DIST[src] = 0;
        QUE[t++] = src;
        while (h < t) {
            int v = QUE[h++];
            if (DIST[v] >= D) continue;
            for (int i = 0; i < d; i++) {
                int u = ADJ[v][i];
                if (DIST[u] < 0) {
                    DIST[u] = DIST[v] + 1;
                    QUE[t++] = u;
                }
            }
        }
        if (t != tot) return 0;
    }
    return 1;
}

/* Try to find a valid bi-Cayley graph of order 2n within the deadline. */
static int search_N(int n, double until) {
    enum_groups(n);
    for (int gi = 0; gi < ngroups; gi++) {
        if (now() > until) return 0;
        build_group(groups[gi]);
        if (d == 3) {
            /* exhaustive over S = {e, a, b} */
            SS[0] = 0;
            for (int a = 1; a < N; a++) {
                if (now() > until) return 0;
                for (int b = a + 1; b < N; b++) {
                    SS[1] = a;
                    SS[2] = b;
                    if (reach_ok(0) && reach_ok(N) && verify_explicit()) {
                        found_N = N;
                        found_g = groups[gi];
                        memcpy(found_S, SS, sizeof SS);
                        return 1;
                    }
                }
            }
        } else {
            /* random S = {e, s_2, ..., s_d} */
            for (long tr = 0; tr < 20000; tr++) {
                if ((tr & 1023) == 0 && now() > until) return 0;
                SS[0] = 0;
                for (int i = 1; i < d; i++) {
                    int c, dup;
                    do {
                        c = 1 + rndint(N - 1);
                        dup = 0;
                        for (int j = 0; j < i; j++)
                            if (SS[j] == c) dup = 1;
                    } while (dup);
                    SS[i] = c;
                }
                if (reach_ok(0) && reach_ok(N) && verify_explicit()) {
                    found_N = N;
                    found_g = groups[gi];
                    memcpy(found_S, SS, sizeof SS);
                    return 1;
                }
            }
        }
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [goal] [start_n]\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int goal = argc > 5 ? atoi(argv[5]) : 0;
    int start_n = argc > 6 ? atoi(argv[6]) : 0;
    double t0 = now();
    t_end = t0 + limit * 0.92;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 3 || d > MAXDEG - 1 || D < 2) {
        printf("0 0\n");
        return 0;
    }
    long moore = moore_bound();
    long maxN = moore / 2;
    if (maxN > MAXH - 1) maxN = MAXH - 1;
    long lo = start_n / 2 + 1;
    if (goal / 2 > lo) lo = goal / 2;   /* first try to match the record order */
    if (lo < d) lo = d;

    for (long n = lo; n <= maxN && now() < t_end; n++) {
        double left = t_end - now();
        double slice = left / 6.0;
        if (slice < 1.0) slice = 1.0;
        double until = now() + slice;
        if (until > t_end) until = t_end;
        search_N((int)n, until);
    }

    if (found_N == 0) {
        printf("0 0\n");
        return 0;
    }
    build_group(found_g);
    memcpy(SS, found_S, sizeof SS);
    if (!verify_explicit()) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", 2 * N, N * d);
    for (int x = 0; x < N; x++)
        for (int i = 0; i < d; i++)
            printf("%d %d\n", x, N + MT[x][SS[i]]);
    return 0;
}
'''

C_SOURCE = r'''
/* Bipartite degree-diameter search core.
 *
 * Usage:   prog d D seed time_limit [goal]   < start_graph
 * stdin:   "n m" then m lines "u v": a known-valid starting graph, or "0 0" for none.
 * goal:    optional known record order; lift search sometimes aims straight at it.
 * stdout:  "n m" then m lines "u v": the largest valid graph found
 *          (bipartite, every degree <= d, every pair of vertices within D steps).
 *
 * Search, in order:
 *   1. Voltage lifts over groups Z_m x| Z_k (semidirect products), with hill-climbing on
 *      the voltages. A lift of a d-regular base multigraph with p vertices per side over a
 *      group of order N has 2pN vertices and is bipartite and d-regular automatically.
 *      Group orders are drawn with a jitter proportional to N. Half of the draws aim at
 *      the record goal (when given) instead of only best + 2, so big lifts are tried early.
 *   2. Grow by two ("squeeze past the record"): take the best graph, insert one new vertex
 *      on each side using the spare degree of d-1 deleted edges, then anneal degree-preserving
 *      edge swaps until no pair is farther than D apart.
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
    unsigned char side[MAXN]; /* 0 = part A, 1 = part B */
} Graph;

static int d, D;
static double t_end;
static long goal_n = 0;

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
static int badv[MAXN]; /* badv[v] = vertices farther than D from v, after bad_pairs() */

/* Number of unordered pairs at distance > D (0 means connected with diameter <= D).
 * Bitset reachability: after r rounds, row v holds every vertex within r steps of v. */
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

/* Full validity check: simple, bipartite (by side labels), degree <= d, diameter <= D. */
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

/* Read "n m" + edges from stdin; 2-colour it. Leaves g->n = 0 if absent or invalid. */
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
    int rp[MAXN]; /* rp[b] = r^b mod m */
} Grp;

static int gmul(const Grp *G, int x, int y) {
    int a = x / G->k, b = x % G->k, c = y / G->k, e = y % G->k;
    return (int)((a + (long)G->rp[b] * c) % G->m) * G->k + (b + e) % G->k;
}

/* Pick a uniformly random (m, k, r) with m*k = N, gcd(r, m) = 1 and r^k = 1 mod m. */
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

typedef struct { int i, j, g; } Dart; /* base A-vertex i -> base B-vertex j, voltage g */

/* Random d-regular bipartite base multigraph with p vertices per side (sum of d random
 * permutation matrices), retried until connected. M[i][j] = number of darts i -> j. */
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

/* A voltage not used by any other dart between the same pair of base vertices. */
static int fresh_voltage(const Dart *dt, int nd, int skip, int i, int j, int N) {
    for (;;) {
        int g = rndint(N), clash = 0;
        for (int t = 0; t < nd; t++)
            if (t != skip && dt[t].i == i && dt[t].j == j && dt[t].g == g) { clash = 1; break; }
        if (!clash) return g;
    }
}

/* One hill-climb over the voltages of a random base graph and group of order N.
 * On success g holds a valid lift with 2pN vertices. */
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
    if (bad != 0) return 0;
    return 1; /* g was built from the accepted voltages */
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
        /* Half of the draws aim straight at the known record order (if one was given),
         * so lifts of record size are tried, not only steps of +2. */
        if (goal_n > target && rndint(2) == 0) target = goal_n;
        if (target > moore) return;
        /* Jitter grows with the group order, so bigger groups are tried as well. */
        int base_N = (int)((target + 2 * p - 1) / (2 * p));
        int jitter = 2 + base_N / 16;
        int N = base_N + rndint(jitter);
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

/* Insert one new vertex per side into a copy of best (degree d each), then anneal edge swaps.
 * Returns 1 if work ends valid with best->n + 2 vertices. */
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
        /* first edge: at a vertex that is too far from something (most of the time) */
        int v = rndint(work->n);
        for (int tries = 0; tries < 30 && badv[v] == 0; tries++) v = rndint(work->n);
        if (work->deg[v] == 0) continue;
        int u = work->adj[v][rndint(work->deg[v])];
        /* second edge: any edge from another vertex on v's side */
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

/* ------------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [goal] < start_graph\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    goal_n = argc > 5 ? atol(argv[5]) : 0;
    double t0 = now();
    t_end = t0 + limit * 0.92;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best;
    if (d < 1 || D < 1 || d > MAXD) { complete_bipartite(&best); print_graph(&best); return 0; }
    read_start(&best);
    int had_start = best.n > 0;

    if (D >= 2 && best.n < moore_bound()) {
        double lift_share = had_start ? 0.2 : 0.6;
        lift_search(&best, t0 + (t_end - t0) * lift_share);
        if (best.n > 0) grow_search(&best, t_end);
    }
    if (best.n == 0) complete_bipartite(&best);
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''

# Known record orders, passed to the C engines as a search goal.
RECORD_GOAL = {(3, 9): 506}


def known_start(d, D):
    """Best graph Python can build directly for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)           # record graphs of order 2(q^2+q+5)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    start = known_start(d, D)
    best = start if start is not None else lib.haar_graph(d, range(d))   # K_{d,d}: always valid
    if best[0] >= lib.moore_bound(d, D):
        return best   # Moore graph: optimal, nothing to search

    def left():
        return 0.85 * time_limit - (time.monotonic() - t0) - 1.0

    goal = RECORD_GOAL.get((d, D), 0)

    # Stage 1: bi-Cayley search over metacyclic groups (new, bold construction).
    if d >= 3 and D >= 2 and left() > 3.0:
        budget = 0.7 * left()
        try:
            text = lib.run_c(C_BICAYLEY, [d, D, seed, budget, goal, best[0]],
                             timeout=budget + 5)
            cand = lib.parse_graph_text(text)
            if cand[0] > best[0] and lib.is_valid(*cand, d, D):
                best = cand
        except (RuntimeError, ValueError):
            pass

    # Stage 2: original lift and grow search from the best graph so far.
    budget = left()
    if budget > 0.2:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, budget, goal], stdin_graph=best,
                             timeout=budget + 5)
            cand = lib.parse_graph_text(text)
            if cand[0] > best[0] and lib.is_valid(*cand, d, D):
                best = cand
        except (RuntimeError, ValueError):
            pass
    return best
