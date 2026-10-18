"""Two-stage search for the degree-diameter target.

Stage 1 (new): Haar graphs of semidirect products Z_m x| Z_k. A Haar graph over a group G
with connection set S (|S| = d, identity in S) has 2|G| vertices, is d-regular and
bipartite, and has left-multiplication symmetry on each side. So diameter <= D only needs two
BFS runs, one from each side. The search scans group orders upward from record/2 + 1 and
keeps the largest order that works. Orders past 254 give more than 506 vertices.

Stage 2 (kept as a safe fallback): the voltage-lift and grow-by-two engine from the parent.

Every candidate is checked with lib.is_valid before it is kept. The best valid graph wins,
so a failed stage can only cost time.
"""
import time

import lib

# Parent engine: voltage lifts over semidirect groups, then grow-by-two. Unchanged.
C_PARENT = r'''
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

# New engine: Haar graphs H(G, S) over semidirect products G = Z_m x| Z_k.
# Vertices a_x = x (side 0), b_y = N + y (side 1); edges a_x -- b_{x*s} for s in S.
# Left multiplication is an automorphism of each side, so checking diameter from a_0 and b_0
# is enough. Normalised so the identity lies in S (right-multiplying S is an isomorphism).
C_HAAR = r'''
#define _POSIX_C_SOURCE 200809L
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXG 1024
#define MAXT 60000
#define MAXDD 8

static int d, D;
static double t_end;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
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

/* All groups Z_m x|_r Z_k of order N (r^k = 1 mod m, gcd(r, m) = 1). */
typedef struct { int m, k, r; } Tup;
static Tup tups[MAXT];
static int ntup;

static void enum_tuples(int N) {
    ntup = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        if (m == 1) {
            if (ntup < MAXT) { tups[ntup].m = 1; tups[ntup].k = k; tups[ntup].r = 0; ntup++; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            if (ntup < MAXT) { tups[ntup].m = m; tups[ntup].k = k; tups[ntup].r = r; ntup++; }
        }
    }
}

/* Current group: element (a, b) is a*gk + b. */
static int gm, gk, gN;
static int rp[MAXG];

static void set_group(int m, int k, int r) {
    gm = m;
    gk = k;
    gN = m * k;
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
}

static int gmul(int x, int y) {
    int a = x / gk, b = x % gk, c = y / gk, e = y % gk;
    return (int)(((long)a + (long)rp[b] * c) % gm) * gk + (b + e) % gk;
}

/* Inverse of (a, b) is (-r^(k-b) a, k-b). */
static int ginv(int x) {
    int a = x / gk, b = x % gk;
    int nb = (gk - b) % gk;
    long t = (long)rp[nb] * a % gm;
    int ia = (int)((gm - t) % gm);
    return ia * gk + nb;
}

static int Sg[MAXDD];
static int Rt[MAXDD][MAXG]; /* Rt[i][x] = x * s_i : b-neighbour (base index) of a_x */
static int Lt[MAXDD][MAXG]; /* Lt[i][y] = y * s_i^{-1} : a-neighbour (base index) of b_y */
static int dist_[2 * MAXG], queue_[2 * MAXG];

static void make_tables(void) {
    for (int i = 0; i < d; i++) {
        int si = ginv(Sg[i]);
        for (int x = 0; x < gN; x++) {
            Rt[i][x] = gmul(x, Sg[i]);
            Lt[i][x] = gmul(x, si);
        }
    }
}

/* BFS from src (0..gN-1 = a side, gN..2gN-1 = b side): 1 iff every vertex is within D. */
static int bfs_ok(int src) {
    int V = 2 * gN;
    for (int v = 0; v < V; v++) dist_[v] = -1;
    int h = 0, t = 0;
    queue_[t++] = src;
    dist_[src] = 0;
    while (h < t) {
        int v = queue_[h++];
        if (dist_[v] >= D) continue;
        if (v < gN) {
            for (int i = 0; i < d; i++) {
                int u = gN + Rt[i][v];
                if (dist_[u] < 0) { dist_[u] = dist_[v] + 1; queue_[t++] = u; }
            }
        } else {
            int y = v - gN;
            for (int i = 0; i < d; i++) {
                int u = Lt[i][y];
                if (dist_[u] < 0) { dist_[u] = dist_[v] + 1; queue_[t++] = u; }
            }
        }
    }
    return t == V;
}

static int haar_valid(void) {
    make_tables();
    return bfs_ok(0) && bfs_ok(gN);
}

/* Random connection set {0, s_1, ..., s_{d-1}} with distinct nonzero s_i. */
static void pick_set(int N) {
    Sg[0] = 0;
    for (int i = 1; i < d; i++) {
        int s, ok;
        do {
            s = 1 + rndint(N - 1);
            ok = 1;
            for (int j = 0; j < i; j++)
                if (Sg[j] == s) { ok = 0; break; }
        } while (!ok);
        Sg[i] = s;
    }
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: %s d D seed time_limit N_start\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int Nstart = atoi(argv[5]);
    if (d < 3 || d > MAXDD || D < 2) { printf("0 0\n"); return 0; }

    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    double t0 = now();
    t_end = t0 + limit * 0.93;
    long moore = moore_bound();
    int Nmax = (int)(moore / 2);
    if (Nmax > MAXG) Nmax = MAXG;
    if (Nstart < d) Nstart = d;
    double slice = limit / 40.0;
    if (slice < 0.05) slice = 0.05;

    int bestN = 0;
    Tup bestTup;
    memset(&bestTup, 0, sizeof bestTup);
    int bestS[MAXDD];
    memset(bestS, 0, sizeof bestS);

    /* Ascending scan: for each order N, sample groups and connection sets until one is valid. */
    for (int N = Nstart; N <= Nmax && now() < t_end; N++) {
        enum_tuples(N);
        if (ntup == 0) continue;
        double send = now() + slice;
        if (send > t_end) send = t_end;
        while (now() < send) {
            Tup t = tups[rndint(ntup)];
            set_group(t.m, t.k, t.r);
            pick_set(N);
            if (haar_valid()) {
                bestN = N;
                bestTup = t;
                memcpy(bestS, Sg, sizeof Sg);
                break;
            }
        }
    }

    if (bestN == 0) { printf("0 0\n"); return 0; }
    set_group(bestTup.m, bestTup.k, bestTup.r);
    memcpy(Sg, bestS, sizeof Sg);
    make_tables();
    printf("%d %d\n", 2 * bestN, bestN * d);
    for (int x = 0; x < bestN; x++)
        for (int i = 0; i < d; i++)
            printf("%d %d\n", x, bestN + Rt[i][x]);
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


def _consider(best, text, d, D):
    """Return the parsed graph if it is valid and larger than best, else best."""
    try:
        n, edges = lib.parse_graph_text(text)
    except Exception:
        return best
    if n > best[0] and lib.is_valid(n, edges, d, D):
        return (n, edges)
    return best


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    start = known_start(d, D)
    best = start if start is not None else lib.haar_graph(d, range(d))   # K_{d,d}: always valid
    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))

    goal = RECORD_GOAL.get((d, D), 0)
    moore = lib.moore_bound(d, D)
    deadline = t0 + 0.85 * time_limit - 1.0
    remaining = deadline - time.monotonic()
    if best[0] >= moore:
        remaining = min(remaining, 0.5)   # nothing beats a Moore graph; just exercise the engine
    use_haar = goal > 0 and d >= 3 and D >= 2 and d <= 8 and best[0] < moore

    if remaining > 0.2:
        # Stage 1: the parent engine (safe fallback, keeps the record-level result).
        p_budget = remaining * (0.55 if use_haar else 1.0)
        try:
            text = lib.run_c(C_PARENT, [d, D, seed, p_budget, goal],
                             stdin_graph=start, timeout=p_budget + 5)
            best = _consider(best, text, d, D)
        except Exception:
            pass

    if use_haar:
        # Stage 2: Haar graphs over semidirect products, scanning group orders upward
        # from goal/2 + 1 (so 2N > goal). Starts from scratch, not from the parent graph.
        h_budget = deadline - time.monotonic()
        if h_budget > 1.0:
            try:
                text = lib.run_c(C_HAAR, [d, D, seed, h_budget, goal // 2 + 1],
                                 stdin_graph=None, timeout=h_budget + 5)
                best = _consider(best, text, d, D)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
