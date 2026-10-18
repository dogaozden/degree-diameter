"""Starter program: Python builds the best known start graph, the C engine searches from it.

Most improvements belong in C_SOURCE (it runs 10-100x faster than Python).
build() keeps the best valid graph it has, so a broken idea in C can only cost time.

Pipeline (bold change): a new Cayley-type search (C_CAYLEY) runs first. It builds bipartite
graphs A_x ~ B_{s*x} over semidirect groups Z_m x| Z_k with a d-element connection set, and
checks diameter from just two sources (identity on each side), which is exact by
vertex-transitivity. Then the original voltage-lift and grow engine (C_SOURCE) runs from
scratch or from the best graph so far. Every stage is validated in Python, so the result never
drops below the parent's fallback.
"""
import time

import lib

C_CAYLEY = r'''
/* Bipartite Cayley-type search.
 *
 * Graph: A_x (index x) ~ B_{s x} (index N + s x) for s in S, |S| = d, G = Z_m x| Z_k of order N.
 * Right translations are automorphisms, so every pair is equivalent to a pair with the
 * first vertex at the identity. The diameter is <= D iff the eccentricities of A_e and B_e
 * are <= D. The search anneals S to minimise the number of unreached vertices, and grows N.
 *
 * Usage:   prog d D seed time_limit      (stdin ignored)
 * stdout:  "n m" then m lines "u v" (valid bipartite graph) or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXD 16
#define MAXN 8192

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

/* Group Z_Gm x|_Gr Z_Gk of order N = Gm*Gk; element a*Gk + b; identity is 0. */
static int Gm, Gk, Gr, N;
static int rp[MAXN];
static int inv_of[MAXN];

static int gmul(int x, int y) {
    int a = x / Gk, b = x % Gk, c = y / Gk, e = y % Gk;
    return (int)(((long)a + (long)rp[b] * c) % Gm) * Gk + (b + e) % Gk;
}

static int ginv(int x) {
    int a = x / Gk, b = x % Gk, nb = (Gk - b) % Gk;
    long ia = (Gm - (long)rp[nb] * a % Gm) % Gm;
    return (int)(ia * Gk + nb);
}

static void set_group(int m, int k, int r) {
    Gm = m; Gk = k; Gr = r; N = m * k;
    rp[0] = 1 % Gm;
    for (int b = 1; b < Gk; b++) rp[b] = (int)((long)rp[b - 1] * Gr % Gm);
    for (int x = 0; x < N; x++) inv_of[x] = ginv(x);
}

/* Uniform random (m, k, r) with m*k = n, gcd(r, m) = 1, r^k = 1 mod m. */
static int random_group(int n) {
    long count = 0;
    int bm = 0, bk = 0, br = 0;
    for (int m = 1; m <= n; m++) {
        if (n % m) continue;
        int k = n / m;
        int rmax = m > 1 ? m : 2;
        for (int r = 1; r < rmax; r++) {
            if (m > 1 && gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            count++;
            if (rndint((int)count) == 0) { bm = m; bk = k; br = r; }
        }
    }
    if (!count) return 0;
    set_group(bm, bk, br);
    return 1;
}

/* Connection set S (distinct group elements), with tables:
 * Lm[i][x] = index of B-neighbour of A_x via S[i]; Li[i][y] = index of A-neighbour of B_y. */
static int S[MAXD], Sinv[MAXD];
static int Lm[MAXD][MAXN], Li[MAXD][MAXN];

static void set_elem(int i, int g) {
    S[i] = g;
    Sinv[i] = inv_of[g];
    for (int x = 0; x < N; x++) {
        Lm[i][x] = gmul(g, x);
        Li[i][x] = gmul(Sinv[i], x);
    }
}

static unsigned int seen[2 * MAXN];
static unsigned int stamp_ctr = 0;
static int qbuf[2 * MAXN];

/* Number of vertices NOT within distance D of src (src in 0..2N-1; >= N means a B vertex). */
static long missing_from(int src) {
    stamp_ctr++;
    int head = 0, tail = 0;
    seen[src] = stamp_ctr;
    qbuf[tail++] = src;
    for (int depth = 0; depth < D && head < tail; depth++) {
        int end = tail;
        while (head < end) {
            int v = qbuf[head++];
            if (v < N) {
                for (int i = 0; i < d; i++) {
                    int u = N + Lm[i][v];
                    if (seen[u] != stamp_ctr) { seen[u] = stamp_ctr; qbuf[tail++] = u; }
                }
            } else {
                int y = v - N;
                for (int i = 0; i < d; i++) {
                    int u = Li[i][y];
                    if (seen[u] != stamp_ctr) { seen[u] = stamp_ctr; qbuf[tail++] = u; }
                }
            }
        }
    }
    return (long)(2 * N - tail);
}

/* Vertex-transitive reduction: diameter <= D iff both identity sources reach everything. */
static long eval_bad(void) { return missing_from(0) + missing_from(N); }

/* Anneal S (size d) over the current group. Returns 1 if the graph has diameter <= D. */
static int anneal(int iters) {
    for (int i = 0; i < d; i++) {
        int g, dup;
        do {
            g = rndint(N);
            dup = 0;
            for (int j = 0; j < i; j++) if (S[j] == g) dup = 1;
        } while (dup);
        set_elem(i, g);
    }
    long f = eval_bad();
    for (long it = 0; it < iters && f > 0; it++) {
        if ((it & 63) == 0 && now() > t_end) return 0;
        int i = rndint(d), g = rndint(N), dup = 0;
        for (int j = 0; j < d; j++) if (S[j] == g) { dup = 1; break; }
        if (dup) continue;
        int old = S[i];
        set_elem(i, g);
        long nf = eval_bad();
        double T = 2.0 * (1.0 - (double)it / iters) + 0.05;
        if (nf <= f || rnd01() < exp((double)(f - nf) / T)) f = nf;
        else set_elem(i, old);
    }
    return f == 0;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit * 0.9;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 3 || d > MAXD || D < 2) { printf("0 0\n"); return 0; }

    /* Half the Moore bound: N <= sum_{i<D} (d-1)^i, and N <= MAXN. */
    long half = 0, pw = 1;
    for (int i = 0; i < D && half <= MAXN; i++) { half += pw; pw *= (d - 1); }
    long Nmax = half < MAXN ? half : MAXN;

    int best_N = 0, bS[MAXD], bm = 0, bk = 0, br = 0;
    int delta = 16;
    long fails = 0;
    while (now() < t_end && best_N + 1 <= Nmax) {
        long hi = best_N + delta;
        if (hi > Nmax) hi = Nmax;
        int n = best_N + 1 + rndint((int)(hi - best_N));
        if (n < d) continue;
        if (!random_group(n)) continue;
        if (anneal(4000)) {
            best_N = n;
            memcpy(bS, S, sizeof S);
            bm = Gm; bk = Gk; br = Gr;
            fails = 0;
            if (delta < 256) delta *= 2;
        } else if (++fails % 40 == 0 && delta > 1) {
            delta /= 2;
        }
    }

    if (best_N == 0) { printf("0 0\n"); return 0; }
    set_group(bm, bk, br);
    for (int i = 0; i < d; i++) set_elem(i, bS[i]);
    /* Independent final check from every vertex. */
    for (int v = 0; v < 2 * N; v++)
        if (missing_from(v) != 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", 2 * N, N * d);
    for (int x = 0; x < N; x++)
        for (int i = 0; i < d; i++)
            printf("%d %d\n", x, N + Lm[i][x]);
    return 0;
}
'''

C_SOURCE = r'''
/* Bipartite degree-diameter search core.
 *
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v": a known-valid starting graph, or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found
 *          (bipartite, every degree <= d, every pair of vertices within D steps).
 *
 * Search, in order:
 *   1. Voltage lifts over groups Z_m x| Z_k (semidirect products), with hill-climbing on
 *      the voltages. A lift of a d-regular base multigraph with p vertices per side over a
 *      group of order N has 2pN vertices and is bipartite and d-regular automatically.
 *      The size target moves by an adaptive relative step: it grows after successes and
 *      shrinks after repeated failures, so large jumps are tried while they work.
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

/* Adaptive lift search: the size target is best->n plus a relative step `jump`.
 * Successes enlarge the step (bigger jumps while they work); repeated failures shrink it,
 * down to a minimum step of 2 vertices, so the search never stalls at tiny increments. */
static void lift_search(Graph *best, double until) {
    static Graph cand;
    static Grp G;
    long moore = moore_bound();
    double jump = 0.04;
    int fails = 0;
    while (now() < until) {
        if (best->n + 2 > moore) return;
        int r = rndint(10);
        int p = r < 3 ? 1 : r < 6 ? 2 : r < 9 ? 3 : 4;
        long step = (long)(best->n * jump);
        if (step < 2) step = 2;
        long target = best->n + step;
        if (target > moore) target = moore;
        int N = (int)((target + 2 * p - 1) / (2 * p)) + rndint(2);
        if (best->n == 0) N = d + rndint(3);
        if (N < d || 2L * p * N > moore || 2 * p * N > MAXN) {
            jump *= 0.8;
            if (jump < 0.002) jump = 0.002;
            if (++fails > 100000) return;
            continue;
        }
        if (!random_group(N, &G)) continue;
        int steps = 200 + 400000 / (2 * p * N);
        if (lift_try(&cand, p, N, &G, steps) && cand.n > best->n && is_valid(&cand)) {
            copy_graph(best, &cand);
            fails = 0;
            if (jump < 0.1) jump *= 1.25;
        } else {
            if (++fails % 8 == 0) {
                jump *= 0.7;
                if (jump < 0.002) jump = 0.002;
            }
        }
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

    static Graph best;
    if (d < 1 || D < 1 || d > MAXD) { complete_bipartite(&best); print_graph(&best); return 0; }
    read_start(&best);
    int had_start = best.n > 0;

    if (D >= 2 && best.n < moore_bound()) {
        /* Without a start graph, lifts are the only source of large graphs: give them most of the time. */
        double lift_share = had_start ? 0.2 : 0.75;
        lift_search(&best, t0 + (t_end - t0) * lift_share);
        if (best.n > 0) grow_search(&best, t_end);
    }
    if (best.n == 0) complete_bipartite(&best);
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


def known_start(d, D):
    """Best graph Python can build directly for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)           # record graphs of order 2(q^2+q+5)
    return None


def _attempt(prog, args, graph, budget):
    """Run one C engine; return the parsed graph, or None on any failure."""
    try:
        text = lib.run_c(prog, args, stdin_graph=graph, timeout=budget + 5)
        return lib.parse_graph_text(text)
    except Exception:
        return None


def _take(cand, best, d, D):
    """Return cand if it is a valid, strictly larger graph; otherwise keep best."""
    if cand is None or cand[0] <= best[0]:
        return best
    try:
        if lib.is_valid(cand[0], cand[1], d, D):
            return cand
    except Exception:
        pass
    return best


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    start = known_start(d, D)
    best = start if start is not None else lib.haar_graph(d, range(d))   # K_{d,d}: always valid
    if best[0] >= lib.moore_bound(d, D):
        return best   # a Moore graph cannot be beaten

    total = 0.85 * time_limit - 2.0   # leave room for compiling and the Python checks

    def left():
        return total - (time.monotonic() - t0)

    # Stage 1 (new): bipartite Cayley-type search over semidirect groups.
    if d >= 3 and D >= 2:
        b = min(0.40 * total, left() - 3.0)
        if b > 0.5:
            best = _take(_attempt(C_CAYLEY, [d, D, seed, b], None, b), best, d, D)

    # Stage 2: voltage lifts and grow, from scratch if we still hold only K_{d,d}.
    from_scratch = best[0] <= 2 * d
    b = min(0.30 * total, left() - 3.0)
    if b > 0.5:
        best = _take(_attempt(C_SOURCE, [d, D, seed, b],
                              None if from_scratch else best, b), best, d, D)

    # Stage 3: polish the best graph found so far.
    b = min(0.20 * total, left() - 2.0)
    if b > 0.5:
        best = _take(_attempt(C_SOURCE, [d, D, seed, b], best, b), best, d, D)

    return best
