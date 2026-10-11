import itertools
import time

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search core (combined engine).
 *
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v": a valid start graph, or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * Phases:
 *   1. Voltage lifts over semidirect products Z_m x| Z_k (baseline).
 *   2. Voltage lifts over random subgroups of small permutation groups (main push).
 *   3. Greedy cover extension: add vertices whose neighbourhoods cover all balls of radius D-1.
 *   4. Grow by two: insert one vertex per side and anneal degree-preserving swaps.
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
#define MAXDEG 16
#define MAXGRP 256
#define HS 1024
#define NAMB_KINDS 9

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

/* ------------------------------------------------------------------ distances */

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static int badv[MAXN]; /* badv[v] = vertices farther than D from v, after bad_pairs() */

/* Bitset reachability: after r rounds, row v holds every vertex within r steps of v.
 * Returns the buffer holding the result (valid until the next call). */
static uint64_t *reach_rounds(const Graph *g, int rounds) {
    int n = g->n, W = (n + 63) / 64;
    uint64_t *cur = RA, *nxt = RB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int r = 0; r < rounds; r++) {
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
    return cur;
}

/* Number of unordered pairs at distance > D (0 means diameter <= D). Fills badv. */
static long bad_pairs(const Graph *g) {
    int n = g->n, W = (n + 63) / 64;
    const uint64_t *R = reach_rounds(g, D);
    long total = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        const uint64_t *s = R + (size_t)v * W;
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

/* K_{d,d}: valid for D >= 2. */
static void complete_bipartite(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= d; }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

/* A single edge: valid for D = 1. */
static void edge_graph(Graph *g) {
    g->n = 2;
    g->deg[0] = g->deg[1] = 0;
    g->side[0] = 0;
    g->side[1] = 1;
    add_edge(g, 0, 1);
}

/* ------------------------------------------------------------------ greedy extension */

/* Add one vertex x on side c joined to a set of vertices of the other side, each of
 * spare degree, whose radius-(D-1) balls cover every vertex. Old distances never grow,
 * so the diameter bound is preserved. Returns 1 if a vertex was added. */
static int extend_once(Graph *g) {
    int n = g->n, W = (n + 63) / 64;
    if (D < 2 || n < 1 || n + 1 > MAXN || n + 1 > moore_bound()) return 0;
    const uint64_t *B = reach_rounds(g, D - 1);
    static uint64_t cov[MAXW];
    static unsigned char taken[MAXN];
    int order[2];
    order[0] = rndint(2);
    order[1] = 1 - order[0];
    for (int oi = 0; oi < 2; oi++) {
        int c = order[oi];
        memset(cov, 0, sizeof(uint64_t) * W);
        memset(taken, 0, (size_t)n);
        int chosen[MAXD], nch = 0, covered = 0;
        while (covered < n && nch < d) {
            int off = rndint(n), bu = -1, bg = 0;
            for (int k = 0; k < n; k++) {
                int u = (k + off) % n;
                if (g->side[u] == c || g->deg[u] >= d || taken[u]) continue;
                const uint64_t *row = B + (size_t)u * W;
                int gain = 0;
                for (int w = 0; w < W; w++) gain += __builtin_popcountll(row[w] & ~cov[w]);
                if (gain > bg) { bg = gain; bu = u; }
            }
            if (bu < 0) break;
            chosen[nch++] = bu;
            taken[bu] = 1;
            const uint64_t *row = B + (size_t)bu * W;
            covered = 0;
            for (int w = 0; w < W; w++) {
                cov[w] |= row[w];
                covered += __builtin_popcountll(cov[w]);
            }
        }
        if (covered == n && nch > 0) {
            g->n = n + 1;
            g->deg[n] = 0;
            g->side[n] = (unsigned char)c;
            for (int i = 0; i < nch; i++) add_edge(g, n, chosen[i]);
            return 1;
        }
    }
    return 0;
}

/* Repeatedly extend g; keep the result only if it is still valid. */
static void extend_all(Graph *g) {
    static Graph bak;
    if (g->n == 0 || D < 2) return;
    copy_graph(&bak, g);
    int grew = 0;
    while (extend_once(g)) grew = 1;
    if (grew && !is_valid(g)) copy_graph(g, &bak);
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
                G->m = m;
                G->k = k;
                G->r = r;
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
            for (int i = p - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int s = perm[i];
                perm[i] = perm[j];
                perm[j] = s;
            }
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

/* Hill-climb the voltages of a random base graph over a cyclic-type semidirect group. */
static int lift_try(Graph *g, int p, int N, const Grp *G, int steps) {
    int M[MAXP][MAXP];
    Dart dt[MAXD * MAXP];
    int nd = 0;
    make_base(p, M);
    for (int i = 0; i < p; i++)
        for (int j = 0; j < p; j++)
            for (int c = 0; c < M[i][j]; c++) {
                dt[nd].i = i;
                dt[nd].j = j;
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

/* ------------------------------------------------------------------ permutation groups */

typedef struct { unsigned char p[MAXDEG]; } Perm;

static int PDEG = 0, NAMB = 0;
static Perm AMB[8];
static Perm ELEM[MAXGRP];
static int NEL = 0;
static int MT[MAXGRP][MAXGRP];

static uint64_t hkey[HS];
static int hval[HS];
static unsigned char hused[HS];

static Perm perm_id(void) {
    Perm e;
    memset(&e, 0, sizeof e);
    for (int x = 0; x < PDEG; x++) e.p[x] = (unsigned char)x;
    return e;
}

/* (a*b)[x] = a[b[x]] */
static Perm pmul(const Perm *a, const Perm *b) {
    Perm c;
    memset(&c, 0, sizeof c);
    for (int x = 0; x < PDEG; x++) c.p[x] = a->p[b->p[x]];
    return c;
}

static uint64_t pkey(const Perm *a) {
    uint64_t k = 0;
    for (int x = 0; x < PDEG; x++) k = k * 16u + a->p[x];
    return k;
}

static unsigned hslot(uint64_t k) {
    return (unsigned)((k * 0x9E3779B97F4A7C15ULL) >> 54);
}

static int hfind(uint64_t k) {
    unsigned h = hslot(k);
    while (hused[h]) {
        if (hkey[h] == k) return hval[h];
        h = (h + 1) & (HS - 1);
    }
    return -1;
}

static void hinsert(uint64_t k, int v) {
    unsigned h = hslot(k);
    while (hused[h]) h = (h + 1) & (HS - 1);
    hused[h] = 1;
    hkey[h] = k;
    hval[h] = v;
}

static void amb_sym(int n) {
    PDEG = n;
    NAMB = 2;
    AMB[0] = perm_id();
    AMB[0].p[0] = 1;
    AMB[0].p[1] = 0;
    AMB[1] = perm_id();
    for (int x = 0; x < n; x++) AMB[1].p[x] = (unsigned char)((x + 1) % n);
}

static void amb_wreath(int a, int b) {
    PDEG = a * b;
    NAMB = 2;
    AMB[0] = perm_id();
    for (int c = 0; c < a; c++) AMB[0].p[c] = (unsigned char)((c + 1) % a);
    AMB[1] = perm_id();
    for (int blk = 0; blk < b; blk++)
        for (int c = 0; c < a; c++)
            AMB[1].p[blk * a + c] = (unsigned char)(((blk + 1) % b) * a + c);
}

static void amb_agl23(void) {
    PDEG = 9;
    NAMB = 5;
    for (int k = 0; k < NAMB; k++) {
        AMB[k] = perm_id();
        for (int x = 0; x < 3; x++)
            for (int y = 0; y < 3; y++) {
                int nx = x, ny = y;
                switch (k) {
                    case 0: nx = (x + 1) % 3; break;
                    case 1: ny = (y + 1) % 3; break;
                    case 2: nx = (x + y) % 3; break;
                    case 3: nx = y; ny = (2 * x) % 3; break;
                    default: nx = (2 * x) % 3; break;
                }
                AMB[k].p[3 * x + y] = (unsigned char)(3 * nx + ny);
            }
    }
}

static void setup_ambient(int kind) {
    switch (kind) {
        case 0: amb_sym(6); break;
        case 1: amb_sym(7); break;
        case 2: amb_sym(8); break;
        case 3: amb_wreath(3, 3); break;
        case 4: amb_wreath(2, 4); break;
        case 5: amb_wreath(4, 2); break;
        case 6: amb_wreath(4, 3); break;
        case 7: amb_wreath(2, 5); break;
        default: amb_agl23(); break;
    }
}

static Perm rand_elem(void) {
    Perm e = perm_id();
    int steps = 12 + rndint(30);
    for (int s = 0; s < steps; s++) {
        Perm t = pmul(&e, &AMB[rndint(NAMB)]);
        e = t;
    }
    return e;
}

/* Enumerate the group generated by gens into ELEM. Returns its order, or -1 if above cap. */
static int closure(const Perm *gens, int ng, int cap) {
    memset(hused, 0, sizeof hused);
    Perm id = perm_id();
    hinsert(pkey(&id), 0);
    ELEM[0] = id;
    NEL = 1;
    for (int i = 0; i < NEL; i++)
        for (int g = 0; g < ng; g++) {
            Perm c = pmul(&ELEM[i], &gens[g]);
            uint64_t k = pkey(&c);
            if (hfind(k) < 0) {
                if (NEL >= cap) return -1;
                hinsert(k, NEL);
                ELEM[NEL++] = c;
            }
        }
    return NEL;
}

static int random_subgroup(int lo, int hi) {
    Perm gens[3];
    int ng = 1 + rndint(3);
    for (int g = 0; g < ng; g++) gens[g] = rand_elem();
    int o = closure(gens, ng, hi);
    return (o >= lo && o <= hi) ? o : 0;
}

static int build_mt(int N) {
    for (int i = 0; i < N; i++)
        for (int j = 0; j < N; j++) {
            Perm c = pmul(&ELEM[i], &ELEM[j]);
            int k = hfind(pkey(&c));
            if (k < 0) return 0;
            MT[i][j] = k;
        }
    return 1;
}

/* Group lift: dart (i, j, g) joins (A, i, x) to (B, j, x*g) for every x. */
static void build_glift(Graph *g, int p, int N, const Dart *dt, int nd) {
    g->n = 2 * p * N;
    for (int v = 0; v < g->n; v++) {
        g->deg[v] = 0;
        g->side[v] = (unsigned char)(v >= p * N);
    }
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, dt[t].i * N + x, p * N + dt[t].j * N + MT[x][dt[t].g]);
}

static int glift_try(Graph *g, int p, int N, int steps, double until) {
    int M[MAXP][MAXP];
    Dart dt[MAXD * MAXP];
    int nd = 0;
    make_base(p, M);
    for (int i = 0; i < p; i++)
        for (int j = 0; j < p; j++)
            for (int c = 0; c < M[i][j]; c++) {
                dt[nd].i = i;
                dt[nd].j = j;
                dt[nd].g = fresh_voltage(dt, nd, -1, i, j, N);
                nd++;
            }
    build_glift(g, p, N, dt, nd);
    long bad = bad_pairs(g);
    for (int s = 0; s < steps && bad > 0; s++) {
        if ((s & 15) == 0 && now() > until) return 0;
        int t = rndint(nd);
        int old = dt[t].g;
        dt[t].g = fresh_voltage(dt, nd, t, dt[t].i, dt[t].j, N);
        build_glift(g, p, N, dt, nd);
        long nb = bad_pairs(g);
        if (nb <= bad || rnd01() < 0.02) bad = nb;
        else dt[t].g = old;
    }
    return bad == 0;
}

static void group_lift_search(Graph *best, double until) {
    static Graph cand;
    long moore = moore_bound();
    int dead = 0;
    while (now() < until) {
        int p = 1 + rndint(4);
        long need = best->n + 2;
        long Nlo = (need + 2L * p - 1) / (2L * p);
        if (Nlo < d + 1) Nlo = d + 1;
        long Nhi = moore / (2L * p);
        if (Nhi > MAXGRP) Nhi = MAXGRP;
        if (Nhi > Nlo + 24) Nhi = Nlo + 24;
        if (Nlo > Nhi) {
            if (++dead > 200) return;
            continue;
        }
        dead = 0;
        int N = 0;
        for (int a = 0; a < 400 && N == 0 && now() < until; a++) {
            setup_ambient(rndint(NAMB_KINDS));
            N = random_subgroup((int)Nlo, (int)Nhi);
        }
        if (N == 0 || !build_mt(N)) continue;
        for (int r = 0; r < 6 && now() < until; r++)
            if (glift_try(&cand, p, N, 1500, until) && cand.n > best->n && is_valid(&cand))
                copy_graph(best, &cand);
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
    while (now() < until && best->n + 2 <= moore_bound()) {
        double left = until - now();
        double slice = left < 4.0 ? left : (left / 4 > 4.0 ? left / 4 : 4.0);
        if (grow_once(best, &work, now() + slice)) {
            copy_graph(best, &work);
            extend_all(best);
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
    t_end = t0 + limit * 0.92;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 1 || d > MAXD) {
        printf("0 0\n");
        return 0;
    }
    static Graph best;
    if (D < 2) {
        edge_graph(&best);
        print_graph(&best);
        return 0;
    }

    read_start(&best);
    int had_start = best.n > 0;

    if (best.n < moore_bound()) {
        double span = t_end - t0;
        lift_search(&best, t0 + span * (had_start ? 0.05 : 0.10));
        group_lift_search(&best, t0 + span * 0.72);
        extend_all(&best);
        if (best.n > 0) grow_search(&best, t_end);
        extend_all(&best);
    }
    if (best.n == 0) complete_bipartite(&best);
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''

GQ_Q_MAX = 9


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q): degree q+1, diameter 4."""
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


def known_start(d, D):
    """Best algebraic graph Python can build directly for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)       # Moore graph
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)               # record family
    if D == 4 and 2 <= d - 1 <= GQ_Q_MAX and lib.is_prime_power(d - 1):
        return _gq_w(d - 1)                                # generalized quadrangle, Moore graph
    return None


def _valid(g, d, D):
    try:
        return lib.is_valid(g[0], g[1], d, D)
    except Exception:
        return False


def build(d, D, seed, time_limit):
    t0 = time.monotonic()

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D                                   # even cycle: Moore-extremal
        return L, [(i, (i + 1) % L) for i in range(L)]

    best = lib.haar_graph(d, range(d))              # K_{d,d}, valid for D >= 2
    if D == 2:
        return best

    start = known_start(d, D)
    start_ok = start is not None and _valid(start, d, D)
    if start_ok:
        if start[0] > best[0]:
            best = start
        if start[0] >= lib.moore_bound(d, D):
            return start                            # already optimal, skip the search

    budget = 0.8 * time_limit - (time.monotonic() - t0) - 2.0
    if budget < 1.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=start if start_ok else None,
                         timeout=budget + 5)
        n, edges = lib.parse_graph_text(text)
        if n > best[0] and _valid((n, edges), d, D):
            best = (n, edges)
    except Exception:
        pass                                        # keep the valid fallback
    return best
