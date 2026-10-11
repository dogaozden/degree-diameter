"""Bi-Cayley search over explicit groups, followed by the lift/grow engine as a safe baseline.

Phase 1 runs the proven lift-and-grow C engine (C_PARENT) from the best known start. This keeps
the parent's result as the fallback.

Phase 2 (C_BICAY) is the new construction. For a group G of order g, the bi-Cayley graph has
vertices A_x and B_x (x in G) and edges A_x ~ B_{x s} for s in a connection set S of size d.
Left multiplication is an automorphism that acts regularly on each side, so the diameter is at
most D iff every vertex lies within distance D of A_e and of B_e. A simulated annealing search
over S minimises the number of unreached pairs. The groups are PGL(2,7) and semidirect products
Z_m x| Z_k, with orders in the range that could beat the current best. Every output is checked
with lib.is_valid, and the best valid graph is returned.
"""
import itertools
import math
import random
import time

import lib

MAX_G = 512  # group order cap, matches the C engine

C_PARENT = r'''
/* Bipartite degree-diameter search core.
 *
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v": a valid start graph, or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * Phase 1 (lift search): base with kb vertices per side, d darts out of each base vertex
 *   (layers are permutations, so the lift is d-regular). Dart (i, j, s) joins A_{i,g} to
 *   B_{j,g*s}. Left multiplication is an automorphism, so the diameter is <= D iff a BFS of
 *   depth D from each of the 2kb class representatives reaches everything. Voltages and
 *   layer swaps are hill-climbed with annealing on the number of unreached pairs.
 *   Escalations when stuck: (a) annealing runs get more steps, (b) the target group order
 *   is raised by one step per block of failures (group-order escalation).
 * Phase 2 (grow by two): add one vertex per side, then anneal degree-preserving edge swaps.
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
#define MAXK 4
#define MAXDART (MAXD * MAXK)
#define BIGCOST 1000000000L

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

/* Upper bound on the order of a bipartite graph with max degree d and diameter D. */
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

/* Number of unordered pairs at distance > D. Zero means diameter <= D. */
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

/* ------------------------------------------------------------ groups */

/* Z_m x|_r Z_k2: element a*k2+b, (a,b)(c,e) = (a + r^b c mod m, b+e mod k2). */
static int GM, GK2, GORD;
static int RP[MAXN]; /* RP[b] = r^b mod m */

static void set_group(int m, int k2, int r) {
    GM = m;
    GK2 = k2;
    GORD = m * k2;
    RP[0] = 1 % m;
    for (int b = 1; b < k2; b++) RP[b] = (int)((long)RP[b - 1] * r % m);
}

static int gmul(int x, int y) {
    int a = x / GK2, b = x % GK2, c = y / GK2, e = y % GK2;
    return (int)(((long)a + (long)RP[b] * c) % GM) * GK2 + (b + e) % GK2;
}

/* Random semidirect group of order G (reservoir over sampled candidates). */
static int sample_group(int G, int *om, int *ok2, int *orr) {
    int cnt = 0;
    for (int m = 1; m <= G; m++) {
        if (G % m) continue;
        int k2 = G / m;
        if (m == 1) {
            if (rndint(++cnt) == 0) { *om = 1; *ok2 = k2; *orr = 0; }
            continue;
        }
        if (k2 == 1) {
            if (rndint(++cnt) == 0) { *om = m; *ok2 = 1; *orr = 1; }
            continue;
        }
        for (int t = 0; t < 120; t++) {
            int r = 1 + rndint(m - 1);
            if (gcd(r, m) != 1 || powmod(r, k2, m) != 1 % m) continue;
            if (rndint(++cnt) == 0) { *om = m; *ok2 = k2; *orr = r; }
        }
    }
    return cnt > 0;
}

/* ------------------------------------------------------------ voltage lifts */

static int KB, ND;                 /* base vertices per side, number of darts */
static int DI[MAXDART], DJ[MAXDART], DS[MAXDART];
static int DPERM[MAXDART][MAXN];   /* DPERM[t][g] = g * DS[t] */
static int LADJ[MAXN][MAXD];
static int LDEG[MAXN];
static int VIS[MAXN], VST = 0;
static int QU[MAXN];

static void set_dart_perm(int t) {
    for (int g = 0; g < GORD; g++) DPERM[t][g] = gmul(g, DS[t]);
}

static int has_dup(void) {
    for (int t1 = 0; t1 < ND; t1++)
        for (int t2 = t1 + 1; t2 < ND; t2++)
            if (DI[t1] == DI[t2] && DJ[t1] == DJ[t2] && DS[t1] == DS[t2]) return 1;
    return 0;
}

static void build_ladj(void) {
    int N = 2 * KB * GORD;
    for (int v = 0; v < N; v++) LDEG[v] = 0;
    for (int t = 0; t < ND; t++)
        for (int g = 0; g < GORD; g++) {
            int a = DI[t] * GORD + g;
            int b = (KB + DJ[t]) * GORD + DPERM[t][g];
            LADJ[a][LDEG[a]++] = b;
            LADJ[b][LDEG[b]++] = a;
        }
}

/* Unreached (representative, vertex) pairs over the 2KB class representatives. */
static long orbit_cost(void) {
    if (has_dup()) return BIGCOST;
    build_ladj();
    int N = 2 * KB * GORD;
    long total = 0;
    for (int rep = 0; rep < 2 * KB; rep++) {
        int src = rep * GORD;
        VST++;
        int head = 0, tail = 0;
        VIS[src] = VST;
        QU[tail++] = src;
        for (int depth = 0; depth < D; depth++) {
            int end = tail;
            if (head == end) break;
            while (head < end) {
                int u = QU[head++];
                for (int i = 0; i < LDEG[u]; i++) {
                    int v = LADJ[u][i];
                    if (VIS[v] != VST) { VIS[v] = VST; QU[tail++] = v; }
                }
            }
        }
        total += N - tail;
    }
    return total;
}

static void build_full(Graph *g) {
    int N = 2 * KB * GORD;
    g->n = N;
    for (int v = 0; v < N; v++) { g->deg[v] = 0; g->side[v] = v >= KB * GORD; }
    for (int t = 0; t < ND; t++)
        for (int x = 0; x < GORD; x++)
            add_edge(g, DI[t] * GORD + x, (KB + DJ[t]) * GORD + DPERM[t][x]);
}

/* One annealing run over voltages and layer swaps for a random base and the given group.
 * On success, out holds the full lift. */
static int lift_climb(int kb, int G, int m, int k2, int r, long steps, Graph *out) {
    KB = kb;
    ND = d * kb;
    set_group(m, k2, r);
    int perm[MAXK];
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < kb; i++) perm[i] = i;
        for (int i = kb - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int s = perm[i]; perm[i] = perm[j]; perm[j] = s;
        }
        for (int i = 0; i < kb; i++) {
            int t = l * kb + i;
            DI[t] = i;
            DJ[t] = perm[i];
            DS[t] = rndint(G);
            set_dart_perm(t);
        }
    }
    long cost = orbit_cost();
    for (long s = 0; s < steps && cost > 0; s++) {
        if ((s & 31) == 0 && now() > t_end) return 0;
        double T = 2.0 * (1.0 - (double)s / (double)steps) + 0.05;
        if (rnd01() < 0.7) {
            int t = rndint(ND);
            int old = DS[t];
            int nv = rndint(G);
            if (nv == old) continue;
            DS[t] = nv;
            set_dart_perm(t);
            long c2 = orbit_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) cost = c2;
            else { DS[t] = old; set_dart_perm(t); }
        } else {
            if (kb < 2) continue;
            int l = rndint(d);
            int i1 = rndint(kb), i2 = rndint(kb);
            if (i1 == i2) continue;
            int t1 = l * kb + i1, t2 = l * kb + i2;
            int tmp = DJ[t1]; DJ[t1] = DJ[t2]; DJ[t2] = tmp;
            long c2 = orbit_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) cost = c2;
            else { tmp = DJ[t1]; DJ[t1] = DJ[t2]; DJ[t2] = tmp; }
        }
    }
    if (cost != 0) return 0;
    build_full(out);
    return 1;
}

static Graph LCAND;

/* Group-order escalation: after many failed attempts, the target group order rises,
 * one step per block of 40 failures, capped at 6. */
static void lift_search(Graph *best, double until) {
    long moore = moore_bound();
    int fails = 0;   /* consecutive attempts that did not improve best */
    while (now() < until) {
        if (best->n + 2 > moore) return;
        int r = rndint(10);
        int kb = r < 3 ? 1 : r < 7 ? 2 : 3;
        long esc = fails > 40 ? (fails - 40) / 40 + 1 : 0;
        if (esc > 6) esc = 6;
        long G = (best->n + 2 + 2L * kb - 1) / (2L * kb) + rndint(4) + esc;
        if (G < 1) G = 1;
        if (2L * kb * G > moore || 2L * kb * G > MAXN) { fails++; continue; }
        int m, k2, rr;
        if (!sample_group((int)G, &m, &k2, &rr)) { fails++; continue; }
        /* When lifts stop improving, give each annealing run more steps. */
        long extra = (long)(fails / 20) * 4000;
        if (extra > 60000) extra = 60000;
        long steps = 3000 + rndint(9000) + extra;
        int before = best->n;
        if (lift_climb(kb, (int)G, m, k2, rr, steps, &LCAND) &&
            LCAND.n > best->n && is_valid(&LCAND))
            copy_graph(best, &LCAND);
        fails = best->n > before ? 0 : fails + 1;
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
    while (now() < until && best->n + 2 <= moore_bound() && best->n + 2 <= MAXN) {
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
    t_end = t0 + limit * 0.9;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 1 || d > MAXD) { printf("1 0\n"); return 0; }
    if (d == 1 || D < 2) { printf("2 1\n0 1\n"); return 0; }

    static Graph best, start;
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    copy_graph(&start, &best);

    if (best.n < moore_bound()) {
        lift_search(&best, t0 + (t_end - t0) * 0.85);
        grow_search(&best, t_end);
    }
    if (!is_valid(&best)) copy_graph(&best, &start);
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''

C_BICAY = r'''
/* Bi-Cayley search over explicit groups.
 *
 * Usage:  prog d D seed time_limit
 * stdin:  "n m" then m lines of two ints. The ints (2m of them) are a flat list:
 *         K, then for each group: G, then G*G entries of the multiplication table
 *         (entry x*G+y is the product x*y). n is ignored.
 * Graph:  vertices A_x = x and B_x = G + x. Edge A_x ~ B_{x*s} for s in S, |S| = d.
 * Check:  left multiplication is an automorphism, so the diameter is <= D iff every
 *         vertex is within distance D of A_e and of B_e. Anneal S to remove unreached pairs.
 * stdout: "n m" and edges of the best (largest order) valid graph, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXG 512
#define MAXV (2 * MAXG)
#define MAXDEG 32
#define MAXK 32

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

typedef struct {
    int G;
    int e;
    int *mt;
    int *inv;
} Grp;

static Grp GR[MAXK];
static int NGR = 0;

/* current group */
static int GG, EE;
static const int *MT, *INV;

static int S[MAXDEG];
static int VIS[MAXV], VST = 0;
static int QU[MAXV];

static int in_prefix(int x, int n) {
    for (int k = 0; k < n; k++)
        if (S[k] == x) return 1;
    return 0;
}

/* k-th neighbour of vertex v in the bi-Cayley graph. */
static inline int nbr(int v, int k) {
    if (v < GG) return GG + MT[v * GG + S[k]];
    return MT[(v - GG) * GG + INV[S[k]]];
}

/* Total unreached vertices from A_e and from B_e within depth D. */
static long cost_of(void) {
    long total = 0;
    int N = 2 * GG;
    for (int src = 0; src < 2; src++) {
        int s0 = src == 0 ? EE : GG + EE;
        VST++;
        int head = 0, tail = 0;
        VIS[s0] = VST;
        QU[tail++] = s0;
        for (int depth = 0; depth < D; depth++) {
            int end = tail;
            if (head == end) break;
            while (head < end) {
                int u = QU[head++];
                for (int k = 0; k < d; k++) {
                    int v = nbr(u, k);
                    if (VIS[v] != VST) { VIS[v] = VST; QU[tail++] = v; }
                }
            }
        }
        total += N - tail;
    }
    return total;
}

static int anneal(long steps) {
    for (int k = 0; k < d; k++) {
        int x;
        do { x = rndint(GG); } while (in_prefix(x, k));
        S[k] = x;
    }
    long cost = cost_of();
    for (long s = 0; s < steps && cost > 0; s++) {
        if ((s & 127) == 0 && now() > t_end) break;
        double T = 1.5 * (1.0 - (double)s / (double)steps) + 0.03;
        int k = rndint(d);
        int x;
        do { x = rndint(GG); } while (in_prefix(x, d));
        int old = S[k];
        S[k] = x;
        long c2 = cost_of();
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) cost = c2;
        else S[k] = old;
    }
    return cost == 0;
}

/* Validate a G x G table as a group (left identity, inverses) and build the inverse table. */
static int load_group(Grp *g, int *tab, int G) {
    for (long i = 0; i < (long)G * G; i++)
        if (tab[i] < 0 || tab[i] >= G) return 0;
    int e = -1;
    for (int x = 0; x < G && e < 0; x++) {
        int ok = 1;
        for (int y = 0; y < G && ok; y++)
            if (tab[x * G + y] != y) ok = 0;
        if (ok) e = x;
    }
    if (e < 0) return 0;
    int *inv = malloc(sizeof(int) * G);
    if (!inv) return 0;
    for (int x = 0; x < G; x++) {
        int found = -1;
        for (int y = 0; y < G && found < 0; y++)
            if (tab[x * G + y] == e) found = y;
        if (found < 0) { free(inv); return 0; }
        inv[x] = found;
    }
    g->G = G;
    g->e = e;
    g->mt = tab;
    g->inv = inv;
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit < groups\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit;
    rs ^= (uint64_t)(seed + 7) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || D < 2 || d > MAXDEG) { printf("0 0\n"); return 0; }

    long n0, m0;
    if (scanf("%ld %ld", &n0, &m0) != 2 || m0 < 1) { printf("0 0\n"); return 0; }
    long cnt = 2 * m0;
    int *vals = malloc(sizeof(int) * (size_t)cnt);
    if (!vals) { printf("0 0\n"); return 0; }
    for (long i = 0; i < cnt; i++)
        if (scanf("%d", &vals[i]) != 1) { printf("0 0\n"); return 0; }

    int K = vals[0];
    long pos = 1;
    for (int i = 0; i < K && i < MAXK; i++) {
        if (pos >= cnt) break;
        int G = vals[pos++];
        if (G < 1 || G > MAXG || pos + (long)G * G > cnt) break;
        Grp g;
        if (d <= G && load_group(&g, vals + pos, G)) GR[NGR++] = g;
        pos += (long)G * G;
    }

    int bestG = 0, bestI = -1;
    int BS[MAXDEG];
    long steps = 3000;
    while (now() < t_end) {
        int any = 0;
        for (int i = 0; i < NGR && now() < t_end; i++) {
            if (GR[i].G <= bestG) continue;
            any = 1;
            GG = GR[i].G;
            EE = GR[i].e;
            MT = GR[i].mt;
            INV = GR[i].inv;
            if (anneal(steps)) {
                bestG = GG;
                bestI = i;
                memcpy(BS, S, sizeof(int) * d);
            }
        }
        if (!any) break;
        if (steps < 400000) steps = steps * 5 / 4 + 1;
    }

    if (bestI < 0) { printf("0 0\n"); return 0; }
    Grp *g = &GR[bestI];
    int G = g->G;
    printf("%d %d\n", 2 * G, G * d);
    for (int x = 0; x < G; x++)
        for (int k = 0; k < d; k++)
            printf("%d %d\n", x, G + g->mt[x * G + BS[k]]);
    return 0;
}
'''


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4, degree q+1."""
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
    """Best known construction Python can build directly for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)
    if D == 4:
        for q in range(min(d - 1, 7), 1, -1):
            if lib.is_prime_power(q) and q + 1 <= d:
                return _gq_w(q)
    return None


def _pgl2_table(p):
    """Multiplication table of PGL(2, p) for prime p: (order, flat table)."""
    def norm(m):
        c = next(x for x in m if x)
        inv = pow(c, p - 2, p)
        return tuple((x * inv) % p for x in m)

    mats = sorted({norm(m) for m in itertools.product(range(p), repeat=4)
                   if (m[0] * m[3] - m[1] * m[2]) % p})
    idx = {m: i for i, m in enumerate(mats)}
    G = len(mats)
    table = [0] * (G * G)
    for i, a in enumerate(mats):
        for j, b in enumerate(mats):
            c = ((a[0] * b[0] + a[1] * b[2]) % p, (a[0] * b[1] + a[1] * b[3]) % p,
                 (a[2] * b[0] + a[3] * b[2]) % p, (a[2] * b[1] + a[3] * b[3]) % p)
            table[i * G + j] = idx[norm(c)]
    return G, table


def _group_specs(lo, hi, seed, cap=6):
    """Candidate groups with order in [lo, hi], as specs sorted by decreasing order."""
    rng = random.Random(seed)
    specs = []
    for G in range(lo, hi + 1):
        for m in range(1, G + 1):
            if G % m:
                continue
            k = G // m
            if m == 1:
                rs = [0]
            else:
                rs = [r for r in range(1, m)
                      if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m][:3]
            specs.extend(("sd", G, m, k, r) for r in rs)
    pgl = [("pgl", 7)] if lo <= 336 <= hi else []
    rest = rng.sample(specs, min(len(specs), max(0, cap - len(pgl))))
    out = pgl + rest
    out.sort(key=lambda s: -(336 if s[0] == "pgl" else s[1]))
    return out


def _spec_table(spec):
    """Build (order, flat table) for a group spec."""
    if spec[0] == "pgl":
        return _pgl2_table(spec[1])
    _, G, m, k, r = spec
    order, mul, _ = lib.semidirect_group(m, k, r)
    return order, [mul(x, y) for x in range(order) for y in range(order)]


def _bicayley_candidate(d, D, seed, lo, hi, budget):
    """Run the C bi-Cayley search over candidate groups; return (n, edges) or None."""
    tables = []
    for spec in _group_specs(lo, hi, seed):
        try:
            G, tab = _spec_table(spec)
        except ValueError:
            continue
        if G < d or G > MAX_G or not (lo <= G <= hi):
            continue
        tables.append((G, tab))
    if not tables:
        return None
    vals = [len(tables)]
    for G, tab in tables:
        vals.append(G)
        vals.extend(tab)
    if len(vals) % 2:
        vals.append(0)
    pairs = [(vals[i], vals[i + 1]) for i in range(0, len(vals), 2)]
    text = lib.run_c(C_BICAY, [d, D, seed, round(budget, 2)],
                     stdin_graph=(1, pairs), timeout=budget + 5)
    return lib.parse_graph_text(text)


def build(d, D, seed, time_limit):
    t0 = time.monotonic()

    def remaining():
        return 0.85 * time_limit - (time.monotonic() - t0) - 1.0

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))          # K_{d,d}: valid for D >= 2
    try:
        start = known_start(d, D)
    except (ValueError, RuntimeError):
        start = None
    if start is not None and start[0] > best[0] and lib.is_valid(start[0], start[1], d, D):
        best = start

    moore = lib.moore_bound(d, D)
    if best[0] >= moore:
        return best
    if remaining() < 0.5:
        return best

    # Phase 1: the proven lift-and-grow engine, kept as the safe baseline.
    p_budget = remaining() * 0.55
    if p_budget >= 0.5:
        try:
            text = lib.run_c(C_PARENT, [d, D, seed, round(p_budget, 2)],
                             stdin_graph=best, timeout=p_budget + 5)
            n, edges = lib.parse_graph_text(text)
            if n > best[0] and lib.is_valid(n, edges, d, D):
                best = (n, edges)
        except (RuntimeError, ValueError, OSError):
            pass

    # Phase 2: bi-Cayley search over explicit groups. Only orders that beat `best` matter.
    lo = best[0] // 2 + 1
    hi = min(moore // 2, MAX_G)
    if lo <= hi and remaining() > 3.0:
        c_budget = remaining() * 0.9
        if c_budget >= 1.0:
            try:
                cand = _bicayley_candidate(d, D, seed, lo, hi, c_budget)
                if cand is not None:
                    n, edges = cand
                    if n > best[0] and lib.is_valid(n, edges, d, D):
                        best = (n, edges)
            except (RuntimeError, ValueError, OSError, MemoryError):
                pass

    return best
