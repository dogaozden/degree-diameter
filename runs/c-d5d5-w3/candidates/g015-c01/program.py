"""Two-stage search: parent lift search in C, then a bi-Cayley (Haar-type) scan over semidirect groups.

Stage A runs the proven parent engine (semidirect voltage lifts with grow-by-two). It keeps the
best valid graph found so far.

Stage B is a new construction family. For a group G of order g, the bi-Cayley graph has vertices
A_x and B_x for x in G, and edges A_x - B_{x*s} for s in S, where |S| = d. Left multiplication is an
automorphism that preserves both sides, so the diameter is <= D iff BFS of depth D from A_1 and from
B_1 reaches every vertex. Each check is therefore two BFS runs, so many thousands of (group, S)
candidates can be tried. Identity is always in S, because right-multiplying S by a fixed element gives
an isomorphic graph. Groups are semidirect products Z_m x| Z_k2 for all factorisations of g. The scan
goes up in order, starting just above the current best order, and repeats with longer annealing runs
on each pass.

Every stage only replaces the best graph with a larger graph that passes lib.is_valid. If a stage fails
or times out, the previous graph is kept, so the output is always valid.
"""
import itertools
import time

import lib

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
 * Phase 2 (grow by two): add one vertex per side, then anneal. Moves are either a random
 *   degree-preserving 2-switch or a bridge move that adds an edge across a bad pair.
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
        if (rnd01() < 0.5) {
            /* Bridge move: add the edge v-w across a bad pair, removing (v,a) and (w,b).
             * Degrees are unchanged. a is on w's side and b is on v's side. */
            int w = rndint(work->n);
            if (w == v || work->side[w] == work->side[v] || has_edge(work, v, w)) continue;
            if (work->deg[w] == 0) continue;
            int a = work->adj[v][rndint(work->deg[v])];
            int b = work->adj[w][rndint(work->deg[w])];
            if (a == w || b == v || has_edge(work, a, b)) continue;
            del_edge(work, v, a);
            del_edge(work, w, b);
            add_edge(work, v, w);
            add_edge(work, a, b);
            long nb = bad_pairs(work);
            if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) {
                bad = nb;
            } else {
                del_edge(work, v, w);
                del_edge(work, a, b);
                add_edge(work, v, a);
                add_edge(work, w, b);
            }
        } else {
            /* Random degree-preserving 2-switch. */
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
    t_end = t0 + limit * 0.95;
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

C_BICAYLEY = r'''
/* Bi-Cayley scan over semidirect groups Z_m x|_r Z_k2 (order g).
 *
 * Graph: vertices A_x = x, B_x = g + x (x in G). Edges A_x - B_{x*s} for s in S, |S| = d.
 * Left multiplication is an automorphism preserving sides, so diameter <= D iff BFS of depth D
 * from A_identity and from B_identity reaches all 2g vertices. Identity is always in S (WLOG,
 * because right-multiplying S gives an isomorphic graph).
 *
 * stdin:  start graph text ("n m" ...); echoed back if nothing better is found.
 * stdout: "n m" then edges of the largest bi-Cayley graph found with n > start n, or the start text.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXG 1024
#define MAXD 32
#define MAXENUM 512

static int d, D;
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

static int gcd_i(int a, int b) {
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

/* ------------------------------------------------------------ group tables */

static int G;                 /* current group order */
static int MT[MAXG][MAXG];    /* multiplication table */
static int INV[MAXG];         /* inverses; identity is index 0 */

static void build_group(int m, int k2, int r) {
    static int RP[MAXG];
    G = m * k2;
    RP[0] = 1 % m;
    for (int b = 1; b < k2; b++) RP[b] = (int)((long)RP[b - 1] * r % m);
    for (int x = 0; x < G; x++) {
        int a = x / k2, b = x % k2;
        for (int y = 0; y < G; y++) {
            int c = y / k2, e = y % k2;
            MT[x][y] = (int)(((long)a + (long)RP[b] * c) % m) * k2 + (b + e) % k2;
        }
    }
    for (int x = 0; x < G; x++)
        for (int y = 0; y < G; y++)
            if (MT[x][y] == 0) { INV[x] = y; break; }
}

/* All semidirect (m, k2, r) with m * k2 = gn, up to cap entries. */
static int enum_groups(int gn, int *gm, int *gk, int *gr, int cap) {
    int c = 0;
    for (int m = 1; m <= gn; m++) {
        if (gn % m) continue;
        int k2 = gn / m;
        if (m == 1) {
            if (c < cap) { gm[c] = 1; gk[c] = k2; gr[c] = 0; c++; }
            continue;
        }
        if (k2 == 1) {
            if (c < cap) { gm[c] = m; gk[c] = 1; gr[c] = 1; c++; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd_i(r, m) != 1 || powmod(r, k2, m) != 1 % m) continue;
            if (c < cap) { gm[c] = m; gk[c] = k2; gr[c] = r; c++; }
        }
    }
    return c;
}

static void shuffle3(int *a, int *b, int *c, int n) {
    for (int i = n - 1; i > 0; i--) {
        int j = rndint(i + 1), t;
        t = a[i]; a[i] = a[j]; a[j] = t;
        t = b[i]; b[i] = b[j]; b[j] = t;
        t = c[i]; c[i] = c[j]; c[j] = t;
    }
}

/* ------------------------------------------------------------ connection set search */

static int S[MAXD], SI[MAXD];
static int VIS[2 * MAXG], vst = 0, Q[2 * MAXG];

/* Number of unreached (source, vertex) pairs for sources A_0 and B_0. Zero iff diameter <= D. */
static long cost_of(void) {
    int N = 2 * G;
    long total = 0;
    for (int rep = 0; rep < 2; rep++) {
        int src = rep ? G : 0;
        vst++;
        int head = 0, tail = 0;
        VIS[src] = vst;
        Q[tail++] = src;
        for (int depth = 0; depth < D && head < tail; depth++) {
            int end = tail;
            while (head < end) {
                int u = Q[head++];
                if (u < G) {
                    for (int i = 0; i < d; i++) {
                        int v = MT[u][S[i]] + G;
                        if (VIS[v] != vst) { VIS[v] = vst; Q[tail++] = v; }
                    }
                } else {
                    int y = u - G;
                    for (int i = 0; i < d; i++) {
                        int v = MT[y][SI[i]];
                        if (VIS[v] != vst) { VIS[v] = vst; Q[tail++] = v; }
                    }
                }
            }
        }
        total += N - tail;
    }
    return total;
}

static int in_set(int x, int k) {
    for (int i = 0; i < k; i++)
        if (S[i] == x) return 1;
    return 0;
}

/* Annealing over S (identity fixed in S[0]). Returns 1 with a valid S in S[]. */
static int climb(long steps) {
    S[0] = 0;
    for (int i = 1; i < d; i++) {
        int x;
        do { x = rndint(G); } while (in_set(x, i));
        S[i] = x;
    }
    for (int i = 0; i < d; i++) SI[i] = INV[S[i]];
    long cost = cost_of();
    for (long s = 0; s < steps && cost > 0; s++) {
        if ((s & 255) == 0 && now() > t_end) return 0;
        double T = 1.5 * (1.0 - (double)s / (double)steps) + 0.05;
        int i = 1 + rndint(d - 1);
        int x = rndint(G);
        if (in_set(x, d)) continue;
        int old = S[i];
        S[i] = x;
        SI[i] = INV[x];
        long c2 = cost_of();
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
            cost = c2;
        } else {
            S[i] = old;
            SI[i] = INV[old];
        }
    }
    return cost == 0;
}

static int try_group(int m, int k2, int r, long steps) {
    build_group(m, k2, r);
    if (d > G) return 0;
    return climb(steps);
}

/* ------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit < graph\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit * 0.95;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    /* Read the whole start graph so it can be echoed back. */
    size_t cap = 1 << 16, len = 0;
    char *buf = malloc(cap);
    if (!buf) return 1;
    for (;;) {
        if (len == cap) {
            cap *= 2;
            char *nb = realloc(buf, cap);
            if (!nb) return 1;
            buf = nb;
        }
        size_t got = fread(buf + len, 1, cap - len, stdin);
        if (got == 0) break;
        len += got;
    }
    char *nb = realloc(buf, len + 1);
    if (!nb) return 1;
    buf = nb;
    buf[len] = 0;

    long n0 = 0;
    if (sscanf(buf, "%ld", &n0) != 1) n0 = 0;

    if (d < 2 || D < 2 || d > MAXD) {
        fwrite(buf, 1, len, stdout);
        return 0;
    }

    long mb = moore_bound();
    long hi_l = mb / 2;
    if (hi_l > MAXG - 1) hi_l = MAXG - 1;
    int hi = (int)hi_l;
    int lo = (int)(n0 / 2) + 1;
    if (lo < 1) lo = 1;

    int have = 0, bestG = 0, bm = 0, bk = 0, br = 0;
    int bS[MAXD];
    static int gm[MAXENUM], gk[MAXENUM], gr[MAXENUM];

    for (int pass = 0; now() < t_end && pass < 12; pass++) {
        int G0 = have ? bestG + 1 : lo;
        if (G0 > hi) break;
        long steps = 2000L << pass;
        if (steps > 60000) steps = 60000;
        int take_base = 8 + 4 * pass;
        for (int Gt = G0; Gt <= hi && now() < t_end; Gt++) {
            if (Gt < d) continue;
            int ng = enum_groups(Gt, gm, gk, gr, MAXENUM);
            shuffle3(gm, gk, gr, ng);
            int take = take_base < ng ? take_base : ng;
            for (int t = 0; t < take && now() < t_end; t++) {
                if (try_group(gm[t], gk[t], gr[t], steps)) {
                    have = 1;
                    bestG = Gt;
                    bm = gm[t];
                    bk = gk[t];
                    br = gr[t];
                    memcpy(bS, S, sizeof(int) * d);
                    break;
                }
            }
        }
    }

    if (have) {
        build_group(bm, bk, br);
        printf("%d %ld\n", 2 * bestG, (long)bestG * d);
        for (int x = 0; x < bestG; x++)
            for (int i = 0; i < d; i++)
                printf("%d %d\n", x, bestG + MT[x][bS[i]]);
    } else {
        fwrite(buf, 1, len, stdout);
    }
    free(buf);
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


def _run_stage(source, args, start, d, D, budget, best):
    """Run one C stage on `start`; return the new graph if it is larger and valid, else `best`."""
    try:
        text = lib.run_c(source, args, stdin_graph=start, timeout=budget + 3)
        n, edges = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, edges, d, D):
            return (n, edges)
    except (RuntimeError, ValueError, OSError):
        pass
    return best


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
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

    if best[0] >= lib.moore_bound(d, D):
        return best

    def remaining():
        # Use most of the limit; keep a margin for compilation and process startup.
        return 0.92 * time_limit - (time.monotonic() - t0) - 1.5

    # Stage A: proven parent lift search (keeps the known-good result as the baseline).
    budget_a = 0.6 * remaining()
    if budget_a >= 0.5:
        best = _run_stage(C_PARENT, [d, D, seed, round(budget_a, 2)],
                          best, d, D, budget_a, best)

    # Stage B: bi-Cayley scan over semidirect groups, started from the stage-A graph.
    budget_b = remaining() - 1.0
    if budget_b >= 0.5:
        best = _run_stage(C_BICAYLEY, [d, D, seed + 1, round(budget_b, 2)],
                          best, d, D, budget_b, best)

    return best
