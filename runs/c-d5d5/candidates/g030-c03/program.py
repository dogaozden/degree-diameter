"""Two-stage search: group Haar graphs in C, then the parent's lift/grow annealing.

Stage 1 (new construction): the Haar graph H(G, S) of a finite group G has vertices A_g and B_g,
with A_g adjacent to B_{gs} for s in S, |S| = d. Left multiplication is an automorphism, so the
diameter is at most D iff a depth-D BFS from A_e and from B_e reaches all 2|G| vertices. Python
builds non-abelian and mixed groups as permutation groups (direct products of A_n, S_n, dihedral
and cyclic factors) and passes the Cayley table to C. C anneals the connection set S.

Stage 2: the best graph so far is handed to the parent's C engine (voltage lifts + grow-by-two).

Every candidate is checked with lib.is_valid. The fallback is always a valid graph: the best of
K_{d,d}, the known construction, and any verified result from either stage.
"""
import itertools
import math
import time

import numpy as np

import lib

C_SOURCE = r'''
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
 *   layer swaps are annealed on the number of unreached pairs.
 *   Escalations when stuck: (a) annealing runs get more steps, (b) the target group order
 *   is raised (group-order escalation).
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

C_HAAR = r'''
/* Haar graph search over a finite group.
 *
 * Usage:  prog d D seed time_limit
 * stdin:  "G m" with m = G*G, then m lines "u v": the product table, MUL[u/G][u%G] = v,
 *         with the identity at index 0.
 * stdout: "n m" then edges of a valid bipartite graph with degree d and diameter <= D,
 *         or "0 0" if none was found.
 *
 * Haar graph H(G,S): A_g (index g) adjacent to B_{g*s} (index G + g*s) for s in S, |S| = d.
 * Left multiplication is an automorphism, so diameter <= D iff a depth-D BFS from A_e and
 * from B_e reaches all 2G vertices. Annealing over the d-subset S minimises unreached pairs.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXG 512
#define MAXDD 32

static int G, d, D;
static int MUL[MAXG][MAXG];
static int INV[MAXG];
static int S[MAXDD], SI[MAXDD];
static int vis[2 * MAXG];
static int qu[2 * MAXG];
static int stamp = 0;
static double t_end;
static uint64_t rs = 88172645463325252ULL;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

/* Vertices unreached by a depth-D BFS from src (0 = A_e, G = B_e). */
static long unreached(int src) {
    stamp++;
    int head = 0, tail = 0;
    vis[src] = stamp;
    qu[tail++] = src;
    for (int depth = 0; depth < D && head < tail; depth++) {
        int end = tail;
        while (head < end) {
            int u = qu[head++];
            if (u < G) {
                for (int k = 0; k < d; k++) {
                    int v = G + MUL[u][S[k]];
                    if (vis[v] != stamp) { vis[v] = stamp; qu[tail++] = v; }
                }
            } else {
                int x = u - G;
                for (int k = 0; k < d; k++) {
                    int v = MUL[x][SI[k]];
                    if (vis[v] != stamp) { vis[v] = stamp; qu[tail++] = v; }
                }
            }
        }
    }
    return 2L * G - tail;
}

static long cost(void) { return unreached(0) + unreached(G); }

static void set_si(int k) { SI[k] = INV[S[k]]; }

static int in_prefix(int x, int cnt) {
    for (int k = 0; k < cnt; k++)
        if (S[k] == x) return 1;
    return 0;
}

static int in_s(int x) { return in_prefix(x, d); }

int main(int argc, char **argv) {
    if (argc < 5) return 2;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    t_end = now() + limit;

    int m;
    if (scanf("%d %d", &G, &m) != 2 || G < 1 || G > MAXG || m != G * G ||
        d < 1 || d > MAXDD || d >= G || D < 1) {
        printf("0 0\n");
        return 0;
    }
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || u >= m || v < 0 || v >= G) {
            printf("0 0\n");
            return 0;
        }
        MUL[u / G][u % G] = v;
    }
    for (int j = 0; j < G; j++)
        if (MUL[0][j] != j || MUL[j][0] != j) { printf("0 0\n"); return 0; }
    for (int j = 0; j < G; j++)
        for (int x = 0; x < G; x++)
            if (MUL[j][x] == 0) INV[j] = x;

    int found = 0;
    while (!found && now() < t_end) {
        for (int k = 0; k < d; k++) {
            int x;
            do { x = rndint(G); } while (in_prefix(x, k));
            S[k] = x;
            set_si(k);
        }
        long cur = cost();
        if (cur == 0) { found = 1; break; }
        long R = 20000;
        for (long s = 0; s < R; s++) {
            if ((s & 127) == 0 && now() > t_end) break;
            double T = 1.0 * (1.0 - (double)s / (double)R) + 0.03;
            int k = rndint(d);
            int nv;
            do { nv = rndint(G); } while (in_s(nv));
            int old = S[k];
            S[k] = nv;
            set_si(k);
            long c = cost();
            if (c <= cur || rnd01() < exp(-(double)(c - cur) / T)) {
                cur = c;
                if (cur == 0) { found = 1; break; }
            } else {
                S[k] = old;
                set_si(k);
            }
        }
    }
    if (!found) { printf("0 0\n"); return 0; }
    printf("%d %d\n", 2 * G, G * d);
    for (int g = 0; g < G; g++)
        for (int k = 0; k < d; k++)
            printf("%d %d\n", g, G + MUL[g][S[k]]);
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


# ------------------------------------------------------- group constructions

# Each spec is a direct product of factors: ("A", n) alternating, ("S", n) symmetric,
# ("Z", m) cyclic, ("D", m) dihedral of order 2m.
GROUP_SPECS = [
    [("A", 5), ("Z", 3)],               # 180
    [("D", 90)],                        # 180
    [("A", 4), ("Z", 15)],              # 180
    [("A", 4), ("D", 8)],               # 192
    [("S", 4), ("Z", 8)],               # 192
    [("A", 4), ("Z", 16)],              # 192
    [("D", 96)],                        # 192
    [("S", 4), ("Z", 2), ("Z", 4)],     # 192
    [("A", 4), ("Z", 3), ("Z", 6)],     # 216
    [("D", 100)],                       # 200
    [("A", 5), ("Z", 2), ("Z", 2)],     # 240
    [("A", 5), ("Z", 4)],               # 240
    [("S", 5), ("Z", 2)],               # 240
    [("S", 4), ("Z", 10)],              # 240
    [("A", 4), ("Z", 20)],              # 240
    [("A", 4), ("D", 10)],              # 240
    [("S", 4), ("D", 5)],               # 240
    [("D", 120)],                       # 240
    [("A", 5), ("Z", 5)],               # 300
    [("A", 4), ("Z", 25)],              # 300
    [("S", 4), ("Z", 11)],              # 264
    [("S", 4), ("Z", 12)],              # 288
    [("A", 4), ("Z", 24)],              # 288
    [("S", 4), ("Z", 13)],              # 312
    [("S", 4), ("Z", 14)],              # 336
]


def _spec_order(spec):
    o = 1
    for kind, size in spec:
        if kind == "A":
            o *= math.factorial(size) // 2
        elif kind == "S":
            o *= math.factorial(size)
        elif kind == "Z":
            o *= size
        else:
            o *= 2 * size
    return o


def _factor_gens(kind, size, off):
    """Generators of one factor on points off..off+size-1; each generator is a list of cycles."""
    if kind == "A":
        return [[[off, off + 1, off + k]] for k in range(2, size)]
    if kind == "S":
        return [[[off, off + 1]], [list(range(off, off + size))]]
    if kind == "Z":
        return [[list(range(off, off + size))]] if size >= 2 else []
    m = size  # dihedral
    refl = [[off + i, off + m - i] for i in range(1, (m - 1) // 2 + 1)]
    return [[list(range(off, off + m))], refl]


def _perm_from_cycles(N, cycles):
    p = list(range(N))
    for c in cycles:
        L = len(c)
        for i in range(L):
            p[c[i]] = c[(i + 1) % L]
    return tuple(p)


def _spec_perms(spec):
    N = sum(size for _, size in spec)
    gens = []
    off = 0
    for kind, size in spec:
        for g in _factor_gens(kind, size, off):
            gens.append(_perm_from_cycles(N, g))
        off += size
    return N, gens


def _group_table(spec, cap):
    """Cayley table (G, flat row-major list) of the permutation group of spec, identity at index 0.
    Returns None if the closure does not have exactly cap elements."""
    N, gens = _spec_perms(spec)
    e = tuple(range(N))
    els = [e]
    index = {e: 0}
    parent = [-1]
    gen_of = [-1]
    qi = 0
    while qi < len(els):
        x = els[qi]
        for gi, g in enumerate(gens):
            y = tuple(x[i] for i in g)
            if y not in index:
                if len(els) >= cap:
                    return None
                index[y] = len(els)
                els.append(y)
                parent.append(qi)
                gen_of.append(gi)
        qi += 1
    G = len(els)
    if G != cap:
        return None
    # Rg[g][x] = index of el[x] * gen_g (right multiplication by each generator).
    Rg = np.array([[index[tuple(x[i] for i in g)] for x in els] for g in gens], dtype=np.int64)
    M = np.zeros((G, G), dtype=np.int64)
    M[:, 0] = np.arange(G)
    for j in range(1, G):
        # el[j] = el[parent[j]] * gen, so el[i] * el[j] = Rg[gen][el[i] * el[parent[j]]].
        M[:, j] = Rg[gen_of[j]][M[:, parent[j]]]
    return G, M.ravel().tolist()


def _haar_phase(d, D, seed, best, t_stop):
    """Try Haar graphs over the candidate groups in increasing order; keep the best verified result."""
    hi = min(340, lib.moore_bound(d, D) // 2)
    specs = []
    for spec in GROUP_SPECS:
        order = _spec_order(spec)
        if best[0] // 2 < order <= hi and order > d:
            specs.append((order, spec))
    specs.sort(key=lambda t: t[0])
    for idx, (order, spec) in enumerate(specs):
        if 2 * order <= best[0]:
            continue
        remaining = t_stop - time.monotonic()
        left = len(specs) - idx
        slot = min(4.0, remaining / left)
        if slot < 0.6:
            break
        table = _group_table(spec, order)
        if table is None:
            continue
        G, flat = table
        try:
            text = lib.run_c(C_HAAR, [d, D, seed + idx, round(slot, 2)],
                             stdin_graph=(G, list(enumerate(flat))), timeout=slot + 5)
            n, edges = lib.parse_graph_text(text)
        except Exception:
            continue
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)
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
    except Exception:
        start = None
    if start is not None and start[0] > best[0] and lib.is_valid(start[0], start[1], d, D):
        best = start

    if best[0] >= lib.moore_bound(d, D):
        return best

    deadline = t0 + 0.85 * time_limit - 1.5
    if deadline - time.monotonic() < 2.0:
        return best

    # Stage 1: Haar graphs over groups (new construction).
    haar_end = time.monotonic() + 0.4 * (deadline - time.monotonic())
    try:
        best = _haar_phase(d, D, seed, best, haar_end)
    except Exception:
        pass

    # Stage 2: the parent's lift and grow search, started from the best graph so far.
    remaining = deadline - time.monotonic()
    if remaining > 1.5:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(remaining, 2)],
                             stdin_graph=best, timeout=remaining + 5)
            n, edges = lib.parse_graph_text(text)
            if n > best[0] and lib.is_valid(n, edges, d, D):
                best = (n, edges)
        except Exception:
            pass
    return best
