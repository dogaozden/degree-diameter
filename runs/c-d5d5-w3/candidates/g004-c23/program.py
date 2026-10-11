"""Combined search: table-group voltage lifts in C, semidirect lifts as a fallback, then grow-by-pairs annealing.

Python picks a valid start (K_{d,d}, or a known construction for D = 3 or 4) and builds a library of
non-metacyclic permutation groups (symmetric, alternating, PSL/PGL(2,p), affine AGL(1,q), and direct
products) as explicit multiplication tables. The tables are compiled into the C source, so one C run
searches over them. C runs a lift search: a base with kb vertices per side and d darts per base vertex,
with voltages in the chosen group. Left multiplication is an automorphism, so the diameter is checked by
2kb BFS runs from class representatives. With probability 0.8 each attempt uses a table group, which
is a construction family the earlier semidirect-only search never reached. Otherwise it falls back to
the semidirect groups Z_m x| Z_k2. Stalled lift searches get more annealing steps, and the target group
order is raised with failures. The best lift is then grown by repair annealing, with plateau walks.
Every output is re-checked in C and Python, and the best valid graph is always returned.
"""
import itertools
import time

import lib

MARK = "/*GROUP_TABLES*/"

C_SOURCE = r'''
/* Bipartite degree-diameter search core.
 *
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v": a valid start graph, or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * Group tables (GT_TAB / GT_ORD, generated before this code) are multiplication tables
 * with identity at index 0. Dart (i, j, s) joins A_{i,g} to B_{j,g*s}; right multiplication
 * makes left multiplication an automorphism, so the diameter test only needs BFS from the
 * 2kb class representatives.
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

/*GROUP_TABLES*/

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

/* Semidirect Z_m x|_r Z_k2: element a*k2+b, (a,b)(c,e) = (a + r^b c mod m, b+e mod k2). */
static int GM, GK2, GORD;
static int RP[MAXN];
static int TMODE = 0;                 /* 1: multiply with table CURT */
static const short *CURT = NULL;

static void set_group(int m, int k2, int r) {
    TMODE = 0;
    GM = m;
    GK2 = k2;
    GORD = m * k2;
    RP[0] = 1 % m;
    for (int b = 1; b < k2; b++) RP[b] = (int)((long)RP[b - 1] * r % m);
}

static void set_table(int k) {
    TMODE = 1;
    CURT = GT_TAB[k];
    GORD = GT_ORD[k];
}

static int gmul(int x, int y) {
    if (TMODE) return (int)CURT[(long)x * GORD + y];
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

static int KB, ND;
static int DI[MAXDART], DJ[MAXDART], DS[MAXDART];
static int DPERM[MAXDART][MAXN];
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

/* One annealing run over voltages and layer swaps. The caller has already set the group
 * (set_group or set_table) with order G. On success, out holds the full lift. */
static int lift_climb(int kb, int G, long steps, Graph *out) {
    KB = kb;
    ND = d * kb;
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

/* Lift search. Each attempt uses a random table group (probability 0.8, when one fits)
 * or a semidirect group. The target order rises with consecutive failures. */
static void lift_search(Graph *best, double until) {
    long moore = moore_bound();
    int fails = 0;
    static int cand[64];
    while (now() < until) {
        if (best->n + 2 > moore) return;
        int r = rndint(10);
        int kb = r < 3 ? 1 : r < 7 ? 2 : 3;
        long esc = fails > 40 ? (fails - 40) / 40 + 1 : 0;
        if (esc > 6) esc = 6;
        long extra = (long)(fails / 20) * 4000;
        if (extra > 60000) extra = 60000;
        long steps = 3000 + rndint(9000) + extra;
        long need = ((long)best->n + 2 + 2L * kb - 1) / (2L * kb);
        int before = best->n;
        int ok = 0, tried = 0;
        if (NGT_GEN > 0 && rnd01() < 0.8) {
            int nc = 0;
            for (int k = 0; k < NGT_GEN; k++) {
                long o = GT_ORD[k];
                if (o < need || 2L * kb * o > moore || 2L * kb * o > MAXN) continue;
                cand[nc++] = k;
            }
            if (nc > 0) {
                int k = cand[rndint(nc)];
                set_table(k);
                tried = 1;
                ok = lift_climb(kb, GT_ORD[k], steps, &LCAND);
            }
        }
        if (!tried) {
            long G = need + rndint(4) + esc;
            if (G < 1) G = 1;
            if (2L * kb * G > moore || 2L * kb * G > MAXN) { fails++; continue; }
            int m, k2, rr;
            if (!sample_group((int)G, &m, &k2, &rr)) { fails++; continue; }
            set_group(m, k2, rr);
            ok = lift_climb(kb, (int)G, steps, &LCAND);
        }
        if (ok && LCAND.n > best->n && is_valid(&LCAND)) copy_graph(best, &LCAND);
        fails = best->n > before ? 0 : fails + 1;
    }
}

/* ------------------------------------------------------------ repair annealing */

/* Degree-preserving edge-swap annealing on the number of unreached pairs.
 * Returns 1 if the graph becomes a valid diameter-D graph before 'until'. */
static int anneal_repair(Graph *w, double until) {
    long bad = bad_pairs(w);
    double T = 1.0;
    long it = 0;
    while (bad > 0) {
        if ((++it & 15) == 0 && now() > until) return 0;
        int v = rndint(w->n);
        for (int tries = 0; tries < 30 && badv[v] == 0; tries++) v = rndint(w->n);
        if (w->deg[v] == 0) continue;
        int u = w->adj[v][rndint(w->deg[v])];
        int s = rndint(w->n);
        if (w->side[s] != w->side[v] || s == v || w->deg[s] == 0) continue;
        int t = w->adj[s][rndint(w->deg[s])];
        if (t == u || has_edge(w, v, t) || has_edge(w, s, u)) continue;
        del_edge(w, v, u);
        del_edge(w, s, t);
        add_edge(w, v, t);
        add_edge(w, s, u);
        long nb = bad_pairs(w);
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) {
            bad = nb;
        } else {
            del_edge(w, v, t);
            del_edge(w, s, u);
            add_edge(w, v, u);
            add_edge(w, s, t);
        }
        T *= 0.9995;
        if (T < 0.05) T = 1.0;
    }
    return is_valid(w);
}

/* ------------------------------------------------------------ plateau walk */

/* Diversification at fixed order: copy best, apply random degree-preserving swaps,
 * then repair the diameter by annealing. */
static int plateau_walk(const Graph *best, Graph *work, double until, int swaps) {
    copy_graph(work, best);
    int done = 0;
    for (long tries = 0; done < swaps && tries < (long)swaps * 60; tries++) {
        int v = rndint(work->n);
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
        done++;
    }
    return anneal_repair(work, until);
}

/* ------------------------------------------------------------ grow by pairs */

/* Adds g pairs of new vertices (x side 0, y side 1, joined to each other), so the order
 * rises by 2g. Each pair steals d-1 old edges. Then annealing repairs the diameter. */
static int grow_once(const Graph *best, Graph *work, double until, int g) {
    int n = best->n;
    if (g < 1) return 0;
    if (n + 2 * g > moore_bound() || n + 2 * g > MAXN) return 0;
    copy_graph(work, best);
    work->n = n + 2 * g;
    static int used[MAXN];
    static int stamp = 0;
    stamp++;
    for (int p = 0; p < g; p++) {
        int x = n + 2 * p, y = x + 1;
        work->deg[x] = work->deg[y] = 0;
        work->side[x] = 0;
        work->side[y] = 1;
        add_edge(work, x, y);
        used[x] = used[y] = stamp;
    }
    for (int p = 0; p < g; p++) {
        int x = n + 2 * p, y = x + 1;
        for (int k = 0, tries = 0; k < d - 1 && tries < 100000; tries++) {
            int a = rndint(n);
            if (work->side[a] != 0 || used[a] == stamp || work->deg[a] == 0) continue;
            int b = work->adj[a][rndint(work->deg[a])];
            if (b >= n || used[b] == stamp) continue;
            del_edge(work, a, b);
            add_edge(work, x, b);
            add_edge(work, y, a);
            used[a] = used[b] = stamp;
            k++;
        }
    }
    return anneal_repair(work, until);
}

static void grow_search(Graph *best, double until) {
    static Graph work, plat;
    int fails = 0;
    while (now() < until) {
        long lim = moore_bound();
        if (lim > MAXN) lim = MAXN;
        int g = (fails % 3 == 2) ? 2 : 1;
        if (best->n + 2 * g > lim) g = 1;
        if (best->n + 2 * g > lim) break;
        double left = until - now();
        double slice = left < 4.0 ? left : (left / 4 > 4.0 ? left / 4 : 4.0);
        if (grow_once(best, &work, now() + slice, g)) {
            copy_graph(best, &work);
            fails = 0;
        } else {
            fails++;
            if (fails % 12 == 0 && now() < until) {
                double pu = now() + 3.0;
                if (pu > until) pu = until;
                if (plateau_walk(best, &plat, pu, 20 + rndint(40)) && plat.n == best->n)
                    copy_graph(best, &plat);
            }
        }
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


# ------------------------------------------------------------ permutation groups

def _cyc(n, cyc):
    """Permutation of range(n) that maps each entry of cyc to the next one (a cycle)."""
    p = list(range(n))
    for i, a in enumerate(cyc):
        p[a] = cyc[(i + 1) % len(cyc)]
    return tuple(p)


def _sym(n):
    return [_cyc(n, [0, 1]), _cyc(n, list(range(n)))]


def _alt(n):
    return [_cyc(n, [0, 1, k]) for k in range(2, n)]


def _zm(m):
    return [_cyc(m, list(range(m)))]


def _mob(M, p):
    """Action of the matrix (a, b, c, d) on the projective line over Z_p (point p = infinity)."""
    a, b, c, dd = M
    out = []
    for x in range(p + 1):
        if x == p:
            img = p if c % p == 0 else (a * pow(c, -1, p)) % p
        else:
            num = (a * x + b) % p
            den = (c * x + dd) % p
            img = p if den == 0 else (num * pow(den, -1, p)) % p
        out.append(img)
    return tuple(out)


def _prim_root(p):
    for g in range(2, p):
        if len({pow(g, k, p) for k in range(1, p)}) == p - 1:
            return g
    return 1


def _psl(p):
    return [_mob((1, 1, 0, 1), p), _mob((0, p - 1, 1, 0), p)]


def _pgl(p):
    g = _prim_root(p)
    return [_mob((1, 1, 0, 1), p), _mob((0, p - 1, 1, 0), p), _mob((g, 0, 0, 1), p)]


def _agl(q):
    F = lib.GF(q)
    g = F.primitive_element()
    gens = [tuple(F.add(x, e) for x in range(q)) for e in range(1, q)]
    gens.append(tuple(F.mul(g, x) for x in range(q)))
    return gens


def _prod(A, B):
    """Direct product of two permutation groups given by generators (disjoint supports)."""
    n1, n2 = len(A[0]), len(B[0])
    gens = [a + tuple(range(n1, n1 + n2)) for a in A]
    gens += [tuple(range(n1)) + tuple(n1 + x for x in b) for b in B]
    return gens


def _perm_group(gens, limit):
    """Closure of the generators; returns (elements, index) with identity first, or None if too big."""
    n = len(gens[0])
    ident = tuple(range(n))
    elems = [ident]
    idx = {ident: 0}
    i = 0
    while i < len(elems):
        x = elems[i]
        i += 1
        for g in gens:
            y = tuple(x[k] for k in g)
            if y not in idx:
                if len(elems) >= limit:
                    return None
                idx[y] = len(elems)
                elems.append(y)
    return elems, idx


def _mult_table(elems, idx):
    n = len(elems)
    flat = [0] * (n * n)
    for i, a in enumerate(elems):
        for j, b in enumerate(elems):
            c = tuple(a[k] for k in b)   # a o b
            flat[i * n + j] = idx[c]
    return flat


def _named_groups():
    makers = {
        "S3": lambda: _sym(3), "S4": lambda: _sym(4), "S5": lambda: _sym(5),
        "A4": lambda: _alt(4), "A5": lambda: _alt(5), "A6": lambda: _alt(6),
        "PSL25": lambda: _psl(5), "PGL25": lambda: _pgl(5),
        "PSL27": lambda: _psl(7), "PGL27": lambda: _pgl(7), "PGL23": lambda: _pgl(3),
        "AGL7": lambda: _agl(7), "AGL8": lambda: _agl(8), "AGL9": lambda: _agl(9),
        "AGL11": lambda: _agl(11), "AGL13": lambda: _agl(13), "AGL16": lambda: _agl(16),
        "AGL17": lambda: _agl(17), "AGL19": lambda: _agl(19),
        "Z2": lambda: _zm(2), "Z3": lambda: _zm(3), "Z4": lambda: _zm(4),
        "Z5": lambda: _zm(5), "Z7": lambda: _zm(7), "Z10": lambda: _zm(10),
    }
    base = {}
    for name, make in makers.items():
        try:
            base[name] = make()
        except Exception:
            pass
    out = list(base.items())
    pairs = [("S4", "Z2"), ("S4", "Z3"), ("S3", "S3"), ("S3", "S4"), ("A4", "A4"),
             ("A4", "Z3"), ("A4", "Z5"), ("A4", "Z7"), ("A4", "Z10"), ("A5", "Z2"),
             ("A5", "Z3"), ("A5", "Z4"), ("S5", "Z2"), ("PSL27", "Z2"), ("PGL23", "Z2"),
             ("PGL23", "Z3"), ("AGL7", "Z2"), ("AGL7", "Z3"), ("AGL7", "Z4"),
             ("AGL8", "Z2"), ("AGL9", "Z2"), ("AGL11", "Z2"), ("AGL13", "Z2")]
    for A, B in pairs:
        if A in base and B in base:
            try:
                out.append((A + "x" + B, _prod(base[A], base[B])))
            except Exception:
                pass
    return out


def _group_tables(lo, hi, cap):
    """Tables (name, order, flat) for groups with lo <= order <= hi, largest first, total entries <= cap."""
    cands = []
    for name, gens in _named_groups():
        try:
            r = _perm_group(gens, hi + 1)
        except Exception:
            continue
        if r is None:
            continue
        G = len(r[0])
        if lo <= G <= hi:
            cands.append((G, name, r))
    cands.sort(key=lambda t: -t[0])
    out = []
    total = 0
    for G, name, (elems, idx) in cands:
        if total + G * G > cap or len(out) >= 64:
            continue
        out.append((name, G, _mult_table(elems, idx)))
        total += G * G
    return out


def _c_tables(groups):
    """C source text defining NGT_GEN, GT_ORD, and GT_TAB from the tables."""
    if not groups:
        return ("#define NGT_GEN 0\n"
                "static const short GT_DUMMY[1] = {0};\n"
                "static const short *const GT_TAB[1] = {GT_DUMMY};\n"
                "static const int GT_ORD[1] = {0};\n")
    parts = [f"#define NGT_GEN {len(groups)}\n"]
    for k, (name, G, flat) in enumerate(groups):
        parts.append(f"/* {name} */\n")
        parts.append(f"static const short GT{k}[] = {{" + ",".join(map(str, flat)) + "};\n")
    parts.append("static const short *const GT_TAB[] = {"
                 + ",".join(f"GT{k}" for k in range(len(groups))) + "};\n")
    parts.append("static const int GT_ORD[] = {"
                 + ",".join(str(G) for _, G, _ in groups) + "};\n")
    return "".join(parts)


# ------------------------------------------------------------ constructions

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

    moore = lib.moore_bound(d, D)
    if best[0] >= moore:
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 3.0
    if budget < 0.5:
        return best

    try:
        groups = _group_tables(lo=20, hi=min(400, moore // 2), cap=400_000)
        gen = _c_tables(groups)
    except Exception:
        gen = _c_tables([])
    source = C_SOURCE.replace(MARK, gen)

    try:
        text = lib.run_c(source, [d, D, seed, round(budget, 2)],
                         stdin_graph=best, timeout=budget + 30)
        n, edges = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)
    except (RuntimeError, ValueError, OSError):
        pass
    return best
