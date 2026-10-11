"""Group-table lift search (non-metacyclic groups), then grow-by-pairs annealing.

New in this version: the voltage lifts are no longer limited to metacyclic groups Z_m x| Z_k.
Python sends a group description to C, either a semidirect product (m, k, r) or a permutation
group given by generators on at most 16 points (for example PSL(2,7), PGL(2,7), A5 x Z3,
S4 x S3). C builds the full multiplication table, then runs the same lift annealing as before:
a base with kb <= 3 vertices per side, d darts per base vertex, and dart (i, j, s) joining
A_{i,g} to B_{j,g*s}. Left multiplication is an automorphism, so the diameter is checked with
BFS from the 2kb class representatives. Surviving lifts are grown by pairs and repaired by
annealing, with a plateau walk when growth stalls.

Python runs several C jobs, one per candidate group, each starting from the best graph so far.
A valid fallback is kept throughout, and every output is checked with lib.is_valid.
"""
import itertools
import math
import random
import time

import lib

C_SOURCE = r'''
/* Group-table lift search and grow-by-pairs annealing.
 *
 * Usage: prog d D seed time_limit lift_frac kind params...   < start_graph
 *   kind 0: params = m k2 r      semidirect Z_m x| Z_k2, (a,b)(c,e) = (a + r^b c, b + e)
 *   kind 1: params = np ng gens  permutation group on np <= 16 points, ng generators,
 *                                each generator given as np values
 * stdin: "n m" then m edges (a valid start graph, or "0 0").
 * stdout: "n m" then m edges, the largest valid graph found.
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
#define MAXK 3
#define MAXG 1024
#define MAXDART (MAXD * MAXK)
#define MAXPT 16
#define HS 4096
#define BIGCOST 1000000000L

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static double t_end, lift_end;

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

static int GORD = 0;
static int MT[MAXG * MAXG];          /* MT[g*GORD + s] = g * s, identity is index 0 */
static int ELEMP[MAXG][MAXPT];
static uint64_t HKEY[HS];
static int HVAL[HS];
static unsigned char HUSED[HS];

static uint64_t encode_perm(const int *p, int np) {
    uint64_t c = 0;
    for (int x = 0; x < np; x++) c |= (uint64_t)p[x] << (4 * x);
    return c;
}

static size_t hslot(uint64_t k) {
    return (size_t)((k * 0x9E3779B97F4A7C15ULL) >> 52) & (HS - 1);
}

static void hclear(void) { memset(HUSED, 0, sizeof HUSED); }

static int hfind(uint64_t k) {
    size_t h = hslot(k);
    while (HUSED[h]) {
        if (HKEY[h] == k) return HVAL[h];
        h = (h + 1) & (HS - 1);
    }
    return -1;
}

static void hinsert(uint64_t k, int v) {
    size_t h = hslot(k);
    while (HUSED[h]) h = (h + 1) & (HS - 1);
    HUSED[h] = 1;
    HKEY[h] = k;
    HVAL[h] = v;
}

/* Z_m x|_r Z_k2: element a*k2+b, (a,b)(c,e) = (a + r^b c mod m, b+e mod k2). */
static int build_semidirect(int m, int k2, int r) {
    GORD = 0;
    if (m < 1 || k2 < 1 || (long)m * k2 > MAXG) return 0;
    if (m > 1 && gcd(((r % m) + m) % m, m) != 1) return 0;
    r = ((r % m) + m) % m;
    if (powmod(r, k2, m) != 1 % m) return 0;
    int G = m * k2;
    int RP[MAXG];
    RP[0] = 1 % m;
    for (int b = 1; b < k2; b++) RP[b] = (int)((long)RP[b - 1] * r % m);
    for (int x = 0; x < G; x++) {
        int a1 = x / k2, b1 = x % k2;
        for (int y = 0; y < G; y++) {
            int a2 = y / k2, b2 = y % k2;
            int a = (int)(((long)a1 + (long)RP[b1] * a2) % m);
            int b = (b1 + b2) % k2;
            MT[x * G + y] = a * k2 + b;
        }
    }
    GORD = G;
    return 1;
}

/* Permutation group: closure of the generators (identity first), then the full table. */
static int build_perm_group(int np, int ng, const int *gens) {
    GORD = 0;
    if (np < 1 || np > MAXPT || ng < 1 || ng > 8) return 0;
    for (int s = 0; s < ng; s++) {
        int seen[MAXPT];
        for (int x = 0; x < MAXPT; x++) seen[x] = 0;
        for (int x = 0; x < np; x++) {
            int y = gens[s * np + x];
            if (y < 0 || y >= np || seen[y]) return 0;
            seen[y] = 1;
        }
    }
    hclear();
    for (int x = 0; x < np; x++) ELEMP[0][x] = x;
    hinsert(encode_perm(ELEMP[0], np), 0);
    int cnt = 1;
    for (int i = 0; i < cnt; i++) {
        for (int s = 0; s < ng; s++) {
            int h[MAXPT];
            for (int x = 0; x < np; x++) h[x] = ELEMP[i][gens[s * np + x]];
            uint64_t c = encode_perm(h, np);
            if (hfind(c) < 0) {
                if (cnt >= MAXG) return 0;
                memcpy(ELEMP[cnt], h, sizeof(int) * (size_t)np);
                hinsert(c, cnt);
                cnt++;
            }
        }
    }
    for (int a = 0; a < cnt; a++)
        for (int b = 0; b < cnt; b++) {
            int c[MAXPT];
            for (int x = 0; x < np; x++) c[x] = ELEMP[a][ELEMP[b][x]];
            int idx = hfind(encode_perm(c, np));
            if (idx < 0) return 0;
            MT[a * cnt + b] = idx;
        }
    GORD = cnt;
    return 1;
}

/* ------------------------------------------------------------ voltage lifts */

static int KB, ND;
static int DI[MAXDART], DJ[MAXDART], DS[MAXDART];
static int DPERM[MAXDART][MAXG];   /* DPERM[t][g] = g * DS[t] */
static int LADJ[MAXN][MAXD];
static int LDEG[MAXN];
static int VIS[MAXN], VST = 0;
static int QU[MAXN];

static void set_dart_perm(int t) {
    for (int g = 0; g < GORD; g++) DPERM[t][g] = MT[g * GORD + DS[t]];
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

/* One annealing run over voltages and layer permutations for base size kb. */
static int lift_climb(int kb, long steps, Graph *out) {
    KB = kb;
    ND = d * kb;
    for (int l = 0; l < d; l++) {
        int perm[MAXK];
        for (int i = 0; i < kb; i++) perm[i] = i;
        for (int i = kb - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int s = perm[i]; perm[i] = perm[j]; perm[j] = s;
        }
        for (int i = 0; i < kb; i++) {
            int t = l * kb + i;
            DI[t] = i;
            DJ[t] = perm[i];
            DS[t] = rndint(GORD);
            set_dart_perm(t);
        }
    }
    long cost = orbit_cost();
    for (long s = 0; s < steps && cost > 0; s++) {
        if ((s & 31) == 0 && now() > lift_end) return 0;
        double T = 2.0 * (1.0 - (double)s / (double)steps) + 0.05;
        if (rnd01() < 0.7) {
            int t = rndint(ND);
            int old = DS[t];
            int nv = rndint(GORD);
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

/* Lift search with the fixed group. Base size kb is chosen among those whose order is
 * above best->n and within the Moore bound. */
static void lift_search(Graph *best, double until) {
    long moore = moore_bound();
    if (moore > MAXN) moore = MAXN;
    static Graph LCAND;
    int fails = 0;
    while (now() < until) {
        int feas[MAXK], nf = 0;
        for (int kb = 1; kb <= MAXK; kb++) {
            long N = 2L * kb * GORD;
            if (N > moore || N <= best->n) continue;
            feas[nf++] = kb;
        }
        if (nf == 0) return;
        int kb = feas[rndint(nf)];
        long extra = (long)(fails / 20) * 4000;
        if (extra > 60000) extra = 60000;
        long steps = 3000 + rndint(9000) + extra;
        int before = best->n;
        if (lift_climb(kb, steps, &LCAND) && LCAND.n > best->n && is_valid(&LCAND))
            copy_graph(best, &LCAND);
        fails = best->n > before ? 0 : fails + 1;
    }
}

/* ------------------------------------------------------------ repair annealing */

/* Degree-preserving edge-swap annealing on the number of unreached pairs. */
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
    if (argc < 7) {
        fprintf(stderr, "usage: %s d D seed time_limit lift_frac kind params... < start\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double lift_frac = atof(argv[5]);
    int kind = atoi(argv[6]);
    double t0 = now();
    t_end = t0 + limit * 0.97;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 1 || d > MAXD) { printf("1 0\n"); return 0; }
    if (d == 1 || D < 2) { printf("2 1\n0 1\n"); return 0; }

    GORD = 0;
    if (kind == 0 && argc >= 10) {
        build_semidirect(atoi(argv[7]), atoi(argv[8]), atoi(argv[9]));
    } else if (kind == 1 && argc >= 9) {
        int np = atoi(argv[7]), ng = atoi(argv[8]);
        if (np >= 1 && np <= MAXPT && ng >= 1 && ng <= 8 && argc >= 9 + ng * np) {
            static int gens[8 * MAXPT];
            for (int i = 0; i < ng * np; i++) gens[i] = atoi(argv[9 + i]);
            build_perm_group(np, ng, gens);
        }
    }

    static Graph best, start;
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    copy_graph(&start, &best);

    long moore = moore_bound();
    if (best.n < moore) {
        if (GORD > 0 && lift_frac > 0.0) {
            lift_end = t0 + (t_end - t0) * lift_frac;
            lift_search(&best, lift_end);
        }
        if (best.n < moore) grow_search(&best, t_end);
    }
    if (!is_valid(&best)) copy_graph(&best, &start);
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
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


# ------------------------------------------------------------ permutation groups

def _perm_closure(gens, cap):
    """All elements of the group generated by gens (tuples), identity first; None if above cap."""
    n = len(gens[0])
    ident = tuple(range(n))
    elems = [ident]
    index = {ident: 0}
    i = 0
    while i < len(elems):
        g = elems[i]
        i += 1
        for s in gens:
            h = tuple(g[x] for x in s)        # g composed with s
            if h not in index:
                if len(elems) >= cap:
                    return None
                index[h] = len(elems)
                elems.append(h)
    return elems


def _dprod(A, B):
    """Generators of the direct product of two permutation groups on disjoint point sets."""
    na, nb = len(A[0]), len(B[0])
    gens = [tuple(g) + tuple(range(na, na + nb)) for g in A]
    gens += [tuple(range(na)) + tuple(x + na for x in h) for h in B]
    return gens


def _cyc(k):
    return [tuple(list(range(1, k)) + [0])]


def _primroot(p):
    for g in range(2, p):
        x, order = g, 1
        while x != 1:
            x = x * g % p
            order += 1
        if order == p - 1:
            return g
    return 1


def _projline(p, squares):
    """PSL(2,p) (squares=True) or PGL(2,p) acting on the projective line, p+1 points."""
    g = _primroot(p)
    a = g * g % p if squares else g
    inf = p
    t = tuple([(x + 1) % p for x in range(p)] + [inf])
    m = tuple([(a * x) % p for x in range(p)] + [inf])
    inv = []
    for x in range(p + 1):
        if x == inf:
            inv.append(0)
        elif x == 0:
            inv.append(inf)
        else:
            inv.append((-pow(x, p - 2, p)) % p)
    return [t, m, tuple(inv)]


_A5 = [(1, 2, 0, 3, 4), (1, 2, 3, 4, 0)]
_S5 = [(1, 0, 2, 3, 4), (1, 2, 3, 4, 0)]
_A4 = [(1, 2, 0, 3), (1, 0, 3, 2)]
_S4 = [(1, 0, 2, 3), (1, 2, 3, 0)]
_S3 = [(1, 0, 2), (1, 2, 0)]


def _group_catalog():
    psl7 = _projline(7, True)
    pgl7 = _projline(7, False)
    pgl5 = _projline(5, False)
    return [
        ("PSL27", psl7),
        ("PGL27", pgl7),
        ("PSL27xZ2", _dprod(psl7, _cyc(2))),
        ("A5", _A5),
        ("S5", _S5),
        ("PGL25xZ2", _dprod(pgl5, _cyc(2))),
        ("A5xZ2", _dprod(_A5, _cyc(2))),
        ("A5xZ3", _dprod(_A5, _cyc(3))),
        ("A5xZ4", _dprod(_A5, _cyc(4))),
        ("S5xZ2", _dprod(_S5, _cyc(2))),
        ("A4xZ4", _dprod(_A4, _cyc(4))),
        ("A4xA4", _dprod(_A4, _A4)),
        ("A4xS4", _dprod(_A4, _S4)),
        ("S4xS3", _dprod(_S4, _S3)),
        ("S4xZ3", _dprod(_S4, _cyc(3))),
        ("S4xZ4", _dprod(_S4, _cyc(4))),
        ("pgl7xS3", _dprod(pgl7, _S3)),
    ]


def _candidates(d, D, n0, moore, seed):
    """Ordered list of (kind, params) for the C engine: non-metacyclic permutation groups first,
    then semidirect products. Each group has an order that gives a lift above n0 within the bound."""
    rng = random.Random(1000003 * seed + 17)
    moore = min(moore, 4096)
    target = max(n0 + 1, round(0.56 * moore))

    def key_for(G):
        best_key = None
        for kb in range(1, 4):
            N = 2 * kb * G
            if n0 < N <= moore:
                k = abs(N - target)
                if best_key is None or k < best_key:
                    best_key = k
        return best_key

    perm = []
    for name, gens in _group_catalog():
        elems = _perm_closure(gens, 1024)
        if elems is None:
            continue
        key = key_for(len(elems))
        if key is None:
            continue
        perm.append((key, name, gens))
    perm.sort(key=lambda t: (t[0], t[1]))
    cands = []
    for key, name, gens in perm[:4]:
        flat = [x for g in gens for x in g]
        cands.append((1, [len(gens[0]), len(gens), *flat]))

    semi = []
    for G in range(2, min(moore // 2, 1024) + 1):
        key = key_for(G)
        if key is None or key > 80:
            continue
        for m in range(1, G + 1):
            if G % m:
                continue
            k2 = G // m
            if m == 1:
                semi.append((key, m, k2, 0))
                continue
            for r in range(1, m):
                if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m:
                    semi.append((key, m, k2, r))
    rng.shuffle(semi)
    semi.sort(key=lambda t: t[0])
    for key, m, k2, r in semi[:3]:
        cands.append((0, [m, k2, r]))
    return cands


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

    # Stay inside the limit: about 90% of it, minus a 1 s margin for start-up and compile.
    deadline = t0 + 0.9 * time_limit - 1.0
    try:
        cands = _candidates(d, D, best[0], moore, seed)
    except (ValueError, ArithmeticError, RuntimeError):
        cands = []

    for i, (kind, params) in enumerate(cands):
        left = deadline - time.monotonic()
        if left < 2.0:
            break
        slice_t = left / (len(cands) - i)
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed + i, round(slice_t, 2), 0.7, kind, *params],
                             stdin_graph=best, timeout=slice_t + 5)
            n, edges = lib.parse_graph_text(text)
            if n > best[0] and lib.is_valid(n, edges, d, D):
                best = (n, edges)
        except (RuntimeError, ValueError, OSError):
            pass
    return best
