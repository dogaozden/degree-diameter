"""Bi-Cayley lift search over general finite groups, then grow-by-pairs annealing.

Python builds multiplication tables for several groups (PSL(2,p), PGL(2,p), SL(2,p) for small p,
direct products with cyclic groups, and metacyclic semidirect products) and passes them to C.
The C engine searches bi-Cayley-type lifts: a base with kb <= 3 vertices per side, d darts out of
each base vertex, and voltages in the chosen group. Left multiplication is an automorphism, so the
diameter is checked by BFS from 2*kb representatives. The best lift is then grown by repair
annealing, with plateau walks at fixed order.

Safe fallback: the Python side keeps K_{d,d} (or a known construction) as the starting graph,
which the C engine also receives. Every output is re-checked in C and in Python.
"""
import itertools
import math
import time

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search core, group-table version.
 *
 * Usage:   prog d D seed time_limit   < stream
 * stream:  "ng M" header, then 2M integer tokens (read sequentially):
 *            for each of ng groups: G, then G*G table entries mul[x*G+y] (identity = 0),
 *          then a start graph in the "n m" + m pairs format (n = 0 for none).
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * Lift search: base with kb <= 3 vertices per side, d darts per base vertex. Dart (i, j, s)
 * joins A_{i,g} to B_{j, g*s}. Left multiplication is an automorphism, so diameter <= D iff
 * BFS of depth D from each of the 2kb class representatives reaches everything. Voltages and
 * layer permutations are annealed on the number of unreached pairs. Candidates are all
 * (group, kb) pairs whose lift order lies above the current best.
 * Grow phase: add pairs of vertices, steal edges, repair by annealing; plateau walk at fixed order.
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
#define MAXDART (MAXD * MAXK)
#define BIGCOST 1000000000L
#define MAXGROUPS 96
#define MAXG 512
#define MAXTAB 2400000

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

static int NGRP = 0;
static int GORD[MAXGROUPS];
static long GOFF[MAXGROUPS];
static int GTAB[MAXTAB];
static long TABUSED = 0;
static int CG = 0, GCUR = 1;

static int gmul(int x, int y) { return GTAB[GOFF[CG] + (long)x * GCUR + y]; }

/* Reads the group list. Groups with a bad identity row/column or out-of-range entries are skipped. */
static void read_groups(void) {
    int ng, m;
    NGRP = 0;
    TABUSED = 0;
    if (scanf("%d %d", &ng, &m) != 2) return;
    for (int g = 0; g < ng; g++) {
        int G;
        if (scanf("%d", &G) != 1 || G < 1 || G > MAXG) return;
        long cells = (long)G * G;
        int keep = (TABUSED + cells <= MAXTAB) && NGRP < MAXGROUPS;
        int ok = 1;
        for (long i = 0; i < cells; i++) {
            int v;
            if (scanf("%d", &v) != 1) return;
            if (keep) {
                if (v < 0 || v >= G) ok = 0;
                else GTAB[TABUSED + i] = v;
            }
        }
        if (keep && ok) {
            for (int y = 0; y < G && ok; y++)
                if (GTAB[TABUSED + y] != y) ok = 0;
            for (int x = 0; x < G && ok; x++)
                if (GTAB[TABUSED + (long)x * G] != x) ok = 0;
        }
        if (keep && ok) {
            GORD[NGRP] = G;
            GOFF[NGRP] = TABUSED;
            NGRP++;
            TABUSED += cells;
        }
    }
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
    for (int g = 0; g < GCUR; g++) DPERM[t][g] = gmul(g, DS[t]);
}

static int has_dup(void) {
    for (int t1 = 0; t1 < ND; t1++)
        for (int t2 = t1 + 1; t2 < ND; t2++)
            if (DI[t1] == DI[t2] && DJ[t1] == DJ[t2] && DS[t1] == DS[t2]) return 1;
    return 0;
}

static void build_ladj(void) {
    int N = 2 * KB * GCUR;
    for (int v = 0; v < N; v++) LDEG[v] = 0;
    for (int t = 0; t < ND; t++)
        for (int g = 0; g < GCUR; g++) {
            int a = DI[t] * GCUR + g;
            int b = (KB + DJ[t]) * GCUR + DPERM[t][g];
            LADJ[a][LDEG[a]++] = b;
            LADJ[b][LDEG[b]++] = a;
        }
}

/* Unreached (representative, vertex) pairs over the 2KB class representatives. */
static long orbit_cost(void) {
    if (has_dup()) return BIGCOST;
    build_ladj();
    int N = 2 * KB * GCUR;
    long total = 0;
    for (int rep = 0; rep < 2 * KB; rep++) {
        int src = rep * GCUR;
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
    int N = 2 * KB * GCUR;
    g->n = N;
    for (int v = 0; v < N; v++) { g->deg[v] = 0; g->side[v] = v >= KB * GCUR; }
    for (int t = 0; t < ND; t++)
        for (int x = 0; x < GCUR; x++)
            add_edge(g, DI[t] * GCUR + x, (KB + DJ[t]) * GCUR + DPERM[t][x]);
}

/* One annealing run over voltages and layer permutations for group gi with kb base vertices. */
static int lift_climb(int kb, int gi, long steps, Graph *out) {
    KB = kb;
    ND = d * kb;
    CG = gi;
    GCUR = GORD[gi];
    int G = GCUR;
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

/* Candidates: every (group, kb) with lift order in (best->n, moore]. Half the time choose the
 * candidate with the smallest order above best (step up); otherwise choose uniformly. */
static void lift_search(Graph *best, double until) {
    long moore = moore_bound();
    int fails = 0;
    while (now() < until) {
        if (best->n + 2 > moore) return;
        int cg[MAXGROUPS * MAXK], ck[MAXGROUPS * MAXK], cv[MAXGROUPS * MAXK];
        int nc = 0, minv = 1 << 30;
        for (int g = 0; g < NGRP; g++)
            for (int kb = 1; kb <= MAXK; kb++) {
                long vc = 2L * kb * GORD[g];
                if (vc <= best->n || vc > moore || vc > MAXN) continue;
                cg[nc] = g; ck[nc] = kb; cv[nc] = (int)vc; nc++;
                if (vc < minv) minv = (int)vc;
            }
        if (nc == 0) return;
        int pick = -1;
        if (rnd01() < 0.5) {
            int cnt = 0;
            for (int i = 0; i < nc; i++)
                if (cv[i] == minv && rndint(++cnt) == 0) pick = i;
        } else {
            pick = rndint(nc);
        }
        int g = cg[pick], kb = ck[pick];
        long extra = (long)(fails / 20) * 4000;
        if (extra > 60000) extra = 60000;
        long steps = 3000 + rndint(9000) + extra;
        int before = best->n;
        if (lift_climb(kb, g, steps, &LCAND) && LCAND.n > best->n && is_valid(&LCAND))
            copy_graph(best, &LCAND);
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

/* Adds g pairs of new vertices (x side 0, y side 1, joined), each stealing d-1 old edges,
 * then anneals until the diameter holds. */
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
        fprintf(stderr, "usage: %s d D seed time_limit < stream\n", argv[0]);
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
    read_groups();
    read_start(&start);
    complete_bipartite(&best);
    if (start.n > best.n) copy_graph(&best, &start);

    if (best.n < moore_bound()) {
        if (NGRP > 0) lift_search(&best, t0 + (t_end - t0) * 0.7);
        grow_search(&best, t_end);
    }
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


# ---------------------------------------------------------------- group tables

def _prime_factors(n):
    out = []
    p = 2
    while p * p <= n:
        if n % p == 0:
            out.append(p)
            while n % p == 0:
                n //= p
        p += 1
    if n > 1:
        out.append(n)
    return out


def _prim_root(p):
    fs = _prime_factors(p - 1)
    for g in range(2, p):
        if all(pow(g, (p - 1) // f, p) != 1 for f in fs):
            return g
    return 1


def _closure(gens, mul, norm, cap):
    """Return (G, table) for the group generated by gens; identity is index 0; None if above cap."""
    e = norm((1, 0, 0, 1))
    elems = [e]
    index = {e: 0}
    frontier = [e]
    while frontier:
        nxt = []
        for x in frontier:
            for g in gens:
                y = norm(mul(x, g))
                if y not in index:
                    if len(elems) >= cap:
                        return None
                    index[y] = len(elems)
                    elems.append(y)
                    nxt.append(y)
        frontier = nxt
    G = len(elems)
    table = [0] * (G * G)
    for i, x in enumerate(elems):
        base = i * G
        for j, y in enumerate(elems):
            table[base + j] = index[norm(mul(x, y))]
    return G, table


def _mat_group(p, kind, cap=400):
    """SL(2,p), PSL(2,p) or PGL(2,p) for prime p, as (G, table)."""
    def mul(A, B):
        a, b, c, d = A
        e, f, g, h = B
        return ((a * e + b * g) % p, (a * f + b * h) % p, (c * e + d * g) % p, (c * f + d * h) % p)

    E = (1, 1, 0, 1)
    F = (1, 0, 1, 1)
    if kind == "SL":
        return _closure([E, F], mul, lambda A: A, cap)
    if kind == "PSL":
        def norm(A):
            return min(A, tuple((-x) % p for x in A))
        return _closure([E, F], mul, norm, cap)
    if kind == "PGL":
        def norm(A):
            c = next(x for x in A if x)
            inv = pow(c, p - 2, p)
            return tuple(x * inv % p for x in A)
        g = _prim_root(p)
        return _closure([E, F, (g, 0, 0, 1)], mul, norm, cap)
    raise ValueError(kind)


def _direct(base, k):
    """Direct product of base = (G1, T1) with cyclic Z_k; element index x*k+b."""
    if base is None:
        raise ValueError("no base group")
    G1, T1 = base
    G = G1 * k
    T = [0] * (G * G)
    for x in range(G1):
        for b in range(k):
            i = x * k + b
            for y in range(G1):
                z1 = T1[x * G1 + y]
                for c in range(k):
                    j = y * k + c
                    T[i * G + j] = z1 * k + (b + c) % k
    return G, T


def _semidirect(m, k, r):
    order, mul, _inv = lib.semidirect_group(m, k, r)
    return order, [mul(x, y) for x in range(order) for y in range(order)]


def _metacyclic_specs(hi, lo, want):
    """Pick (m, k, r) with m*k = G, r != 1, r^k = 1 mod m, one per order, G from hi down to lo."""
    out = []
    for G in range(hi, lo - 1, -1):
        found = None
        for k in range(2, G):
            if G % k:
                continue
            m = G // k
            if m < 3:
                continue
            for r in range(2, m):
                if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                    found = (m, k, r)
                    break
            if found:
                break
        if found:
            out.append(found)
            if len(out) >= want:
                break
    return out


def _group_thunks():
    th = [
        lambda: _mat_group(7, "PSL"),
        lambda: _mat_group(7, "PGL"),
        lambda: _mat_group(7, "SL"),
        lambda: _mat_group(5, "PSL"),
        lambda: _mat_group(5, "PGL"),
        lambda: _mat_group(5, "SL"),
        lambda: _direct(_mat_group(7, "PSL"), 2),
        lambda: _direct(_mat_group(5, "PGL"), 2),
        lambda: _direct(_mat_group(5, "SL"), 2),
    ]
    for k in (2, 3, 4, 5):
        th.append(lambda k=k: _direct(_mat_group(5, "PSL"), k))
    for m, k, r in _metacyclic_specs(340, 177, 8) + _metacyclic_specs(176, 60, 10):
        th.append(lambda m=m, k=k, r=r: _semidirect(m, k, r))
    return th


def _make_groups(deadline, cap_entries=2_000_000):
    groups = []
    total = 0
    for make in _group_thunks():
        if time.monotonic() > deadline:
            break
        try:
            res = make()
        except Exception:
            continue
        if res is None:
            continue
        G, T = res
        if G < 2 or G > 400 or total + G * G > cap_entries:
            continue
        groups.append((G, T))
        total += G * G
    return groups


def _stream(groups, start):
    """Flatten groups and the start graph into the stdin token stream read by the C engine.

    The header 'ng M' is written by lib.graph_to_text; the remaining tokens are read sequentially.
    """
    rest = []
    for G, T in groups:
        rest.append(G)
        rest.extend(T)
    sn, se = start
    rest.extend([sn, len(se)])
    for u, v in se:
        rest.extend((u, v))
    if len(rest) % 2:
        rest.append(0)
    return len(groups), [(rest[i], rest[i + 1]) for i in range(0, len(rest), 2)]


# ---------------------------------------------------------------- constructions

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


# ---------------------------------------------------------------- entry point

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

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if budget < 0.5:
        return best

    try:
        groups = _make_groups(t0 + 0.25 * budget)
    except Exception:
        groups = []

    try:
        ng, edges = _stream(groups, best)
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=(ng, edges), timeout=budget + 5)
        n, out_edges = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, out_edges, d, D):
            best = (n, out_edges)
    except (RuntimeError, ValueError, OSError, MemoryError):
        pass
    return best
