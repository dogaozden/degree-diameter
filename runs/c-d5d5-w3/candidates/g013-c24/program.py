"""Non-metacyclic group-lift search with grow-by-two annealing.

The parent family used semidirect products Z_m x| Z_k only. This version draws the
base group from a pool of non-metacyclic groups (A5 x Z3, S5 x Z2, PGL(2,7), PSL(2,7) x Z2,
ASL(2,3), S4 x A4, Z2 wr A4, Z3 wr Z3, ...) and adds a few semidirect products as well.
Each group is passed to C as a multiplication table. C runs voltage lifts with kb base
vertices per side (2 kb BFS checks per candidate, since left multiplication is an
automorphism), then grows the best lift by two with annealing. If nothing beats the
fallback, the fallback is returned.
"""
import itertools
import math
import random
import time

import numpy as np

import lib

C_SOURCE = r'''
/* Group-lift search over tables of finite groups, then grow-by-two annealing.
 *
 * Usage:  prog d D seed time_limit < stdin
 * stdin:  a header "h1 h2" (ignored), then for each group: G, then G*G integers
 *         (the multiplication table, row-major, identity = index 0).
 * stdout: "n m" then m lines "u v" for the best valid graph found.
 *
 * Lift: base with kb vertices per side; d darts out of each base vertex (one per layer;
 * each layer is a permutation of the kb base vertices). Dart (i, j, s) joins A_{i,g} to
 * B_{j, g*s}. Left multiplication by h is an automorphism, so diameter <= D iff a BFS
 * of depth D from each of the 2kb representatives A_i, B_j reaches everything.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 2048
#define MAXD 32
#define MAXW (MAXN / 64)
#define MAXK 3
#define MAXDART (MAXD * MAXK)
#define MAXG 340
#define MAXNG 48
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

static int NG = 0;
static int GORD[MAXNG];
static int GSORT[MAXNG];
static unsigned short GT[MAXNG][MAXG][MAXG];

static void read_groups(void) {
    int h1, h2, k = 0;
    NG = 0;
    if (scanf("%d %d", &h1, &h2) != 2) return;
    while (k < MAXNG) {
        int G, good = 1, eof = 0;
        if (scanf("%d", &G) != 1) break;
        if (G < 1 || G > MAXG) break;
        for (int x = 0; x < G && !eof; x++)
            for (int y = 0; y < G; y++) {
                int v;
                if (scanf("%d", &v) != 1) { eof = 1; break; }
                if (v < 0 || v >= G) good = 0;
                else GT[k][x][y] = (unsigned short)v;
            }
        if (eof) break;
        for (int y = 0; y < G && good; y++)
            if (GT[k][0][y] != y || GT[k][y][0] != y) good = 0;
        if (good) {
            GORD[k] = G;
            k++;
        }
    }
    NG = k;
    for (int i = 0; i < NG; i++) GSORT[i] = i;
    for (int i = 1; i < NG; i++) {
        int j = i;
        while (j > 0 && GORD[GSORT[j - 1]] > GORD[GSORT[j]]) {
            int t = GSORT[j - 1]; GSORT[j - 1] = GSORT[j]; GSORT[j] = t;
            j--;
        }
    }
}

/* ------------------------------------------------------------ voltage lifts */

static int KB, ND, GI, GG;
static int DI[MAXDART], DJ[MAXDART], DS[MAXDART];
static int LADJ[MAXN][MAXD];
static int LDEG[MAXN];
static int VIS[MAXN], VST = 0;
static int QU[MAXN];

static int has_dup(void) {
    for (int t1 = 0; t1 < ND; t1++)
        for (int t2 = t1 + 1; t2 < ND; t2++)
            if (DI[t1] == DI[t2] && DJ[t1] == DJ[t2] && DS[t1] == DS[t2]) return 1;
    return 0;
}

static void build_ladj(void) {
    int N = 2 * KB * GG;
    for (int v = 0; v < N; v++) LDEG[v] = 0;
    for (int t = 0; t < ND; t++)
        for (int g = 0; g < GG; g++) {
            int a = DI[t] * GG + g;
            int b = (KB + DJ[t]) * GG + GT[GI][g][DS[t]];
            LADJ[a][LDEG[a]++] = b;
            LADJ[b][LDEG[b]++] = a;
        }
}

/* Unreached (representative, vertex) pairs over the 2KB class representatives. */
static long orbit_cost(void) {
    if (has_dup()) return BIGCOST;
    build_ladj();
    int N = 2 * KB * GG;
    long total = 0;
    for (int rep = 0; rep < 2 * KB; rep++) {
        int src = rep * GG;
        if (++VST == 0x3fffffff) { memset(VIS, 0, sizeof(VIS)); VST = 1; }
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
    int N = 2 * KB * GG;
    g->n = N;
    for (int v = 0; v < N; v++) { g->deg[v] = 0; g->side[v] = v >= KB * GG; }
    for (int t = 0; t < ND; t++)
        for (int x = 0; x < GG; x++)
            add_edge(g, DI[t] * GG + x, (KB + DJ[t]) * GG + GT[GI][x][DS[t]]);
}

/* One annealing run over voltages and layer swaps for group gi with kb base vertices. */
static int lift_climb(int kb, int gi, long steps, Graph *out) {
    KB = kb;
    ND = d * kb;
    GI = gi;
    GG = GORD[gi];
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
            DS[t] = rndint(GG);
        }
    }
    long cost = orbit_cost();
    for (long s = 0; s < steps && cost > 0; s++) {
        if ((s & 31) == 0 && now() > t_end) return 0;
        double T = 1.5 * (1.0 - (double)s / (double)steps) + 0.05;
        if (rnd01() < 0.6) {
            int t = rndint(ND);
            int old = DS[t];
            int nv = rndint(GG);
            if (nv == old) continue;
            DS[t] = nv;
            long c2 = orbit_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) cost = c2;
            else DS[t] = old;
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

static int ELIG[MAXNG];
static Graph LCAND;

/* Repeated lift attempts. Candidate groups are those whose lift order 2*kb*G is at least
 * best+2; the smallest few are preferred, widening after repeated failures. */
static void lift_search(Graph *best, double until) {
    if (NG == 0) return;
    long cap = moore_bound();
    if (cap > MAXN) cap = MAXN;
    int fails = 0;
    while (now() < until) {
        if (best->n + 2 > cap) return;
        int kb = 1 + rndint(3);
        int cnt = 0;
        for (int q = 0; q < NG; q++) {
            int k = GSORT[q];
            long N2 = 2L * kb * GORD[k];
            if (N2 >= best->n + 2 && N2 <= cap) ELIG[cnt++] = k;
        }
        if (cnt == 0) { fails++; continue; }
        int lim = 2 + fails / 8;
        if (lim > cnt) lim = cnt;
        int gi = ELIG[rndint(lim)];
        long extra = (long)(fails / 20) * 3000;
        if (extra > 40000) extra = 40000;
        long steps = 4000 + rndint(8000) + extra;
        int before = best->n;
        if (lift_climb(kb, gi, steps, &LCAND) && LCAND.n > best->n && is_valid(&LCAND))
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
            /* Bridge move: add v-w across a bad pair, removing (v,a) and (w,b). */
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
        fprintf(stderr, "usage: %s d D seed time_limit < groups\n", argv[0]);
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

    read_groups();

    static Graph best;
    complete_bipartite(&best);
    if (best.n < moore_bound()) {
        lift_search(&best, t0 + (t_end - t0) * 0.88);
        grow_search(&best, t_end);
    }
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


def _cyc(n, *cycles):
    """Permutation of range(n) with the given cycles."""
    p = list(range(n))
    for c in cycles:
        for i, x in enumerate(c):
            p[x] = c[(i + 1) % len(c)]
    return tuple(p)


def _fn(n, f):
    """Permutation of range(n) given by a function."""
    return tuple(f(t) for t in range(n))


def _pad(p, n):
    """Extend a permutation by fixed points up to n points."""
    return tuple(list(p) + list(range(len(p), n)))


def _psl_gens():
    """PSL(2,7) on the projective line 0..6 plus infinity (= 7)."""
    T = _cyc(8, tuple(range(7)))
    M2 = _fn(8, lambda t: 7 if t == 7 else (2 * t) % 7)
    I = _fn(8, lambda t: 0 if t == 7 else (7 if t == 0 else (-pow(t, -1, 7)) % 7))
    return [T, M2, I]


def _pgl_gens():
    """PGL(2,7) on the projective line 0..6 plus infinity (= 7)."""
    T = _cyc(8, tuple(range(7)))
    M3 = _fn(8, lambda t: 7 if t == 7 else (3 * t) % 7)
    I = _fn(8, lambda t: 0 if t == 7 else (7 if t == 0 else (-pow(t, -1, 7)) % 7))
    return [T, M3, I]


def _asl23_gens():
    """ASL(2,3) on F_3^2, point (x, y) coded as 3x + y."""
    tr1 = _fn(9, lambda k: 3 * ((k // 3 + 1) % 3) + k % 3)
    tr2 = _fn(9, lambda k: 3 * (k // 3) + (k % 3 + 1) % 3)
    sh = _fn(9, lambda k: 3 * ((k // 3 + k % 3) % 3) + k % 3)
    mt = _fn(9, lambda k: 3 * (k % 3) + (2 * (k // 3)) % 3)
    return [tr1, tr2, sh, mt]


def _specs():
    """(number of points, generators) for a pool of permutation groups of moderate order."""
    A4 = [_cyc(4, (0, 1, 2)), _cyc(4, (0, 1), (2, 3))]
    S4 = [_cyc(4, (0, 1)), _cyc(4, (0, 1, 2, 3))]
    A5 = [_cyc(5, (0, 1, 2)), _cyc(5, (0, 1, 2, 3, 4))]
    S5 = [_cyc(5, (0, 1)), _cyc(5, (0, 1, 2, 3, 4))]
    psl = _psl_gens()

    def pad(gs, n):
        return [_pad(g, n) for g in gs]

    return [
        (4, A4),
        (4, S4),
        (4, [_cyc(4, (0, 1, 2, 3)), _cyc(4, (1, 3))]),
        (5, [_fn(5, lambda t: (t + 1) % 5), _fn(5, lambda t: (2 * t) % 5)]),
        (7, [_fn(7, lambda t: (t + 1) % 7), _fn(7, lambda t: (3 * t) % 7)]),
        (5, A5),
        (5, S5),
        (7, pad(A5, 7) + [_cyc(7, (5, 6))]),
        (7, pad(S5, 7) + [_cyc(7, (5, 6))]),
        (8, pad(A5, 8) + [_cyc(8, (5, 6, 7))]),
        (7, pad(S4, 7) + [_cyc(7, (4, 5, 6))]),
        (8, pad(S4, 8) + [_cyc(8, (4, 5, 6, 7))]),
        (8, pad(S4, 8) + [_cyc(8, (4, 5, 6)), _cyc(8, (4, 5), (6, 7))]),
        (8, [_cyc(8, (0, 1, 2)), _cyc(8, (0, 1), (2, 3)),
             _cyc(8, (4, 5, 6)), _cyc(8, (4, 5), (6, 7))]),
        (8, psl),
        (8, _pgl_gens()),
        (10, [_pad(g, 10) for g in psl] + [_cyc(10, (8, 9))]),
        (11, [_fn(11, lambda t: (t + 1) % 11), _fn(11, lambda t: (2 * t) % 11)]),
        (13, [_fn(13, lambda t: (t + 1) % 13), _fn(13, lambda t: (2 * t) % 13)]),
        (9, _asl23_gens()),
        (9, [_cyc(9, (0, 1, 2)), _cyc(9, (3, 4, 5)), _cyc(9, (6, 7, 8)),
             _cyc(9, (0, 3, 6), (1, 4, 7), (2, 5, 8))]),
        (8, [_cyc(8, (0, 1)), _cyc(8, (2, 3)), _cyc(8, (4, 5)), _cyc(8, (6, 7)),
             _cyc(8, (0, 2, 4), (1, 3, 5)), _cyc(8, (0, 2), (1, 3), (4, 6), (5, 7))]),
        (8, [_cyc(8, (0, 1)), _cyc(8, (2, 3)), _cyc(8, (4, 5)), _cyc(8, (6, 7)),
             _cyc(8, (0, 2, 4, 6), (1, 3, 5, 7))]),
    ]


def _perm_table(gens, npts, cap=340):
    """Multiplication table (order G, G x G int array) of the permutation group generated by gens.

    Identity is index 0. Returns None if the group is trivial or larger than cap.
    """
    ident = tuple(range(npts))
    elems = [ident]
    seen = {ident: 0}
    frontier = [ident]
    while frontier:
        nxt = []
        for x in frontier:
            for g in gens:
                y = tuple(g[i] for i in x)
                if y not in seen:
                    if len(elems) >= cap:
                        return None
                    seen[y] = len(elems)
                    elems.append(y)
                    nxt.append(y)
        frontier = nxt
    G = len(elems)
    if G < 2:
        return None
    E = np.array(elems, dtype=np.int64)
    prod = E[np.arange(G)[:, None, None], E[None, :, :]]   # prod[x, y, i] = x(y(i))
    w = np.array([npts ** i for i in range(npts)], dtype=np.int64)
    cp = prod @ w
    ce = E @ w
    order = np.argsort(ce)
    sc = ce[order]
    pos = np.minimum(np.searchsorted(sc, cp), G - 1)
    if not np.array_equal(sc[pos], cp):
        return None
    return G, order[pos].astype(np.int64)


def _semidirect_specs(seed):
    """A few metacyclic groups Z_m x| Z_k of order in [89, 340], chosen by seed."""
    rng = random.Random(seed * 7919 + 11)
    cands = []
    for m in range(3, 341):
        for k in range(2, 340 // m + 1):
            if m * k < 89:
                continue
            for r in range(2, m):
                if math.gcd(r, m) == 1 and pow(r, k, m) == 1:
                    cands.append((m, k, r))
    rng.shuffle(cands)
    return cands[:3]


def _group_pool(seed):
    """List of (G, table) for the group pool, identity at index 0 of every table."""
    pool = []
    for npts, gens in _specs():
        t = _perm_table(gens, npts)
        if t is not None:
            pool.append(t)
    for m, k, r in _semidirect_specs(seed):
        G, mul, _ = lib.semidirect_group(m, k, r)
        tab = np.array([[mul(x, y) for y in range(G)] for x in range(G)], dtype=np.int64)
        pool.append((G, tab))
    return pool


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
        return lib.projective_plane_incidence(d - 1)
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

    if best[0] >= lib.moore_bound(d, D) or D < 2:
        return best

    try:
        pool = _group_pool(seed)
    except Exception:
        return best

    elapsed = time.monotonic() - t0
    budget = 0.85 * (time_limit - elapsed) - 3.0
    if budget < 1.0:
        return best

    tokens = []
    for G, tab in pool:
        tokens.append(G)
        tokens.extend(tab.ravel().tolist())
    if len(tokens) % 2:
        tokens.append(0)
    pairs = list(zip(tokens[0::2], tokens[1::2]))

    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=(1, pairs), timeout=budget + 5)
        n, edges = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)
    except (RuntimeError, ValueError, OSError):
        pass
    return best
