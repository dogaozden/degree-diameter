"""Permutation-group voltage lifts in C, then grow-by-two annealing.

Python picks a valid start (K_{d,d}, or a known construction for D = 3 or 4) and passes a pool of
group specs to the C engine. The pool mixes semidirect products Z_m x| Z_k and permutation groups
(PSL(2,p), PGL(2,p) for p = 3, 5, 7, and their direct products with cyclic groups). The C engine
builds a bi-coset lift: a base with kb vertices per side, d darts per base vertex, and voltages in
the chosen group G. Left multiplication by G is an automorphism, so the diameter is checked with
2*kb BFS runs from the class representatives. Voltages and layer swaps are annealed on the number
of unreached pairs. The best lift is then grown by two vertices and repaired by annealing.
Every output is re-checked in C and in Python. The fallback is always a valid graph.
"""
import itertools
import math
import random
import time

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search core.
 *
 * Usage:   prog d D seed time_limit spec_string   < start_graph
 * stdin:   "n m" then m lines "u v": a valid start graph, or "0 0" for none.
 * spec_string: group specs separated by semicolons. Each spec is either
 *   "S m k r"            semidirect Z_m x| Z_k with r^k = 1 mod m, or
 *   "P np:g1/g2/..."     permutation group on np points (np <= 16), gens as comma lists.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
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
#define MAXG 512
#define MAXP 16
#define MAXSPEC 512
#define MAXSG 8
#define HS 4096
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

/* ------------------------------------------------------------ group specs */

typedef struct {
    int type;                 /* 0: semidirect Z_m x| Z_k with action r; 1: permutation group */
    int m, k, r;
    int np, ng;
    unsigned char gen[MAXSG][MAXP];
    int order;                /* -1 when the spec is unusable */
} Spec;

static Spec SPEC[MAXSPEC];
static int NSPEC = 0;

static int GORD = 1;
static short MUL[MAXG][MAXG];   /* MUL[x][y] = index of x*y, identity is index 0 */
static int CUR = -1;            /* spec index currently in MUL */

static unsigned char EL[MAXG][MAXP];
static int NEL = 0;
static uint64_t HK[HS];
static int HV[HS];              /* index + 1, 0 means empty */

static uint64_t pkey(const unsigned char *p, int np) {
    uint64_t k = 0;
    for (int i = 0; i < np; i++) k |= (uint64_t)p[i] << (4 * i);
    return k;
}

static int hslot(uint64_t key) {
    uint64_t h = (key * 0x9E3779B97F4A7C15ULL) >> 52;
    while (HV[h] && HK[h] != key) h = (h + 1) & (HS - 1);
    return (int)h;
}

static int insert_el(const unsigned char *p, int np) {
    uint64_t key = pkey(p, np);
    int sl = hslot(key);
    if (HV[sl]) return 0;
    if (NEL >= MAXG) return -1;
    memcpy(EL[NEL], p, (size_t)np);
    HK[sl] = key;
    HV[sl] = NEL + 1;
    NEL++;
    return 1;
}

/* out = apply x, then y. */
static void comp(const unsigned char *x, const unsigned char *y, int np, unsigned char *out) {
    for (int i = 0; i < np; i++) out[i] = y[x[i]];
}

/* Closure of the generators; returns the group order, or -1 if it exceeds MAXG. */
static int closure_perm(const Spec *s) {
    int np = s->np;
    unsigned char id[MAXP], c[MAXP];
    memset(HV, 0, sizeof HV);
    NEL = 0;
    for (int i = 0; i < np; i++) id[i] = (unsigned char)i;
    if (insert_el(id, np) != 1) return -1;
    for (int q = 0; q < NEL; q++)
        for (int g = 0; g < s->ng; g++) {
            comp(EL[q], s->gen[g], np, c);
            if (insert_el(c, np) < 0) return -1;
        }
    return NEL;
}

/* Fill GORD and MUL for spec si. Returns 1 on success. */
static int build_group(int si) {
    if (CUR == si) return 1;
    const Spec *s = &SPEC[si];
    CUR = -1;
    if (s->type == 0) {
        int m = s->m, k = s->k;
        static int RP[MAXG];
        RP[0] = 1 % m;
        for (int b = 1; b < k; b++) RP[b] = (int)((long)RP[b - 1] * s->r % m);
        GORD = m * k;
        if (GORD > MAXG) return 0;
        for (int x = 0; x < GORD; x++) {
            int a1 = x / k, b1 = x % k;
            for (int y = 0; y < GORD; y++) {
                int c = y / k, e = y % k;
                int a = (int)(((long)a1 + (long)RP[b1] * c) % m);
                MUL[x][y] = (short)(a * k + (b1 + e) % k);
            }
        }
    } else {
        int ng = closure_perm(s);
        if (ng <= 0) return 0;
        GORD = ng;
        unsigned char c[MAXP];
        for (int x = 0; x < GORD; x++)
            for (int y = 0; y < GORD; y++) {
                comp(EL[x], EL[y], s->np, c);
                int sl = hslot(pkey(c, s->np));
                if (!HV[sl]) return 0;
                MUL[x][y] = (short)(HV[sl] - 1);
            }
    }
    CUR = si;
    return 1;
}

/* Parse a spec string: specs separated by semicolons. Keeps only usable specs. */
static void parse_specs(const char *str) {
    NSPEC = 0;
    const char *p = str;
    while (*p && NSPEC < MAXSPEC) {
        while (*p == ' ' || *p == '\n' || *p == '\t') p++;
        if (!*p) break;
        Spec *s = &SPEC[NSPEC];
        memset(s, 0, sizeof *s);
        s->order = -1;
        char *end = NULL;
        int ok = 1;
        if (*p == 'S') {
            p++;
            long m = strtol(p, &end, 10); p = end;
            long k = strtol(p, &end, 10); p = end;
            long r = strtol(p, &end, 10); p = end;
            s->type = 0;
            if (m < 1 || k < 1 || m * k > MAXG) ok = 0;
            else if (m > 1) {
                if (r < 1 || r >= m || gcd((int)r, (int)m) != 1 ||
                    powmod(r, k, m) != 1 % m) ok = 0;
            }
            s->m = (int)m; s->k = (int)k; s->r = (int)r;
            if (ok) s->order = (int)(m * k);
        } else if (*p == 'P') {
            p++;
            long np = strtol(p, &end, 10); p = end;
            if (*p == ':') p++;
            if (np < 1 || np > MAXP) ok = 0;
            s->type = 1;
            s->np = (int)(np < 1 ? 1 : np);
            int ng = 0;
            while (ok) {
                if (ng >= MAXSG) { ok = 0; break; }
                int cnt = 0;
                for (;;) {
                    long v = strtol(p, &end, 10);
                    if (end == p) break;
                    p = end;
                    if (cnt >= s->np || v < 0 || v >= s->np) { ok = 0; break; }
                    s->gen[ng][cnt++] = (unsigned char)v;
                    if (*p == ',') { p++; continue; }
                    break;
                }
                if (!ok) break;
                if (cnt != s->np) { ok = 0; break; }
                ng++;
                if (*p == '/') { p++; continue; }
                break;
            }
            s->ng = ng;
            if (ok) {
                int o = closure_perm(s);
                if (o > 0) s->order = o;
            }
        } else {
            break;
        }
        while (*p && *p != ';') p++;
        if (*p == ';') p++;
        if (s->order > 0) NSPEC++;
    }
    CUR = -1;
}

/* ------------------------------------------------------------ voltage lifts */

static int KB, ND;                 /* base vertices per side, number of darts */
static int DI[MAXDART], DJ[MAXDART], DS[MAXDART];
static int DPERM[MAXDART][MAXG];   /* DPERM[t][g] = g * DS[t] */
static int LADJ[MAXN][MAXD];
static int LDEG[MAXN];
static int VIS[MAXN], VST = 0;
static int QU[MAXN];

static void set_dart_perm(int t) {
    for (int g = 0; g < GORD; g++) DPERM[t][g] = MUL[g][DS[t]];
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

/* One annealing run over voltages and layer swaps for the current group (MUL, GORD). */
static int lift_climb(int kb, long steps, Graph *out) {
    KB = kb;
    ND = d * kb;
    int G = GORD;
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
static int ELIG[MAXSPEC];

/* True if some spec and some base size kb could give a lift larger than bn (and within lim). */
static int has_eligible(long bn, long lim) {
    for (int kb = 1; kb <= 3; kb++)
        for (int s = 0; s < NSPEC; s++) {
            long tot = 2L * kb * SPEC[s].order;
            if (tot > bn && tot <= lim) return 1;
        }
    return 0;
}

/* Lift search: random base size, random eligible group from the pool, annealed voltages.
 * Stalls lengthen the annealing runs. */
static void lift_search(Graph *best, double until) {
    long moore = moore_bound();
    long lim = moore < MAXN ? moore : MAXN;
    int fails = 0;
    while (now() < until) {
        if (!has_eligible(best->n, lim)) return;
        int r = rndint(10);
        int kb = r < 3 ? 1 : r < 7 ? 2 : 3;
        int ne = 0;
        for (int s = 0; s < NSPEC; s++) {
            long tot = 2L * kb * SPEC[s].order;
            if (tot > best->n && tot <= lim) ELIG[ne++] = s;
        }
        if (ne == 0) { fails++; continue; }
        int si = ELIG[rndint(ne)];
        if (!build_group(si)) { fails++; continue; }
        long extra = (long)(fails / 20) * 4000;
        if (extra > 60000) extra = 60000;
        long steps = 3000 + rndint(9000) + extra;
        int before = best->n;
        if (lift_climb(kb, steps, &LCAND) && LCAND.n > best->n && is_valid(&LCAND))
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
        fprintf(stderr, "usage: %s d D seed time_limit [specs] < start_graph\n", argv[0]);
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

    if (argc >= 6) parse_specs(argv[5]);

    static Graph best, start;
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    copy_graph(&start, &best);

    if (best.n < moore_bound()) {
        if (NSPEC > 0) lift_search(&best, t0 + (t_end - t0) * 0.85);
        grow_search(&best, t_end);
    }
    if (!is_valid(&best)) copy_graph(&best, &start);
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


def _primroot(p):
    """Smallest primitive root mod prime p (returns 1 for p = 2)."""
    for g in range(2, p):
        x, k = g % p, 1
        while x != 1:
            x = x * g % p
            k += 1
        if k == p - 1:
            return g
    return 1


def _proj_line(p, pgl):
    """Permutation group PSL(2,p) (or PGL(2,p) if pgl) on the projective line 0..p (p = infinity)."""
    inf = p

    def t(x):
        return inf if x == inf else (x + 1) % p

    def s(x):
        if x == inf:
            return 0
        if x == 0:
            return inf
        return (-pow(x, p - 2, p)) % p

    gens = [tuple(t(x) for x in range(p + 1)), tuple(s(x) for x in range(p + 1))]
    if pgl:
        g = _primroot(p)
        gens.append(tuple(inf if x == inf else (g * x) % p for x in range(p + 1)))
    return (p + 1, gens)


def _cyc(k):
    """Cyclic group Z_k acting on k points."""
    return (k, [tuple((i + 1) % k for i in range(k))])


def _product(A, B):
    """Direct product of two permutation groups acting on disjoint point sets."""
    na, ga = A
    nb, gb = B
    gens = [tuple(list(g) + list(range(na, na + nb))) for g in ga]
    gens += [tuple(list(range(na)) + [na + x for x in h]) for h in gb]
    return (na + nb, gens)


def _perm_spec(group):
    np_, gens = group
    return "P " + str(np_) + ":" + "/".join(",".join(str(x) for x in g) for g in gens)


def _group_pool(d, D, seed):
    """Group specs for the C engine: semidirect products and permutation groups, joined by ';'."""
    moore = lib.moore_bound(d, D)
    maxg = max(2, min(512, moore // 2))
    rng = random.Random(seed * 1009 + d * 31 + D)

    specs = []
    seen = set()
    tries = 0
    while len(specs) < 120 and tries < 40000:
        tries += 1
        m = rng.randint(2, maxg)
        k = rng.randint(1, maxg // m)
        if m * k < 40:
            continue
        r = rng.randint(1, m - 1)
        if math.gcd(r, m) != 1 or pow(r, k, m) != 1 % m:
            continue
        key = (m, k, r)
        if key in seen:
            continue
        seen.add(key)
        specs.append(f"S {m} {k} {r}")

    bases = []
    for p in (3, 5, 7):
        bases.append((p * (p * p - 1) // 2, _proj_line(p, False)))
        bases.append((p * (p * p - 1), _proj_line(p, True)))
    cyc = [(k, _cyc(k)) for k in range(2, 17)]

    seen_p = set()
    for o, A in bases:
        if o <= maxg:
            s = _perm_spec(A)
            if s not in seen_p:
                seen_p.add(s)
                specs.append(s)
    for oa, A in bases:
        for ob, B in bases + cyc:
            if oa * ob > maxg or A[0] + B[0] > 16:
                continue
            s = _perm_spec(_product(A, B))
            if s not in seen_p:
                seen_p.add(s)
                specs.append(s)
    rng.shuffle(specs)
    return ";".join(specs)


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

    if best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if budget < 0.5:
        return best
    try:
        specs = _group_pool(d, D, seed)
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), specs],
                         stdin_graph=best, timeout=budget + 5)
        n, edges = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)
    except (RuntimeError, ValueError, OSError):
        pass
    return best
