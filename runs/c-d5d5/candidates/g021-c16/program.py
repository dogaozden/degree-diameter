"""Non-abelian table-group voltage lifts, plus the semidirect lifts and grow-by-two annealing from the parent.

Python picks a valid start (K_{d,d}, or a known construction for D = 3 or 4) and calls the C engine.
C runs a lift search with two families of voltage groups:
  (a) permutation groups built in C from cycle generators (A5 x Z_k, S5 x Z2, S4 x Z_k, S4 x S3,
      PSL(2,7), PGL(2,7), PSL(2,7) x Z2). Their multiplication tables are closed under composition,
      so the lift is a bi-Cayley type graph and left multiplication is an automorphism.
  (b) the parent's semidirect groups Z_m x| Z_k2.
Each lift has 2*kb*|G| vertices. The diameter is checked by 2kb BFS runs from class representatives.
The best lift is then grown by two and repaired by annealing. Every output is re-checked in C and Python,
and Python falls back to the best construction it already has if anything fails.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search core.
 *
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v": a valid start graph, or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * Phase 1 (lift search): base with kb vertices per side, d darts out of each base vertex.
 *   Dart (i, j, s) joins A_{i,g} to B_{j, g*s} for group elements g. The group is either a
 *   permutation group built by closure of cycle generators (multiplication table GTAB), or a
 *   semidirect product Z_m x| Z_k2. Left multiplication is an automorphism, so the diameter is
 *   <= D iff a BFS of depth D from each of the 2kb class representatives reaches everything.
 *   Voltages and layer swaps are annealed on the number of unreached pairs.
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
#define MAXGR 512
#define MAXPT 16
#define NTAB 12

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

/* ------------------------------------------------------------ permutation groups */

typedef struct { unsigned char p[MAXPT]; } Perm;

static Perm GEL[MAXGR];
static int GNEL = 0;
static int HT[4096];
static int GTAB[MAXGR][MAXGR];   /* GTAB[x][y] = index of GEL[x]*GEL[y] (table mode) */
static int TMODE = 0;            /* 1: multiplication comes from GTAB */
static int CUR_TAB = -1;
static int TAB_ORD[NTAB];

/* Cycle notation per group: up to 6 cycles, each terminated by -1; a row starting with -1 is empty.
 * Ids: 0 A5xZ3(180), 1 S5xZ2(240), 2 A5xZ5(300), 3 PSL(2,7)(168), 4 PGL(2,7)(336),
 *      5 PSL(2,7)xZ2(336), 6 A5xZ4(240), 7 S4xZ4(96), 8 S4xZ5(120), 9 S4xS3(144),
 *      10 A5xZ2(120), 11 A5(60).
 * PSL(2,7) acts on P^1(F7) = {0..6, inf=7}: x->x+1 is (0 1 2 3 4 5 6); x->-1/x is (0 7)(1 6)(2 3)(4 5);
 * x->3x (for PGL) is (1 3 2 6 4 5). */
static const int CYC[NTAB][6][8] = {
    /* 0 */ {{0,1,2,-1}, {0,1,2,3,4,-1}, {5,6,7,-1}, {-1}, {-1}, {-1}},
    /* 1 */ {{0,1,-1}, {0,1,2,3,4,-1}, {5,6,-1}, {-1}, {-1}, {-1}},
    /* 2 */ {{0,1,2,-1}, {0,1,2,3,4,-1}, {5,6,7,8,9,-1}, {-1}, {-1}, {-1}},
    /* 3 */ {{0,1,2,3,4,5,6,-1}, {0,7,-1}, {1,6,-1}, {2,3,-1}, {4,5,-1}, {-1}},
    /* 4 */ {{0,1,2,3,4,5,6,-1}, {0,7,-1}, {1,6,-1}, {2,3,-1}, {4,5,-1}, {1,3,2,6,4,5,-1}},
    /* 5 */ {{0,1,2,3,4,5,6,-1}, {0,7,-1}, {1,6,-1}, {2,3,-1}, {4,5,-1}, {8,9,-1}},
    /* 6 */ {{0,1,2,-1}, {0,1,2,3,4,-1}, {5,6,7,8,-1}, {-1}, {-1}, {-1}},
    /* 7 */ {{0,1,-1}, {0,1,2,3,-1}, {4,5,6,7,-1}, {-1}, {-1}, {-1}},
    /* 8 */ {{0,1,-1}, {0,1,2,3,-1}, {4,5,6,7,8,-1}, {-1}, {-1}, {-1}},
    /* 9 */ {{0,1,-1}, {0,1,2,3,-1}, {4,5,-1}, {4,5,6,-1}, {-1}, {-1}},
    /* 10 */ {{0,1,2,-1}, {0,1,2,3,4,-1}, {5,6,-1}, {-1}, {-1}, {-1}},
    /* 11 */ {{0,1,2,-1}, {0,1,2,3,4,-1}, {-1}, {-1}, {-1}, {-1}}
};

static void id_perm(Perm *p) {
    for (int i = 0; i < MAXPT; i++) p->p[i] = (unsigned char)i;
}

static void cyc_perm(Perm *p, const int *c, int k) {
    id_perm(p);
    for (int i = 0; i < k; i++) p->p[c[i]] = (unsigned char)c[(i + 1) % k];
}

static unsigned perm_hash(const Perm *a) {
    unsigned h = 2166136261u;
    for (int i = 0; i < MAXPT; i++) {
        h ^= a->p[i];
        h *= 16777619u;
    }
    return h & 4095u;
}

static int perm_find(const Perm *a) {
    unsigned h = perm_hash(a);
    while (HT[h]) {
        if (memcmp(GEL[HT[h] - 1].p, a->p, MAXPT) == 0) return HT[h] - 1;
        h = (h + 1) & 4095u;
    }
    return -1;
}

static void perm_put(const Perm *a, int idx) {
    unsigned h = perm_hash(a);
    while (HT[h]) h = (h + 1) & 4095u;
    HT[h] = idx + 1;
}

/* Closure of the generators (right multiplication from the identity). Returns order or -1. */
static int build_group(const Perm *gens, int ng) {
    memset(HT, 0, sizeof(HT));
    Perm idp;
    id_perm(&idp);
    GEL[0] = idp;
    perm_put(&idp, 0);
    GNEL = 1;
    for (int k = 0; k < GNEL; k++) {
        for (int s = 0; s < ng; s++) {
            Perm c;
            for (int x = 0; x < MAXPT; x++) c.p[x] = GEL[k].p[gens[s].p[x]];
            if (perm_find(&c) >= 0) continue;
            if (GNEL >= MAXGR) return -1;
            GEL[GNEL] = c;
            perm_put(&c, GNEL);
            GNEL++;
        }
    }
    return GNEL;
}

/* Fill GTAB for the group currently in GEL/HT. */
static int install_table(void) {
    for (int i = 0; i < GNEL; i++)
        for (int j = 0; j < GNEL; j++) {
            Perm c;
            for (int x = 0; x < MAXPT; x++) c.p[x] = GEL[i].p[GEL[j].p[x]];
            int k = perm_find(&c);
            if (k < 0) return 0;
            GTAB[i][j] = k;
        }
    return 1;
}

static int make_gens(int id, Perm *g) {
    int ng = 0;
    for (int c = 0; c < 6; c++) {
        if (CYC[id][c][0] < 0) continue;
        int tmp[8], k = 0;
        for (int i = 0; i < 8 && CYC[id][c][i] >= 0; i++) tmp[k++] = CYC[id][c][i];
        cyc_perm(&g[ng++], tmp, k);
    }
    return ng;
}

/* Make table group id the active multiplication. Returns its order, or 0 on failure. */
static int use_table(int id) {
    if (TMODE && CUR_TAB == id) return GORD_T_PLACEHOLDER;
    return 0;
}

/* ------------------------------------------------------------ groups (semidirect) */

static int GM, GK2, GORD;
static int RP[MAXN]; /* RP[b] = r^b mod m */

static void set_group(int m, int k2, int r) {
    TMODE = 0;
    GM = m;
    GK2 = k2;
    GORD = m * k2;
    RP[0] = 1 % m;
    for (int b = 1; b < k2; b++) RP[b] = (int)((long)RP[b - 1] * r % m);
}

static int gmul(int x, int y) {
    if (TMODE) return GTAB[x][y];
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

/* One annealing run over voltages and layer swaps. The group must already be installed
 * (set_group or use_table), and G must equal GORD. On success, out holds the full lift. */
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

/* Feasible (table group, kb) pairs whose lift exceeds cur_n and fits under the Moore bound. */
static int pick_table(long cur_n, long moore, int *oid, int *okb) {
    int cid[NTAB * 3], ckb[NTAB * 3], nc = 0;
    for (int id = 0; id < NTAB; id++) {
        if (TAB_ORD[id] <= 0) continue;
        for (int kb = 1; kb <= 3; kb++) {
            long n2 = 2L * kb * TAB_ORD[id];
            if (n2 <= cur_n || n2 > moore || n2 > MAXN) continue;
            cid[nc] = id;
            ckb[nc] = kb;
            nc++;
        }
    }
    if (nc == 0) return 0;
    int k = rndint(nc);
    *oid = cid[k];
    *okb = ckb[k];
    return 1;
}

/* Lift search: table groups (about 60% of attempts when feasible) and semidirect groups. */
static void lift_search(Graph *best, double until) {
    long moore = moore_bound();
    int fails = 0;   /* consecutive attempts that did not improve best */
    while (now() < until) {
        if (best->n + 2 > moore) return;
        long extra = (long)(fails / 20) * 4000;
        if (extra > 60000) extra = 60000;
        int before = best->n;

        int tid = -1, tkb = 0;
        if (rndint(5) < 3 && pick_table(best->n, moore, &tid, &tkb)) {
            int ord = use_table(tid);
            if (ord > 0) {
                long steps = 3000 + rndint(9000) + extra;
                if (lift_climb(tkb, ord, steps, &LCAND) && LCAND.n > best->n && is_valid(&LCAND))
                    copy_graph(best, &LCAND);
                fails = best->n > before ? 0 : fails + 1;
                continue;
            }
        }

        int r = rndint(10);
        int kb = r < 3 ? 1 : r < 7 ? 2 : 3;
        long esc = fails > 40 ? (fails - 40) / 40 + 1 : 0;
        if (esc > 6) esc = 6;
        long G = (best->n + 2 + 2L * kb - 1) / (2L * kb) + rndint(4) + esc;
        if (G < 1) G = 1;
        if (2L * kb * G > moore || 2L * kb * G > MAXN) { fails++; continue; }
        int m, k2, rr;
        if (!sample_group((int)G, &m, &k2, &rr)) { fails++; continue; }
        set_group(m, k2, rr);
        long steps = 3000 + rndint(9000) + extra;
        if (lift_climb(kb, (int)G, steps, &LCAND) && LCAND.n > best->n && is_valid(&LCAND))
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

    for (int id = 0; id < NTAB; id++) {
        Perm g[6];
        int ng = make_gens(id, g);
        int o = build_group(g, ng);
        TAB_ORD[id] = o > 0 ? o : 0;
    }

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
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=best, timeout=budget + 5)
        n, edges = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)
    except (RuntimeError, ValueError, OSError):
        pass
    return best
