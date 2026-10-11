"""Combined search: lift searches over semidirect and table-defined groups in C, then grow-by-pairs annealing.

Python picks a valid start (K_{d,d}, or a known construction for D = 3 or 4) and calls the C engine.
C runs a voltage-lift search: a base with k vertices per side and d darts per base vertex, with
voltages in a finite group. Groups come from two sources. The first is the semidirect family
Z_m x| Z_k2. The second is a table-defined family, which is new in this version: SL/PSL/PGL(2,p)
for small p, and affine groups GF(p^e) x| H with H a subgroup of GF(p^e)* (non-metacyclic, so the
semidirect family does not cover them). Left multiplication is an automorphism of every lift, so the
diameter is checked by 2k BFS runs from class representatives. When lift searches stall, the target
group order rises (escalation). The best lift is then grown by repair annealing. Every output is
re-checked in C and Python, and the Python fallback is always a valid graph.
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
 * Phase 1 (lift search): base with kb vertices per side, d darts out of each base vertex
 *   (one per layer, layers are permutations, so the lift is d-regular). Dart (i, j, s) joins
 *   A_{i,g} to B_{j,g*s}. Groups are given by a multiplication table (identity = 0), built from
 *   one of: semidirect Z_m x| Z_k2, PSL/SL/PGL(2,p), or GF(p^e) x| H. Left multiplication is an
 *   automorphism, so the diameter is <= D iff a BFS of depth D from each of the 2kb class
 *   representatives reaches everything. Voltages and layer swaps are annealed on the number of
 *   unreached pairs.
 * Phase 2 (grow by pairs): add g pairs of new vertices, wire them with degree-preserving edge
 *   steals, then anneal degree-preserving edge swaps until the diameter holds.
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
#define MAXNAMED 256
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

/* ------------------------------------------------------------ group tables */

/* GT[x][y] = x*y for the current group of order GORD; identity is element 0. */
static int GORD;
static int GT[MAXG][MAXG];

/* Z_m x|_r Z_k2: element a*k2+b, (a,b)(c,e) = (a + r^b c mod m, b+e mod k2). */
static void build_semi(int m, int k2, int r) {
    static int RPW[MAXG];
    GORD = m * k2;
    RPW[0] = 1 % m;
    for (int b = 1; b < k2; b++) RPW[b] = (int)((long)RPW[b - 1] * r % m);
    for (int x = 0; x < GORD; x++) {
        int a = x / k2, b = x % k2;
        for (int y = 0; y < GORD; y++) {
            int c = y / k2, e = y % k2;
            GT[x][y] = (int)(((long)a + (long)RPW[b] * c) % m) * k2 + (b + e) % k2;
        }
    }
}

/* Finite field GF(p^e), e >= 2, elements as base-p digit integers 0..q-1. */
static int FP, FE, FQ;
static int FMOD[8];                 /* x^e = -sum FMOD[i] x^i */
static int FM[32][32], FA[32][32];
static int FPW[32];                 /* FPW[k] = x^k, x primitive */

static void fdig(int v, int *dg) {
    for (int i = 0; i < FE; i++) { dg[i] = v % FP; v /= FP; }
}

static int fint(const int *dg) {
    int v = 0;
    for (int i = FE - 1; i >= 0; i--) v = v * FP + dg[i];
    return v;
}

static int fmul_slow(int a, int b) {
    int da[8], db[8], pr[16];
    fdig(a, da);
    fdig(b, db);
    for (int k = 0; k < 16; k++) pr[k] = 0;
    for (int i = 0; i < FE; i++)
        for (int j = 0; j < FE; j++) pr[i + j] = (pr[i + j] + da[i] * db[j]) % FP;
    for (int k = 2 * FE - 2; k >= FE; k--) {
        int c = pr[k];
        if (!c) continue;
        pr[k] = 0;
        for (int i = 0; i < FE; i++)
            pr[k - FE + i] = ((pr[k - FE + i] - c * FMOD[i]) % FP + FP) % FP;
    }
    int dd[8];
    for (int i = 0; i < FE; i++) dd[i] = pr[i];
    return fint(dd);
}

static int fadd_slow(int a, int b) {
    int da[8], db[8], dc[8];
    fdig(a, da);
    fdig(b, db);
    for (int i = 0; i < FE; i++) dc[i] = (da[i] + db[i]) % FP;
    return fint(dc);
}

/* Find a primitive polynomial (x has order q-1 in the quotient ring) and fill the tables. */
static int setup_field(int p, int e) {
    FP = p;
    FE = e;
    FQ = 1;
    for (int i = 0; i < e; i++) FQ *= p;
    if (FQ > 32 || e < 2) return 0;
    for (int code = 0; code < FQ; code++) {
        int c = code;
        for (int i = 0; i < FE; i++) { FMOD[i] = c % FP; c /= FP; }
        if (FMOD[0] == 0) continue;
        int x = FP;                 /* the element x (digit 1 set) */
        int cur = x, ord = 1;
        while (cur != 1 && ord <= FQ) { cur = fmul_slow(cur, x); ord++; }
        if (cur == 1 && ord == FQ - 1) {
            for (int a = 0; a < FQ; a++)
                for (int b = 0; b < FQ; b++) {
                    FM[a][b] = fmul_slow(a, b);
                    FA[a][b] = fadd_slow(a, b);
                }
            FPW[0] = 1;
            for (int k = 1; k < FQ - 1; k++) FPW[k] = FM[FPW[k - 1]][x];
            return 1;
        }
    }
    return 0;
}

/* Affine group GF(q) x| H, H = subgroup of order h in GF(q)*. Element (b, j) is coded as
 * b*h + j and acts as t -> g^(j*s) t + b with s = (q-1)/h. Identity is (0, 0) = 0. */
static int build_aff(int p, int e, int h) {
    if (!setup_field(p, e)) return 0;
    int q = FQ, s = (q - 1) / h;
    if (h < 1 || (q - 1) % h) return 0;
    GORD = q * h;
    for (int x = 0; x < GORD; x++) {
        int b1 = x / h, j1 = x % h;
        int a1 = FPW[(j1 * s) % (q - 1)];
        for (int y = 0; y < GORD; y++) {
            int b2 = y / h, j2 = y % h;
            int bb = FA[b1][FM[a1][b2]];
            int jj = (j1 + j2) % h;
            GT[x][y] = bb * h + jj;
        }
    }
    return 1;
}

/* Matrix groups over Z_p: kind 0 = SL(2,p), 1 = PSL(2,p) (SL modulo +-I), 2 = PGL(2,p).
 * Matrices are coded as ((a*p+b)*p+c)*p+d; each class is represented by its minimal code. */
static int MP, MKIND;
static int MIDX[2401];

static int mcode(const int *m) { return ((m[0] * MP + m[1]) * MP + m[2]) * MP + m[3]; }

static void mdecode(int code, int *m) {
    for (int i = 3; i >= 0; i--) { m[i] = code % MP; code /= MP; }
}

static int mcanon(const int *m) {
    int best = mcode(m);
    if (MKIND == 1) {
        int n2[4];
        for (int i = 0; i < 4; i++) n2[i] = (MP - m[i]) % MP;
        int c2 = mcode(n2);
        if (c2 < best) best = c2;
    } else if (MKIND == 2) {
        for (int l = 2; l < MP; l++) {
            int t[4];
            for (int i = 0; i < 4; i++) t[i] = (l * m[i]) % MP;
            int c = mcode(t);
            if (c < best) best = c;
        }
    }
    return best;
}

static int build_mat(int p, int kind) {
    MP = p;
    MKIND = kind;
    int N = p * p * p * p;
    static int elems[MAXG];
    for (int i = 0; i < N; i++) MIDX[i] = -1;
    int ne = 0;
    int id[4] = {1, 0, 0, 1};
    int idc = mcode(id);
    elems[ne++] = idc;
    MIDX[idc] = 0;
    for (int code = 0; code < N; code++) {
        if (code == idc) continue;
        int m[4];
        mdecode(code, m);
        int det = ((m[0] * m[3] - m[1] * m[2]) % p + p) % p;
        if (kind == 2 ? det == 0 : det != 1) continue;
        if (mcanon(m) != code) continue;
        if (ne >= MAXG) return 0;
        MIDX[code] = ne;
        elems[ne++] = code;
    }
    GORD = ne;
    for (int x = 0; x < GORD; x++) {
        int A[4];
        mdecode(elems[x], A);
        for (int y = 0; y < GORD; y++) {
            int B[4], P[4];
            mdecode(elems[y], B);
            P[0] = (A[0] * B[0] + A[1] * B[2]) % p;
            P[1] = (A[0] * B[1] + A[1] * B[3]) % p;
            P[2] = (A[2] * B[0] + A[3] * B[2]) % p;
            P[3] = (A[2] * B[1] + A[3] * B[3]) % p;
            int idx = MIDX[mcanon(P)];
            if (idx < 0) return 0;
            GT[x][y] = idx;
        }
    }
    return 1;
}

/* ------------------------------------------------------------ named groups */

#define GK_SEMI 0
#define GK_MAT 1
#define GK_AFF 2

typedef struct { int type, a, b, c, order; } GDesc;
static GDesc NAMED[MAXNAMED];
static int NNAMED = 0;

static void add_named(int type, int a, int b, int c, int order) {
    if (NNAMED >= MAXNAMED || order < 12 || order > MAXG) return;
    NAMED[NNAMED].type = type;
    NAMED[NNAMED].a = a;
    NAMED[NNAMED].b = b;
    NAMED[NNAMED].c = c;
    NAMED[NNAMED].order = order;
    NNAMED++;
}

/* Table-defined groups of order at most MAXG that are not in the semidirect family. */
static void init_named(void) {
    static const int mp[3] = {3, 5, 7};
    for (int i = 0; i < 3; i++)
        for (int kind = 0; kind < 3; kind++) {
            int p = mp[i];
            int ord = p * (p * p - 1);
            if (kind == 1) ord /= 2;
            add_named(GK_MAT, p, kind, 0, ord);
        }
    /* {q, p, e} with q = p^e, e >= 2 (non-prime fields are outside the semidirect family). */
    static const int fq[7][3] = {{4, 2, 2}, {8, 2, 3}, {9, 3, 2}, {16, 2, 4},
                                 {25, 5, 2}, {27, 3, 3}, {32, 2, 5}};
    for (int i = 0; i < 7; i++) {
        int q = fq[i][0];
        for (int h = 1; h <= q - 1; h++) {
            if ((q - 1) % h) continue;
            if (q * h > MAXG) continue;
            add_named(GK_AFF, fq[i][1], fq[i][2], h, q * h);
        }
    }
}

static int build_named(const GDesc *g) {
    if (g->type == GK_MAT) return build_mat(g->a, g->b);
    if (g->type == GK_AFF) return build_aff(g->a, g->b, g->c);
    return 0;
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
    for (int g = 0; g < GORD; g++) DPERM[t][g] = GT[g][DS[t]];
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
        int src = rep * GORD;   /* identity of the group is element 0 */
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

/* One annealing run over voltages and layer swaps for base size kb, in the group currently
 * held in GT. On success, out holds the full lift. */
static int lift_climb(int kb, long steps, Graph *out) {
    int G = GORD;
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

/* Lift search. Each attempt picks a base size kb, then a group of order G with
 * 2*kb*G in (best, moore]. With some probability the group is a table-defined named group
 * (matrix or affine); otherwise it is semidirect. The target G rises after many failures
 * (escalation), and annealing runs get more steps. */
static void lift_search(Graph *best, double until) {
    long moore = moore_bound();
    int fails = 0;
    while (now() < until) {
        if (best->n + 2 > moore) return;
        int r = rndint(10);
        int kb = r < 3 ? 1 : r < 7 ? 2 : 3;
        long step = 2L * kb;
        long lo = (best->n + 2 + step - 1) / step;
        long hi = moore / step;
        if (hi > MAXG) hi = MAXG;
        if (step * hi > MAXN) hi = MAXN / step;
        if (lo > hi) { fails++; continue; }
        long esc = fails > 40 ? (fails - 40) / 40 + 1 : 0;
        if (esc > 6) esc = 6;
        long extra = (long)(fails / 20) * 4000;
        if (extra > 60000) extra = 60000;
        long steps = 3000 + rndint(9000) + extra;
        int before = best->n;
        int built = 0;
        if (NNAMED > 0 && rndint(100) < 45) {
            int cand[MAXNAMED], nc = 0;
            for (int i = 0; i < NNAMED; i++)
                if (NAMED[i].order >= lo && NAMED[i].order <= hi) cand[nc++] = i;
            if (nc > 0) built = build_named(&NAMED[cand[rndint(nc)]]);
        }
        if (!built) {
            long G = lo + rndint(4) + esc;
            if (G > hi) { fails++; continue; }
            int m, k2, rr;
            if (!sample_group((int)G, &m, &k2, &rr)) { fails++; continue; }
            build_semi(m, k2, rr);
        }
        if (lift_climb(kb, steps, &LCAND) && LCAND.n > best->n && is_valid(&LCAND))
            copy_graph(best, &LCAND);
        fails = best->n > before ? 0 : fails + 1;
    }
}

/* ------------------------------------------------------------ grow by pairs */

/* Adds g pairs of new vertices (x side 0, y side 1, joined to each other), so the order
 * rises by 2g. Each pair steals d-1 old edges: x takes the far end b of an old edge a-b,
 * and y takes a. Old vertices are used at most once per call, so degrees stay exact.
 * Then annealing swaps edges until the diameter bound holds. */
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
    int fails = 0;
    while (now() < until) {
        long lim = moore_bound();
        if (lim > MAXN) lim = MAXN;
        /* Every third failure, try a jump of two pairs (four vertices). */
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
    t_end = t0 + limit * 0.97;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 1 || d > MAXD) { printf("1 0\n"); return 0; }
    if (d == 1 || D < 2) { printf("2 1\n0 1\n"); return 0; }

    init_named();

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

    # Use most of the limit; keep a margin for compilation and process startup.
    budget = 0.95 * time_limit - (time.monotonic() - t0) - 2.0
    if budget < 0.5:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=best, timeout=budget + 2.5)
        n, edges = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)
    except (RuntimeError, ValueError, OSError):
        pass
    return best
