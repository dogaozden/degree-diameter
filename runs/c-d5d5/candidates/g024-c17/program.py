"""Combined search: Haar graphs over permutation groups, then semidirect voltage lifts and grow-by-two.

Python picks a valid start (K_{d,d}, or a known construction for D = 3 or 4) and calls the C engine.
C runs three phases within the time budget:

1. Haar phase (new): for a catalogue of permutation groups (A5, S5, PSL(2,p), PGL(2,p), ASL(2,3),
   S4 and direct products with cyclic groups), build the group by closure and use the bipartite
   Haar graph H(G,S): a_x ~ b_{x s} for s in S, |S| = d. Left multiplication is an automorphism,
   so the diameter is <= D iff BFS of depth D from a_e and from b_e reaches everything. S is
   annealed to minimise the unreached count.
2. Lift phase: semidirect voltage lifts Z_m x| Z_k2 with k = 1..3 base vertices per side,
   annealed as before.
3. Grow phase: add one vertex per side and repair by annealing edge swaps.

Every output is re-checked in C and Python, with the start graph as fallback.
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
 * Phase 0 (Haar search): groups from a fixed catalogue of permutation groups (closure
 *   computed in C). A bipartite Haar graph over G with connection set S (|S| = d) has
 *   vertices a_x, b_x (x in G) and edges a_x -- b_{x s}. Left multiplication is an
 *   automorphism, so diameter <= D iff BFS from a_e and from b_e reaches all vertices.
 *   S is annealed to minimise the number of unreached vertices.
 * Phase 1 (lift search): semidirect voltage lifts over Z_m x| Z_k2 with kb base vertices
 *   per side, annealed on the orbit-representative BFS cost.
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
#define MAXPT 16
#define MAXG 4
#define MAXORD 1024
#define HSZ 8192

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static double t_end, phase_end;

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

typedef struct {
    int np, ng;
    unsigned char g[MAXG][MAXPT];
} Spec;

static void spec_ident(Spec *s) {
    s->np = 0;
    s->ng = 0;
    for (int i = 0; i < MAXG; i++)
        for (int k = 0; k < MAXPT; k++) s->g[i][k] = (unsigned char)k;
}

static void set_perm(Spec *s, int gi, const int *p, int len) {
    for (int k = 0; k < MAXPT; k++) s->g[gi][k] = (unsigned char)k;
    for (int k = 0; k < len; k++) s->g[gi][k] = (unsigned char)p[k];
}

/* Component generators. kind: 0 A5, 1 S5, 2 S4, 3 S3, 4 cyclic Z_param,
 * 5 PSL(2,param), 6 PGL(2,param), 7 ASL(2,3) on 9 points. */
static void comp(int kind, int param, Spec *s) {
    static const int a5a[5] = {1, 2, 0, 3, 4}, a5b[5] = {1, 2, 3, 4, 0};
    static const int s5a[5] = {1, 0, 2, 3, 4};
    static const int s4a[4] = {1, 0, 2, 3}, s4b[4] = {1, 2, 3, 0};
    static const int s3a[3] = {1, 0, 2}, s3b[3] = {1, 2, 0};
    spec_ident(s);
    int p = param;
    switch (kind) {
    case 0:
        s->np = 5; s->ng = 2;
        set_perm(s, 0, a5a, 5); set_perm(s, 1, a5b, 5);
        break;
    case 1:
        s->np = 5; s->ng = 2;
        set_perm(s, 0, s5a, 5); set_perm(s, 1, a5b, 5);
        break;
    case 2:
        s->np = 4; s->ng = 2;
        set_perm(s, 0, s4a, 4); set_perm(s, 1, s4b, 4);
        break;
    case 3:
        s->np = 3; s->ng = 2;
        set_perm(s, 0, s3a, 3); set_perm(s, 1, s3b, 3);
        break;
    case 4: {
        int c[MAXPT];
        for (int i = 0; i < p; i++) c[i] = (i + 1) % p;
        s->np = p; s->ng = 1;
        set_perm(s, 0, c, p);
        break;
    }
    case 5:
    case 6: {
        int g0[MAXPT], g1[MAXPT], g2[MAXPT];
        for (int x = 0; x < p; x++) g0[x] = (x + 1) % p;
        g0[p] = p;
        for (int x = 0; x < p; x++) {
            if (x == 0) g1[x] = p;
            else g1[x] = (p - (int)powmod(x, p - 2, p)) % p;
        }
        g1[p] = 0;
        s->np = p + 1; s->ng = 2;
        set_perm(s, 0, g0, p + 1);
        set_perm(s, 1, g1, p + 1);
        if (kind == 6) {
            int r;
            for (r = 2; r < p; r++) {
                long x = 1;
                int ord = 0;
                do { x = x * r % p; ord++; } while (x != 1);
                if (ord == p - 1) break;
            }
            for (int x = 0; x < p; x++) g2[x] = (r * x) % p;
            g2[p] = p;
            set_perm(s, 2, g2, p + 1);
            s->ng = 3;
        }
        break;
    }
    case 7: {
        int t1[9], t2[9], m1[9], m2[9];
        for (int a = 0; a < 3; a++)
            for (int b = 0; b < 3; b++) {
                int i = 3 * a + b;
                t1[i] = 3 * ((a + 1) % 3) + b;
                t2[i] = 3 * a + (b + 1) % 3;
                m1[i] = 3 * ((a + b) % 3) + b;
                m2[i] = 3 * ((3 - b) % 3) + a;
            }
        s->np = 9; s->ng = 4;
        set_perm(s, 0, t1, 9);
        set_perm(s, 1, t2, 9);
        set_perm(s, 2, m1, 9);
        set_perm(s, 3, m2, 9);
        break;
    }
    default:
        break;
    }
}

/* Direct product on disjoint point sets. */
static void spec_product(const Spec *a, const Spec *b, Spec *o) {
    spec_ident(o);
    o->np = a->np + b->np;
    o->ng = a->ng + b->ng;
    for (int i = 0; i < a->ng; i++)
        for (int k = 0; k < MAXPT; k++) o->g[i][k] = a->g[i][k];
    for (int j = 0; j < b->ng; j++) {
        int gi = a->ng + j;
        for (int k = 0; k < MAXPT; k++) o->g[gi][k] = (unsigned char)k;
        for (int k = 0; k < b->np; k++)
            o->g[gi][a->np + k] = (unsigned char)(a->np + b->g[j][k]);
    }
}

/* Rows: up to three components (kind, param); kind -1 means absent. */
static const int SPEC_ROWS[][6] = {
    {0, 0, -1, 0, -1, 0},   /* A5 60 */
    {1, 0, -1, 0, -1, 0},   /* S5 120 */
    {0, 0, 4, 2, -1, 0},    /* A5 x Z2 120 */
    {0, 0, 4, 3, -1, 0},    /* A5 x Z3 180 */
    {0, 0, 4, 4, -1, 0},    /* A5 x Z4 240 */
    {0, 0, 3, 0, -1, 0},    /* A5 x S3 360 */
    {1, 0, 4, 2, -1, 0},    /* S5 x Z2 240 */
    {1, 0, 4, 3, -1, 0},    /* S5 x Z3 360 */
    {5, 5, 4, 3, -1, 0},    /* PSL(2,5) x Z3 180 */
    {5, 7, -1, 0, -1, 0},   /* PSL(2,7) 168 */
    {6, 5, -1, 0, -1, 0},   /* PGL(2,5) 120 */
    {6, 5, 4, 2, -1, 0},    /* PGL(2,5) x Z2 240 */
    {6, 7, -1, 0, -1, 0},   /* PGL(2,7) 336 */
    {7, 0, -1, 0, -1, 0},   /* ASL(2,3) 216 */
    {5, 7, 4, 2, -1, 0},    /* PSL(2,7) x Z2 336 */
    {0, 0, 4, 2, 4, 2},     /* A5 x Z2 x Z2 240 */
    {5, 5, 3, 0, -1, 0},    /* PSL(2,5) x S3 360 */
    {0, 0, 4, 5, -1, 0},    /* A5 x Z5 300 */
    {2, 0, -1, 0, -1, 0},   /* S4 24 */
    {2, 0, 4, 7, -1, 0},    /* S4 x Z7 168 */
    {2, 0, 4, 8, -1, 0},    /* S4 x Z8 192 */
    {2, 0, 4, 10, -1, 0},   /* S4 x Z10 240 */
    {2, 0, 4, 11, -1, 0},   /* S4 x Z11 264 */
    {2, 0, 4, 6, -1, 0},    /* S4 x Z6 144 */
    {2, 0, 3, 0, -1, 0},    /* S4 x S3 144 */
};
#define NSPEC ((int)(sizeof(SPEC_ROWS) / sizeof(SPEC_ROWS[0])))

static int build_spec(int row, Spec *out) {
    Spec acc, c, tmp;
    int first = 1;
    for (int r = 0; r < 3; r++) {
        int kind = SPEC_ROWS[row][2 * r], param = SPEC_ROWS[row][2 * r + 1];
        if (kind < 0) continue;
        comp(kind, param, &c);
        if (first) { acc = c; first = 0; }
        else { spec_product(&acc, &c, &tmp); acc = tmp; }
    }
    if (first || acc.ng > MAXG || acc.np > MAXPT) return 0;
    *out = acc;
    return 1;
}

/* Group closure: elements, multiplication table, inverses. */
static int HGORD;
static unsigned char HEL[MAXORD][MAXPT];
static short HMT[MAXORD][MAXORD];
static short HINV[MAXORD];
static uint64_t HKEY[HSZ];
static int HVAL[HSZ], HUSE[HSZ], HSTAMP = 0;

static uint64_t enc(const unsigned char *p) {
    uint64_t k = 0;
    for (int i = 0; i < MAXPT; i++) k |= (uint64_t)p[i] << (4 * i);
    return k;
}

static unsigned hslot(uint64_t k) {
    return (unsigned)((k * 0x9E3779B97F4A7C15ULL) >> 51);
}

static int hfind(uint64_t k) {
    unsigned s = hslot(k);
    while (HUSE[s] == HSTAMP) {
        if (HKEY[s] == k) return HVAL[s];
        s = (s + 1) & (HSZ - 1);
    }
    return -1;
}

static void hinsert(uint64_t k, int v) {
    unsigned s = hslot(k);
    while (HUSE[s] == HSTAMP) s = (s + 1) & (HSZ - 1);
    HUSE[s] = HSTAMP;
    HKEY[s] = k;
    HVAL[s] = v;
}

/* Returns the group order (0 on failure). Element 0 is the identity. */
static int build_group(const Spec *s) {
    HSTAMP++;
    int count = 1;
    unsigned char q[MAXPT];
    for (int k = 0; k < MAXPT; k++) HEL[0][k] = (unsigned char)k;
    hinsert(enc(HEL[0]), 0);
    for (int i = 0; i < count; i++) {
        for (int gi = 0; gi < s->ng; gi++) {
            for (int k = 0; k < MAXPT; k++) q[k] = HEL[i][s->g[gi][k]];
            uint64_t key = enc(q);
            if (hfind(key) < 0) {
                if (count >= MAXORD) return 0;
                memcpy(HEL[count], q, MAXPT);
                hinsert(key, count);
                count++;
            }
        }
    }
    HGORD = count;
    for (int x = 0; x < count; x++)
        for (int y = 0; y < count; y++) {
            for (int k = 0; k < MAXPT; k++) q[k] = HEL[x][HEL[y][k]];
            int v = hfind(enc(q));
            if (v < 0) return 0;
            HMT[x][y] = (short)v;
        }
    for (int x = 0; x < count; x++) {
        HINV[x] = 0;
        for (int y = 0; y < count; y++)
            if (HMT[x][y] == 0) { HINV[x] = (short)y; break; }
    }
    return count;
}

/* ------------------------------------------------------------ Haar graphs */

static int HS[MAXD];
static int VSTAMP[2 * MAXORD], VCNT = 0, QQ[2 * MAXORD];

static int in_S(int e, int cnt) {
    for (int i = 0; i < cnt; i++)
        if (HS[i] == e) return 1;
    return 0;
}

/* Vertices a_x = x (0..N-1), b_y = N + y. a_x ~ b_{x s}, so b_y ~ a_{y s^-1}. */
static int unreached_from(int src) {
    int N = HGORD;
    VCNT++;
    int head = 0, tail = 0;
    QQ[tail++] = src;
    VSTAMP[src] = VCNT;
    for (int lev = 0; lev < D && head < tail; lev++) {
        int end = tail;
        while (head < end) {
            int u = QQ[head++];
            if (u < N) {
                for (int k = 0; k < d; k++) {
                    int v = N + HMT[u][HS[k]];
                    if (VSTAMP[v] != VCNT) { VSTAMP[v] = VCNT; QQ[tail++] = v; }
                }
            } else {
                int y = u - N;
                for (int k = 0; k < d; k++) {
                    int v = HMT[y][HINV[HS[k]]];
                    if (VSTAMP[v] != VCNT) { VSTAMP[v] = VCNT; QQ[tail++] = v; }
                }
            }
        }
    }
    return 2 * N - tail;
}

/* Two sources suffice: left translation is an automorphism acting on each side. */
static long haar_cost(void) {
    return (long)unreached_from(0) + (long)unreached_from(HGORD);
}

static int haar_anneal(long steps) {
    int N = HGORD;
    if (N < d) return 0;
    for (int k = 0; k < d; k++) {
        int e;
        do { e = rndint(N); } while (in_S(e, k));
        HS[k] = e;
    }
    long cost = haar_cost();
    for (long s = 0; s < steps && cost > 0; s++) {
        if ((s & 255) == 0 && now() > phase_end) return 0;
        double T = 1.5 * (1.0 - (double)s / (double)steps) + 0.05;
        int k = rndint(d), e = rndint(N);
        if (in_S(e, d)) continue;
        int old = HS[k];
        HS[k] = e;
        long c2 = haar_cost();
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) cost = c2;
        else HS[k] = old;
    }
    return cost == 0;
}

static void haar_build(Graph *g) {
    int N = HGORD;
    g->n = 2 * N;
    for (int v = 0; v < 2 * N; v++) { g->deg[v] = 0; g->side[v] = v >= N; }
    for (int x = 0; x < N; x++)
        for (int k = 0; k < d; k++) add_edge(g, x, N + HMT[x][HS[k]]);
}

static void haar_search(Graph *best, double until) {
    static Graph HGRAPH;
    static int ORDS[NSPEC];
    static int valid_spec[NSPEC];
    static Spec SPECS[NSPEC];
    long moore = moore_bound();
    for (int i = 0; i < NSPEC; i++) {
        valid_spec[i] = build_spec(i, &SPECS[i]) && build_group(&SPECS[i]) > 0;
        ORDS[i] = valid_spec[i] ? HGORD : 0;
    }
    phase_end = until;
    while (now() < until) {
        int elig[NSPEC], ne = 0;
        for (int i = 0; i < NSPEC; i++) {
            long n2 = 2L * ORDS[i];
            if (valid_spec[i] && ORDS[i] >= d && n2 > best->n && n2 <= moore && n2 <= MAXN)
                elig[ne++] = i;
        }
        if (ne == 0) break;
        int pick = elig[rndint(ne)];
        if (build_group(&SPECS[pick]) == 0) { valid_spec[pick] = 0; continue; }
        for (int r = 0; r < 4 && now() < until; r++) {
            if (2L * HGORD <= best->n) break;
            if (haar_anneal(6000 + rndint(6000))) {
                haar_build(&HGRAPH);
                if (HGRAPH.n > best->n && is_valid(&HGRAPH)) copy_graph(best, &HGRAPH);
                break;
            }
        }
    }
}

/* ------------------------------------------------------------ semidirect voltage lifts */

/* Z_m x|_r Z_k2: element a*k2+b, (a,b)(c,e) = (a + r^b c mod m, b+e mod k2). */
static int GM, GK2, GORD;
static int RP[MAXN];

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

static void lift_search(Graph *best, double until) {
    long moore = moore_bound();
    int fails = 0;
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
        double span = t_end - t0;
        haar_search(&best, t0 + span * 0.5);
        lift_search(&best, t0 + span * 0.8);
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
    budget = 0.92 * time_limit - (time.monotonic() - t0) - 1.5
    if budget < 0.5:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=best, timeout=budget + 3)
        n, edges = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)
    except (RuntimeError, ValueError, OSError):
        pass
    return best
