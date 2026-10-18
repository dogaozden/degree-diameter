"""Combined program. Python builds the best algebraic start and checks it with lib.is_valid,
then the C engine searches from that start.

Changed in this version (bold change): the C voltage-lift search now draws from a second group
family. Half the trials use a catalog of non-metacyclic groups, built from permutation generators
by closure: PSL(2,p), PGL(2,p), symmetric groups, and direct products with cyclic groups. These
include order 420 = PSL(2,5) x Z_7, which gives a 840-vertex bi-Cayley lift, equal to the record.
The other trials keep the metacyclic Z_m x| Z_k family. The far jump targets (best+16 up to
0.4 * Moore bound) are kept. H(3) (728 vertices, diameter 6, valid for D = 7) stays as the
start and as the fallback. Every candidate is checked with lib.is_valid.
"""
import time

import itertools

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search core.
 * Usage:   prog d D seed time_limit [mode]  < start_graph
 *   stdin:  "n m" then m lines "u v", or "0 0" for none.
 *   stdout: "n m" then m lines "u v": the largest valid graph found.
 * Phase 1: voltage-lift search over two group families: metacyclic Z_m x| Z_k, and a catalog of
 *          non-metacyclic groups built from permutation generators by closure.
 * Phase 2: grow-by-two annealing from the best graph found.
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
#define MAXP 4
#define MAXG 1024
#define MAXL 16
#define HT 8192
#define MAXCAT 64

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static double t_end;

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

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static int badv[MAXN];

/* Full all-pairs check by bitsets: number of unordered pairs at distance > D. */
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

static void read_start(Graph *g) {
    int n, m;
    g->n = 0;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN) return;
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

static void complete_bipartite(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= d; }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

/* ------------------------------------------------------------------ groups
 * The active group is always stored as a multiplication table gmt[x][y] on 0..gN-1,
 * with element 0 the identity. */
static int gN = 0;
static int gmt[MAXG][MAXG];

typedef struct { int L, ng; unsigned char gen[8][MAXL]; } PermGroup;

static uint64_t enc(const unsigned char *p, int L) {
    uint64_t c = 0;
    for (int i = 0; i < L; i++) c |= (uint64_t)p[i] << (4 * i);
    return c;
}

static uint64_t ht_key[HT];
static int ht_val[HT];
static int ht_stamp[HT];
static int ht_cur = 0;

static unsigned ht_hash(uint64_t c) { return (unsigned)((c * 0x9E3779B97F4A7C15ULL) >> 51); }

static int ht_get(uint64_t c) {
    unsigned h = ht_hash(c);
    while (ht_stamp[h] == ht_cur) {
        if (ht_key[h] == c) return ht_val[h];
        h = (h + 1) & (HT - 1);
    }
    return -1;
}

static void ht_put(uint64_t c, int v) {
    unsigned h = ht_hash(c);
    while (ht_stamp[h] == ht_cur) h = (h + 1) & (HT - 1);
    ht_stamp[h] = ht_cur;
    ht_key[h] = c;
    ht_val[h] = v;
}

static unsigned char pel[MAXG][MAXL];

/* Closure of a permutation group from its generators. Returns the order (0 on failure).
 * If fill is set, also writes the multiplication table gmt and sets gN. */
static int perm_closure(const PermGroup *G, int fill) {
    int L = G->L, N = 1;
    unsigned char id[MAXL];
    memset(id, 0, sizeof id);
    for (int i = 0; i < L; i++) id[i] = (unsigned char)i;
    memcpy(pel[0], id, MAXL);
    ht_cur++;
    ht_put(enc(id, L), 0);
    for (int h = 0; h < N; h++) {
        for (int s = 0; s < G->ng; s++) {
            unsigned char c[MAXL];
            memset(c, 0, sizeof c);
            for (int i = 0; i < L; i++) c[i] = pel[h][G->gen[s][i]];
            uint64_t code = enc(c, L);
            if (ht_get(code) < 0) {
                if (N >= MAXG) return 0;
                memcpy(pel[N], c, MAXL);
                ht_put(code, N);
                N++;
            }
        }
    }
    if (fill) {
        for (int x = 0; x < N; x++)
            for (int y = 0; y < N; y++) {
                unsigned char c[MAXL];
                memset(c, 0, sizeof c);
                for (int i = 0; i < L; i++) c[i] = pel[x][pel[y][i]];
                int z = ht_get(enc(c, L));
                if (z < 0) return 0;
                gmt[x][y] = z;
            }
        gN = N;
    }
    return N;
}

static int inv_mod(int a, int p) {
    long r = 1, b = a % p, e = p - 2;
    while (e > 0) {
        if (e & 1) r = r * b % p;
        b = b * b % p;
        e >>= 1;
    }
    return (int)r;
}

static int prim_root(int p) {
    for (int a = 2; a < p; a++) {
        int x = 1, ord = 0;
        do { x = x * a % p; ord++; } while (x != 1);
        if (ord == p - 1) return a;
    }
    return 1;
}

static void pg_clear(PermGroup *G, int L) {
    G->L = L;
    G->ng = 0;
    memset(G->gen, 0, sizeof G->gen);
}

static void pg_add(PermGroup *G, const int *img) {
    if (G->ng >= 8) return;
    for (int i = 0; i < G->L; i++) G->gen[G->ng][i] = (unsigned char)img[i];
    G->ng++;
}

/* PSL(2,p) (proj = 0) or PGL(2,p) (proj = 1) acting on the projective line:
 * points 0..p-1 and p = infinity. Generators: x+1, -1/x, and (proj) a*x. */
static void pgl_build(PermGroup *G, int p, int proj) {
    int img[MAXL];
    pg_clear(G, p + 1);
    for (int x = 0; x < p; x++) img[x] = (x + 1) % p;
    img[p] = p;
    pg_add(G, img);
    for (int x = 0; x < p; x++) img[x] = (x == 0) ? p : (p - inv_mod(x, p)) % p;
    img[p] = 0;
    pg_add(G, img);
    if (proj) {
        int a = prim_root(p);
        for (int x = 0; x < p; x++) img[x] = x * a % p;
        img[p] = p;
        pg_add(G, img);
    }
}

static void sym_build(PermGroup *G, int n) {
    int img[MAXL];
    pg_clear(G, n);
    for (int i = 0; i < n; i++) img[i] = (i + 1) % n;
    pg_add(G, img);
    for (int i = 0; i < n; i++) img[i] = i;
    img[0] = 1;
    img[1] = 0;
    pg_add(G, img);
}

static void cyc_build(PermGroup *G, int k) {
    int img[MAXL];
    pg_clear(G, k);
    for (int i = 0; i < k; i++) img[i] = (i + 1) % k;
    pg_add(G, img);
}

static void pg_product(PermGroup *C, const PermGroup *A, const PermGroup *B) {
    int L = A->L + B->L;
    int img[MAXL];
    pg_clear(C, L);
    for (int s = 0; s < A->ng; s++) {
        for (int i = 0; i < L; i++) img[i] = i;
        for (int i = 0; i < A->L; i++) img[i] = A->gen[s][i];
        pg_add(C, img);
    }
    for (int s = 0; s < B->ng; s++) {
        for (int i = 0; i < L; i++) img[i] = i;
        for (int j = 0; j < B->L; j++) img[A->L + j] = A->L + B->gen[s][j];
        pg_add(C, img);
    }
}

/* Catalog of non-metacyclic groups. t: 0 = PSL(2,p), 1 = PGL(2,p), 2 = Sym(p), 3 = Cyclic(p).
 * t2 < 0 means a single factor, otherwise the group is the direct product of both factors.
 * Every entry has at most 16 points. */
typedef struct { int t1, p1, t2, p2; } CatEntry;
static const CatEntry CAT[] = {
    {0, 5, -1, 0}, {1, 5, -1, 0}, {2, 5, -1, 0}, {2, 4, -1, 0},
    {0, 7, -1, 0}, {1, 7, -1, 0}, {0, 11, -1, 0},
    {0, 5, 3, 2}, {0, 5, 3, 3}, {0, 5, 3, 4}, {0, 5, 3, 5}, {0, 5, 3, 6},
    {0, 5, 3, 7}, {0, 5, 3, 8}, {0, 5, 3, 9}, {0, 5, 3, 10},
    {1, 5, 3, 2}, {1, 5, 3, 3}, {1, 5, 3, 4},
    {2, 5, 3, 2}, {2, 5, 3, 3}, {2, 5, 3, 4}, {2, 4, 3, 2},
    {0, 7, 3, 2}, {0, 7, 3, 3}, {0, 7, 3, 4}, {0, 7, 3, 5}, {0, 7, 3, 6},
    {1, 7, 3, 2}, {1, 7, 3, 3},
};
#define NCAT ((int)(sizeof(CAT) / sizeof(CAT[0])))

static int cat_build_perm(int t, int p, PermGroup *G) {
    switch (t) {
    case 0: pgl_build(G, p, 0); return 1;
    case 1: pgl_build(G, p, 1); return 1;
    case 2: sym_build(G, p); return 1;
    case 3: cyc_build(G, p); return 1;
    }
    return 0;
}

static int cat_make(int idx, PermGroup *G) {
    const CatEntry *e = &CAT[idx];
    PermGroup A, B;
    if (!cat_build_perm(e->t1, e->p1, &A)) return 0;
    if (e->t2 < 0) { *G = A; return 1; }
    if (!cat_build_perm(e->t2, e->p2, &B)) return 0;
    pg_product(G, &A, &B);
    return 1;
}

static int cat_order[MAXCAT];
static int cat_ready = 0;

static void cat_init(void) {
    if (cat_ready) return;
    cat_ready = 1;
    for (int c = 0; c < NCAT && c < MAXCAT; c++) {
        PermGroup G;
        cat_order[c] = cat_make(c, &G) ? perm_closure(&G, 0) : 0;
    }
}

/* Install catalog group c as the active group. Returns 1 on success. */
static int cat_use(int c) {
    PermGroup G;
    return cat_make(c, &G) && perm_closure(&G, 1) > 0;
}

/* Z_m x|_r Z_k: element a*k + b, (a,b)(c,e) = (a + r^b c mod m, b + e mod k). */
static int random_group(int N, int *om, int *ok, int *orr) {
    long count = 0;
    int m0 = 0, k0 = 0, r0 = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        int rmax = m > 1 ? m : 2;
        for (int r = 1; r < rmax; r++) {
            if (m > 1 && gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            count++;
            if (rndint((int)count) == 0) { m0 = m; k0 = k; r0 = r; }
        }
    }
    if (!count) return 0;
    *om = m0;
    *ok = k0;
    *orr = r0;
    return 1;
}

static void sd_table(int m, int k, int r) {
    static int rp[MAXG];
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
    int N = m * k;
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++) {
            int a = x / k, b = x % k, c = y / k, e = y % k;
            gmt[x][y] = (int)((a + (long)rp[b] * c) % m) * k + (b + e) % k;
        }
    gN = N;
}

/* ------------------------------------------------------------ voltage lifts */
typedef struct { int i, j, g; } Dart;

/* Random d-regular bipartite base multigraph on p + p vertices, connected. */
static void make_base(int p, int M[MAXP][MAXP]) {
    for (;;) {
        memset(M, 0, sizeof(int) * MAXP * MAXP);
        for (int t = 0; t < d; t++) {
            int perm[MAXP];
            for (int i = 0; i < p; i++) perm[i] = i;
            for (int i = p - 1; i > 0; i--) { int j = rndint(i + 1); int s = perm[i]; perm[i] = perm[j]; perm[j] = s; }
            for (int i = 0; i < p; i++) M[i][perm[i]]++;
        }
        int seen[2 * MAXP] = {0}, stack[2 * MAXP], top = 0, nseen = 1;
        seen[0] = 1;
        stack[top++] = 0;
        while (top) {
            int v = stack[--top];
            for (int u = 0; u < 2 * p; u++) {
                if (seen[u]) continue;
                int linked = v < p ? (u >= p && M[v][u - p]) : (u < p && M[u][v - p]);
                if (linked) { seen[u] = 1; nseen++; stack[top++] = u; }
            }
        }
        if (nseen == 2 * p) return;
    }
}

/* Vertex layout: A-fibre i, element x -> i*N + x; B-fibre j, element x -> (p+j)*N + x.
 * Dart (i,j,g) joins (i,x) to (j, x*g) for all x, using the active table gmt. */
static void build_lift(Graph *g, int p, int N, const Dart *dt, int nd) {
    g->n = 2 * p * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= p * N; }
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, dt[t].i * N + x, p * N + dt[t].j * N + gmt[x][dt[t].g]);
}

static int fresh_voltage(const Dart *dt, int nd, int skip, int i, int j, int N) {
    for (;;) {
        int g = rndint(N), clash = 0;
        for (int t = 0; t < nd; t++)
            if (t != skip && dt[t].i == i && dt[t].j == j && dt[t].g == g) { clash = 1; break; }
        if (!clash) return g;
    }
}

/* Orbit-reduced diameter objective for a regular-fibre lift. Left multiplication by the group
 * is an automorphism, so BFS from the identity of each fibre suffices. Returns the number of
 * (representative, vertex) pairs unreached within distance D. Zero iff diameter <= D. */
static int dist_buf[MAXN], queue_buf[MAXN];

static long orbit_bad(const Graph *g, int p) {
    int nv = g->n;
    long total = 0;
    for (int b = 0; b < 2 * p; b++) {
        int src = b * gN;   /* identity of fibre b (element 0) */
        for (int v = 0; v < nv; v++) dist_buf[v] = -1;
        int head = 0, tail = 0;
        dist_buf[src] = 0;
        queue_buf[tail++] = src;
        while (head < tail) {
            int v = queue_buf[head++];
            if (dist_buf[v] >= D) continue;
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[v][i];
                if (dist_buf[u] < 0) {
                    dist_buf[u] = dist_buf[v] + 1;
                    queue_buf[tail++] = u;
                }
            }
        }
        total += nv - tail;
    }
    return total;
}

/* Hill-climb the voltages of one random base multigraph over the active group. */
static int lift_fast_try(Graph *g, int p, int N, int steps, double until) {
    int M[MAXP][MAXP];
    Dart dt[MAXD * MAXP];
    int nd = 0;
    make_base(p, M);
    for (int i = 0; i < p; i++)
        for (int j = 0; j < p; j++)
            for (int c = 0; c < M[i][j]; c++) {
                dt[nd].i = i;
                dt[nd].j = j;
                dt[nd].g = c == 0 ? 0 : fresh_voltage(dt, nd, -1, i, j, N);
                nd++;
            }
    build_lift(g, p, N, dt, nd);
    long bad = orbit_bad(g, p);
    for (int s = 0; s < steps && bad > 0; s++) {
        if ((s & 31) == 0 && now() > until) break;
        int t = rndint(nd);
        int old = dt[t].g;
        dt[t].g = fresh_voltage(dt, nd, t, dt[t].i, dt[t].j, N);
        build_lift(g, p, N, dt, nd);
        long nb = orbit_bad(g, p);
        if (nb <= bad || rnd01() < 0.02) bad = nb;
        else dt[t].g = old;
    }
    build_lift(g, p, N, dt, nd);
    return bad == 0;
}

/* Lift search over two families. Half the trials use a catalog group whose lift order is near
 * the target. The other half use a random metacyclic group of order N. About one trial in three
 * targets a far size, between best+16 and 0.4 * Moore bound, with a larger hill-climb budget.
 * Keeps any valid lift larger than the best. */
static void fast_lift_search(Graph *best, double until) {
    static Graph cand;
    long moore = moore_bound();
    cat_init();
    while (now() < until) {
        int r = rndint(20);
        int p = r < 8 ? 1 : r < 14 ? 2 : r < 18 ? 3 : 4;
        long target;
        int steps = 20000;
        if (rndint(3) == 0 && moore * 2 / 5 > best->n + 16) {
            long span = moore * 2 / 5 - best->n;
            target = best->n + 16 + (long)rndint((int)(span - 15));
            steps = 60000;
        } else {
            target = best->n + 2 + 2 * rndint(7);
        }
        if (target > moore) target = best->n + 2;
        if (target > moore) return;

        int N = 0;
        if (rndint(2) == 0) {
            int cands[MAXCAT], nc = 0;
            for (int c = 0; c < NCAT && c < MAXCAT; c++) {
                long v = 2L * p * cat_order[c];
                long diff = v - target;
                if (diff < 0) diff = -diff;
                if (cat_order[c] > 0 && v > best->n && v <= moore && v <= MAXN &&
                    diff <= target / 10 + 8)
                    cands[nc++] = c;
            }
            if (!nc) continue;
            if (!cat_use(cands[rndint(nc)])) continue;
            N = gN;
        } else {
            int Nmin = (int)((target + 2 * p - 1) / (2 * p));
            N = Nmin + rndint(3);
            if (N < d) N = d;
            if (N > MAXG || 2L * p * N > moore || 2 * p * N > MAXN) continue;
            int m, k, rr;
            if (!random_group(N, &m, &k, &rr)) continue;
            sd_table(m, k, rr);
        }
        if (N > MAXG || 2L * p * N > moore || 2 * p * N > MAXN) continue;
        for (int a = 0; a < 3 && now() < until; a++) {
            if (lift_fast_try(&cand, p, N, steps, until) && is_valid(&cand) &&
                cand.n > best->n) {
                copy_graph(best, &cand);
                break;
            }
        }
    }
}

/* ------------------------------------------------------------ growth phase */
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
    while (now() < until && best->n + 2 <= moore_bound()) {
        double left = until - now();
        double slice = left < 4.0 ? left : (left / 4 > 4.0 ? left / 4 : 4.0);
        if (grow_once(best, &work, now() + slice)) copy_graph(best, &work);
    }
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [mode] < start_graph\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit * 0.92;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best;
    if (d < 1 || D < 1 || d > MAXD) { complete_bipartite(&best); print_graph(&best); return 0; }
    read_start(&best);

    if (D >= 2 && best.n > 0 && best.n < moore_bound()) {
        fast_lift_search(&best, t0 + (t_end - t0) * 0.7);
        if (best.n > 0) grow_search(&best, t_end);
    }
    if (best.n == 0) complete_bipartite(&best);
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


def _gq_w(q):
    """Incidence graph of points and lines of W(q): degree q+1, diameter 4."""
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


def _h3_lines(pts, index, s):
    """Lines of H(3) from Tits' description, with the right-hand sign multiplier s (1 or 2 mod 3)."""
    P = len(pts)

    def bil(x, y):
        return (x[0] * y[4] + x[4] * y[0] + x[1] * y[5] + x[5] * y[1]
                + x[2] * y[6] + x[6] * y[2] - 2 * x[3] * y[3]) % 3

    def norm(v):
        c = next(t for t in v if t)
        inv = 1 if c == 1 else 2
        return tuple((t * inv) % 3 for t in v)

    lines = set()
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            y = pts[j]
            if bil(x, y):
                continue

            def pl(a, b):
                return (x[a] * y[b] - x[b] * y[a]) % 3

            conds = [(pl(1, 2), pl(3, 4)), (pl(5, 4), pl(3, 2)), (pl(2, 0), pl(3, 5)),
                     (pl(6, 5), pl(3, 0)), (pl(0, 1), pl(3, 6)), (pl(4, 6), pl(3, 1))]
            if any((a - s * b) % 3 for a, b in conds):
                continue
            L = set()
            for a in range(3):
                for b in range(3):
                    if a == 0 and b == 0:
                        continue
                    v = tuple((a * x[k] + b * y[k]) % 3 for k in range(7))
                    if any(v):
                        L.add(index[norm(v)])
            if len(L) == 4:
                lines.add(tuple(sorted(L)))
    return lines


def _hexagon_h3():
    """Incidence graph of the split Cayley hexagon H(3): 728 vertices, 4-regular, diameter 6.

    Both sign conventions are tried, and the result is accepted only if lib.is_valid confirms
    it. Returns (n, edges) or None.
    """
    pts = []
    for v in itertools.product(range(3), repeat=7):
        if not any(v):
            continue
        if v[next(i for i, c in enumerate(v) if c)] != 1:
            continue
        if (v[0] * v[4] + v[1] * v[5] + v[2] * v[6] - v[3] * v[3]) % 3:
            continue
        pts.append(v)
    P = len(pts)
    if P != 364:
        return None
    index = {v: i for i, v in enumerate(pts)}
    for s in (1, 2):
        lines = _h3_lines(pts, index, s)
        if len(lines) != P:
            continue
        lines = sorted(lines)
        edges = [(p, P + j) for j, L in enumerate(lines) for p in L]
        if lib.is_valid(2 * P, edges, 4, 6):
            return 2 * P, edges
    return None


def _largest_prime_power_le(x):
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def known_starts(d, D):
    """Algebraic candidates valid for diameter D (may be empty)."""
    out = []
    if D >= 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        out.append(lib.projective_plane_incidence(d - 1))
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        out.append(lib.araujo_lopez_graph(d - 2))
    if D >= 4:
        q = _largest_prime_power_le(min(d - 1, 9))
        if q is not None and q >= 2:
            out.append(_gq_w(q))
    return out


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D
        return L, [(i, (i + 1) % L) for i in range(L)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}: always valid for D >= 2
    for cand in known_starts(d, D):
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d == 4 and D >= 6:
        try:
            hexg = _hexagon_h3()
        except Exception:
            hexg = None
        if hexg is not None and hexg[0] > best[0] and lib.is_valid(hexg[0], hexg[1], d, D):
            best = hexg

    if d > 31 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if budget <= 0.2:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, budget, 0],
                         stdin_graph=best, timeout=budget + 5)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
