"""Combined program: Z_k voltage covers of the start graph, then non-metacyclic lifts, then grow-by-two.

Changes from the parent:
- New C routine repair_delete: when a lift of size above the current best cannot be made
  fully valid by voltage search, the lift is repaired by deleting the vertex that lies on the
  most bad pairs (random tie-break), until the graph is valid or drops to the current best size.
  Deleting vertices keeps bipartiteness and degree bounds, so only the diameter needs repair.
  This is applied to the lifts of run_attempts, so near-miss lifts become candidates
  for a slightly smaller but still larger-than-best graph.
- Everything else (Z_k covers, PSL/PGL and semidirect lifts, grow-by-two) is unchanged.
"""
import time

import itertools

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search core.
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v", or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * 1. Z_k voltage covers of the current graph (k small), hill-climbed on voltages.
 * 2. Regular voltage lifts over PSL(2,p), PGL(2,p) x Z_k and semidirect Z_m x| Z_k,
 *    base multigraphs on p <= 4 fibres per side, orbit-reduced diameter objective.
 *    Near-miss lifts are repaired by greedy vertex deletion (repair_delete).
 * 3. Grow by two: insert one vertex per side and anneal degree-preserving edge swaps.
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
#define MAXG 1400
#define HS 8192
#define NB 5
#define KICK_AFTER 800
#define MAXE (MAXN * MAXD / 2)
#define REPAIR_MAX_DEL 64

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
    if (b < 0) b += m;
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

/* Full all-pairs check by bitsets: number of unordered pairs at distance > D.
 * Also fills badv[v] = number of vertices at distance > D from v. */
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

/* ---------------------------------------------------------------- Z_k voltage covers
 * Base graph B (sides 0/1). Cover vertex (v, c) = v*k + c. Each base edge (u on side 0,
 * v on side 1) with voltage a joins (u,c) to (v,(c+a) mod k) for every c. The cover is bipartite
 * and simple when B is simple. Z_k acts on the cover by translation, so
 * dist((u,c),(w,h)) = dist((u,0),(w,h-c)); BFS from the n fibre-zero vertices is exact. */
static int cu[MAXE], cv[MAXE], cvolt[MAXE];
static int cdist[MAXN], cqueue[MAXN];

static int cover_edges(const Graph *base) {
    int m = 0;
    for (int u = 0; u < base->n; u++) {
        if (base->side[u] != 0) continue;
        for (int i = 0; i < base->deg[u]; i++) {
            if (m >= MAXE) return m;
            cu[m] = u;
            cv[m] = base->adj[u][i];
            m++;
        }
    }
    return m;
}

static void build_cover(Graph *g, const Graph *base, int k, int m) {
    int n = base->n;
    g->n = n * k;
    for (int v = 0; v < n; v++)
        for (int c = 0; c < k; c++) {
            g->deg[v * k + c] = 0;
            g->side[v * k + c] = base->side[v];
        }
    for (int e = 0; e < m; e++)
        for (int c = 0; c < k; c++)
            add_edge(g, cu[e] * k + c, cv[e] * k + (c + cvolt[e]) % k);
}

static long cover_bad(const Graph *g, int nb, int k) {
    int nv = g->n;
    long total = 0;
    for (int s = 0; s < nb; s++) {
        int src = s * k;
        for (int v = 0; v < nv; v++) cdist[v] = -1;
        int head = 0, tail = 0;
        cdist[src] = 0;
        cqueue[tail++] = src;
        while (head < tail) {
            int v = cqueue[head++];
            if (cdist[v] >= D) continue;
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[v][i];
                if (cdist[u] < 0) {
                    cdist[u] = cdist[v] + 1;
                    cqueue[tail++] = u;
                }
            }
        }
        total += nv - tail;
    }
    return total;
}

/* Hill-climb the Z_k voltages of a Z_k cover of base. On success, out holds the verified cover. */
static int cover_try(const Graph *base, int k, int steps, double until, Graph *out) {
    int m = cover_edges(base);
    if (m == 0 || k < 2) return 0;
    static Graph tmp;
    for (int e = 0; e < m; e++) cvolt[e] = rndint(k);
    build_cover(&tmp, base, k, m);
    long bad = cover_bad(&tmp, base->n, k);
    for (int s = 0; s < steps && bad > 0; s++) {
        if ((s & 15) == 0 && now() > until) break;
        int e = rndint(m);
        int old = cvolt[e];
        cvolt[e] = (old + 1 + rndint(k - 1)) % k;
        build_cover(&tmp, base, k, m);
        long nb = cover_bad(&tmp, base->n, k);
        if (nb <= bad || rnd01() < 0.01) bad = nb;
        else cvolt[e] = old;
    }
    if (bad != 0) return 0;
    build_cover(&tmp, base, k, m);
    if (!is_valid(&tmp)) return 0;
    copy_graph(out, &tmp);
    return 1;
}

static void cover_search(Graph *best, double until) {
    static Graph cand;
    long moore = moore_bound();
    while (now() < until) {
        long kmax = MAXN / best->n;
        if (kmax > 8) kmax = 8;
        if (moore / best->n < kmax) kmax = moore / best->n;
        if (kmax < 2) return;
        int k = 2 + rndint((int)(kmax - 1));
        if (cover_try(best, k, 30000, until, &cand) && cand.n > best->n)
            copy_graph(best, &cand);
    }
}

/* ---------------------------------------------------------------- group tables
 * The current group is held as a full multiplication table GT[x*GN+y] = x*y, identity 0.
 * Every group used here acts regularly on itself by left multiplication. */
static int GN;
static int *GT;
static int GT_store[MAXG * MAXG];

static int *base_tab[NB];
static int base_ord[NB];

typedef struct { unsigned char p[16]; } Perm;
static Perm ELEM[MAXG];
static uint64_t hkey[HS];
static int hval[HS];

static uint64_t pkey(const unsigned char *p, int s) {
    uint64_t k = 0;
    for (int i = 0; i < s; i++) k |= (uint64_t)p[i] << (4 * i);
    return k;
}

static unsigned hslot(uint64_t key) {
    return (unsigned)((key * 0x9E3779B97F4A7C15ULL) >> 51);
}

static int hfind(uint64_t key) {
    unsigned h = hslot(key);
    while (hval[h]) {
        if (hkey[h] == key) return hval[h] - 1;
        h = (h + 1) & (HS - 1);
    }
    return -1;
}

static void hput(uint64_t key, int idx) {
    unsigned h = hslot(key);
    while (hval[h]) h = (h + 1) & (HS - 1);
    hkey[h] = key;
    hval[h] = idx + 1;
}

/* Closure of the generators of PSL(2,p) (pgl = 0) or PGL(2,p) (pgl = 1) on P^1(F_p). */
static int perm_closure(int p, int pgl, int *orderp) {
    int s = p + 1, inf = p, ng = 0, prim = 1;
    Perm gen[3];
    memset(gen, 0, sizeof gen);
    for (int c = 2; c < p; c++) {
        int ok = 1;
        for (int e = 1; e < p - 1 && ok; e++)
            if (powmod(c, e, p) == 1) ok = 0;
        if (ok) { prim = c; break; }
    }
    for (int x = 0; x <= p; x++)
        gen[ng].p[x] = (unsigned char)((x == inf) ? inf : (x + 1) % p);
    ng++;
    for (int x = 0; x <= p; x++) {
        int v;
        if (x == inf) v = 0;
        else if (x == 0) v = inf;
        else v = (int)((p - powmod(x, p - 2, p)) % p);
        gen[ng].p[x] = (unsigned char)v;
    }
    ng++;
    if (pgl) {
        for (int x = 0; x <= p; x++)
            gen[ng].p[x] = (unsigned char)((x == inf) ? inf : (x * prim) % p);
        ng++;
    }

    memset(hval, 0, sizeof hval);
    memset(&ELEM[0], 0, sizeof(Perm));
    for (int x = 0; x < s; x++) ELEM[0].p[x] = (unsigned char)x;
    hput(pkey(ELEM[0].p, s), 0);
    int n = 1;
    for (int qi = 0; qi < n; qi++) {
        for (int k = 0; k < ng; k++) {
            Perm h;
            memset(&h, 0, sizeof h);
            for (int x = 0; x < s; x++) h.p[x] = ELEM[qi].p[gen[k].p[x]];
            uint64_t key = pkey(h.p, s);
            if (hfind(key) < 0) {
                if (n >= MAXG) return 0;
                ELEM[n] = h;
                hput(key, n);
                n++;
            }
        }
    }
    *orderp = n;
    return 1;
}

static int *make_base_table(int p, int pgl, int *ordp) {
    int ord = 0;
    if (!perm_closure(p, pgl, &ord)) return NULL;
    int s = p + 1;
    int *tab = malloc(sizeof(int) * (size_t)ord * (size_t)ord);
    if (!tab) return NULL;
    for (int i = 0; i < ord; i++)
        for (int j = 0; j < ord; j++) {
            Perm h;
            memset(&h, 0, sizeof h);
            for (int x = 0; x < s; x++) h.p[x] = ELEM[i].p[ELEM[j].p[x]];
            int idx = hfind(pkey(h.p, s));
            tab[(size_t)i * ord + j] = idx < 0 ? 0 : idx;
        }
    *ordp = ord;
    return tab;
}

static void init_bases(void) {
    static const int BP[NB] = {5, 5, 7, 7, 11};
    static const int BG[NB] = {0, 1, 0, 1, 0};
    for (int b = 0; b < NB; b++) {
        int ord = 0;
        base_tab[b] = make_base_table(BP[b], BG[b], &ord);
        base_ord[b] = base_tab[b] ? ord : 0;
    }
}

/* Direct product of base group b with Z_k: element x*k + c, (x,c)(y,e) = (xy, c+e). */
static void set_product_group(int b, int k) {
    int o = base_ord[b], N = o * k;
    GN = N;
    GT = GT_store;
    const int *bt = base_tab[b];
    for (int x = 0; x < o; x++)
        for (int c = 0; c < k; c++)
            for (int y = 0; y < o; y++)
                for (int e = 0; e < k; e++)
                    GT[(x * k + c) * N + (y * k + e)] = bt[x * o + y] * k + (c + e) % k;
}

/* Z_m x|_r Z_k: element a*k + b, (a,b)(c,e) = (a + r^b c mod m, b + e mod k). */
typedef struct {
    int m, k, r;
    int rp[MAXN];
} Grp;

static int gmul(const Grp *G, int x, int y) {
    int a = x / G->k, b = x % G->k, c = y / G->k, e = y % G->k;
    return (int)((a + (long)G->rp[b] * c) % G->m) * G->k + (b + e) % G->k;
}

static void set_semidirect_group(const Grp *G) {
    int N = G->m * G->k;
    GN = N;
    GT = GT_store;
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            GT[x * N + y] = gmul(G, x, y);
}

static int random_group(int N, Grp *G) {
    long count = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        int rmax = m > 1 ? m : 2;
        for (int r = 1; r < rmax; r++) {
            if (m > 1 && gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            count++;
            if (rndint((int)(count < 2000000000L ? count : 2000000000L)) == 0) {
                G->m = m; G->k = k; G->r = r;
            }
        }
    }
    if (!count) return 0;
    G->rp[0] = 1 % G->m;
    for (int b = 1; b < G->k; b++) G->rp[b] = (int)((long)G->rp[b - 1] * G->r % G->m);
    return 1;
}

/* ---------------------------------------------------------------- voltage lifts */
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

/* Vertex layout: A-fibre i, element x -> i*N + x; B-fibre j, element x -> (p+j)*N + x. */
static void build_lift(Graph *g, int p, const Dart *dt, int nd) {
    int N = GN;
    g->n = 2 * p * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= p * N; }
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, dt[t].i * N + x, p * N + dt[t].j * N + GT[x * N + dt[t].g]);
}

static int fresh_voltage(const Dart *dt, int nd, int skip, int i, int j, int N) {
    for (;;) {
        int g = rndint(N), clash = 0;
        for (int t = 0; t < nd; t++)
            if (t != skip && dt[t].i == i && dt[t].j == j && dt[t].g == g) { clash = 1; break; }
        if (!clash) return g;
    }
}

/* Orbit-reduced diameter objective for a regular-fibre lift: BFS from the 2p fibre-zero
 * representatives only. Returns the number of (representative, vertex) pairs at distance > D. */
static int dist_buf[MAXN], queue_buf[MAXN];

static long orbit_bad(const Graph *g, int p) {
    int N = GN, nv = g->n;
    long total = 0;
    for (int b = 0; b < 2 * p; b++) {
        int src = b * N;
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

/* Iterated local search over the voltages of one random base multigraph over the current group.
 * On return, g holds the lift built from the best voltages found (valid iff the return is 1). */
static int lift_fast_try(Graph *g, int p, int steps, double until) {
    int M[MAXP][MAXP];
    Dart dt[MAXD * MAXP], bestdt[MAXD * MAXP];
    int nd = 0, N = GN;
    if (N < d) return 0;
    make_base(p, M);
    for (int i = 0; i < p; i++)
        for (int j = 0; j < p; j++)
            for (int c = 0; c < M[i][j]; c++) {
                dt[nd].i = i;
                dt[nd].j = j;
                dt[nd].g = c == 0 ? 0 : fresh_voltage(dt, nd, -1, i, j, N);
                nd++;
            }
    build_lift(g, p, dt, nd);
    long bad = orbit_bad(g, p);
    long bestbad = bad;
    memcpy(bestdt, dt, sizeof(Dart) * nd);
    int stall = 0;
    for (int s = 0; s < steps && bestbad > 0; s++) {
        if ((s & 31) == 0 && now() > until) break;
        int t = rndint(nd);
        int old = dt[t].g;
        dt[t].g = fresh_voltage(dt, nd, t, dt[t].i, dt[t].j, N);
        build_lift(g, p, dt, nd);
        long nb = orbit_bad(g, p);
        if (nb <= bad || rnd01() < 0.02) bad = nb;
        else dt[t].g = old;
        if (bad < bestbad) {
            bestbad = bad;
            memcpy(bestdt, dt, sizeof(Dart) * nd);
            stall = 0;
        } else {
            stall++;
        }
        if (stall > KICK_AFTER && bestbad > 0) {
            memcpy(dt, bestdt, sizeof(Dart) * nd);
            for (int k = 0; k < 2; k++) {
                int u = rndint(nd);
                dt[u].g = fresh_voltage(dt, nd, u, dt[u].i, dt[u].j, N);
            }
            build_lift(g, p, dt, nd);
            bad = orbit_bad(g, p);
            stall = 0;
        }
    }
    memcpy(dt, bestdt, sizeof(Dart) * nd);
    build_lift(g, p, dt, nd);
    return bestbad == 0;
}

/* ---------------------------------------------------------------- repair by deletion (new)
 * Remove vertex x: detach it from its neighbours, then move the last vertex into slot x so
 * labels stay 0..n-1. Degrees only drop, sides and bipartiteness are preserved. */
static void delete_vertex(Graph *g, int x) {
    for (int i = 0; i < g->deg[x]; i++) {
        int u = g->adj[x][i];
        del_half(g, u, x);
    }
    g->deg[x] = 0;
    int last = g->n - 1;
    if (x != last) {
        for (int i = 0; i < g->deg[last]; i++) {
            int u = g->adj[last][i];
            for (int j = 0; j < g->deg[u]; j++)
                if (g->adj[u][j] == last) g->adj[u][j] = x;
        }
        g->deg[x] = g->deg[last];
        memcpy(g->adj[x], g->adj[last], sizeof(int) * g->deg[last]);
        g->side[x] = g->side[last];
    }
    g->deg[last] = 0;
    g->n--;
}

/* Vertex with the largest badv (random tie-break). Requires badv from the last bad_pairs call. */
static int pick_bad_vertex(int n) {
    int bv = -1, bi = -1, cnt = 0;
    for (int v = 0; v < n; v++) {
        if (badv[v] > bv) { bv = badv[v]; bi = v; cnt = 1; }
        else if (badv[v] == bv && bv > 0) {
            cnt++;
            if (rndint(cnt) == 0) bi = v;
        }
    }
    return bi;
}

/* Greedy repair: repeatedly delete the most-bad vertex while the graph has bad pairs and
 * size stays at least floor_n. Returns 1 iff the result is a valid graph of size >= floor_n. */
static int repair_delete(Graph *g, int floor_n, double until) {
    for (int steps = 0;; steps++) {
        long bad = bad_pairs(g);
        if (bad == 0) return is_valid(g);
        if (g->n <= floor_n || steps >= REPAIR_MAX_DEL || now() > until) return 0;
        int x = pick_bad_vertex(g->n);
        if (x < 0) return 0;
        delete_vertex(g, x);
    }
}

static void run_attempts(int p, Graph *best, Graph *cand, double until) {
    for (int a = 0; a < 2 && now() < until; a++) {
        int ok = lift_fast_try(cand, p, 6000, until);
        /* Near miss: the lift is larger than the best but has some bad pairs.
         * Repair it by deleting vertices, keeping it strictly larger than the best. */
        if (!ok && cand->n > best->n + 1)
            ok = repair_delete(cand, best->n + 1, until);
        if (ok && cand->n > best->n && is_valid(cand)) {
            copy_graph(best, cand);
            break;
        }
    }
}

/* Search lifts of size 2pN strictly larger than the current best. Most attempts use the explicit
 * non-metacyclic families (PSL/PGL(2,p) times Z_k); the rest use semidirect groups. */
static void fast_lift_search(Graph *best, double until) {
    static Graph cand;
    static Grp SG;
    long moore = moore_bound();
    static int cb[512], ck[512], cp[512];
    while (now() < until) {
        long target = best->n + 2;
        if (target > moore) return;
        long hi = target + target / 4 + 60;
        if (hi > moore) hi = moore;
        if (hi > MAXN) hi = MAXN;
        int cnt = 0;
        for (int b = 0; b < NB; b++) {
            if (!base_tab[b]) continue;
            int o = base_ord[b];
            for (int k = 1; k * o <= MAXG; k++)
                for (int p = 1; p <= MAXP; p++) {
                    long nv = 2L * p * o * k;
                    if (nv < target || nv > hi) continue;
                    if (cnt < 512) { cb[cnt] = b; ck[cnt] = k; cp[cnt] = p; cnt++; }
                }
        }
        if (cnt > 0 && rndint(10) < 7) {
            int c = rndint(cnt);
            set_product_group(cb[c], ck[c]);
            run_attempts(cp[c], best, &cand, until);
        } else {
            int p = 1 + rndint(MAXP);
            long Nmin = (target + 2 * p - 1) / (2 * p);
            long Nr = Nmin + rndint(3 + (int)(Nmin / 8));
            if (Nr < d) Nr = d;
            if (2L * p * Nr > moore || 2L * p * Nr > MAXN || Nr > MAXG) continue;
            if (!random_group((int)Nr, &SG)) continue;
            set_semidirect_group(&SG);
            run_attempts(p, best, &cand, until);
        }
    }
}

/* ---------------------------------------------------------------- grow by two */
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
        fprintf(stderr, "usage: %s d D seed time_limit < start_graph\n", argv[0]);
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
        init_bases();
        double span = t_end - t0;
        cover_search(&best, t0 + 0.30 * span);
        fast_lift_search(&best, t0 + 0.88 * span);
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


def _gh_h3():
    """Incidence graph of the split Cayley hexagon H(3): 364 + 364 vertices, degree 4, diameter 6.

    Returns None if no sign convention verifies with lib.is_valid.
    """
    q = 3

    def norm(v):
        c = next(x for x in v if x)
        inv = 1 if c == 1 else 2
        return tuple((x * inv) % q for x in v)

    vecs = itertools.product(range(q), repeat=7)
    pts = sorted({norm(v) for v in vecs if any(v) and
                  (v[0] * v[4] + v[1] * v[5] + v[2] * v[6] - v[3] * v[3]) % q == 0})
    P = len(pts)
    index = {p: i for i, p in enumerate(pts)}

    def bil(x, y):
        return (x[0] * y[4] + x[4] * y[0] + x[1] * y[5] + x[5] * y[1] +
                x[2] * y[6] + x[6] * y[2] + x[3] * y[3]) % q

    def pl(x, y, i, j):
        return (x[i] * y[j] - x[j] * y[i]) % q

    conds = [((1, 2), (3, 4)), ((5, 4), (3, 2)), ((2, 0), (3, 5)),
             ((6, 5), (3, 0)), ((0, 1), (3, 6)), ((4, 6), (3, 1))]
    combos = ((1, 0), (0, 1), (1, 1), (1, 2))
    for s in (1, -1):
        lines = set()
        for i in range(P):
            x = pts[i]
            for j in range(i + 1, P):
                y = pts[j]
                if bil(x, y):
                    continue
                if any((pl(x, y, *a) - s * pl(x, y, *b)) % q for a, b in conds):
                    continue
                L = frozenset(index[norm(tuple((a * x[k] + b * y[k]) % q for k in range(7)))]
                              for a, b in combos)
                lines.add(L)
        if len(lines) != P or any(len(L) != 4 for L in lines):
            continue
        ordered = sorted(lines, key=sorted)
        edges = [(p, P + j) for j, L in enumerate(ordered) for p in L]
        n = P + len(ordered)
        if lib.is_valid(n, edges, 4, 6):
            return n, edges
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
    if d == 4 and D >= 6:
        try:
            gh = _gh_h3()
        except Exception:
            gh = None
        if gh is not None:
            out.append(gh)
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

    if d > 31 or best[0] >= lib.moore_bound(d, D):
        return best

    # Use most of the case budget for the engine; keep a margin for startup and output.
    budget = 0.9 * time_limit - (time.monotonic() - t0) - 2.0
    if budget <= 0.2:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, budget],
                         stdin_graph=best, timeout=budget + 6)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
