"""Bi-Cayley and voltage-lift search over broad group families for the weakest target (d=4, D=7).

Change from the parent: the C engine no longer hill-climbs starting from the parent's grown graph.
It samples regular voltage lifts with p = 1..3 fibres per side over many finite groups: products of
PSL(2,p)/PGL(2,p) (p = 5, 7, 11) with cyclic groups, and semidirect products Z_m x| Z_k of every
order in the target window. The diameter test is exact: for a regular fibre action, the distance
structure is determined by BFS from the 2p fibre identities, so each evaluation costs only 2p BFS
runs. Every candidate that passes the objective is re-checked by the full all-pairs bitset test.
The last 20% of the engine window is still spent on grow-by-two from the best graph found.
If anything fails, the best valid graph seen so far (at worst the Haar graph K_{d,d}) is returned.
"""
import time

import itertools

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search core, bi-Cayley / voltage-lift version.
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v", or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * 1. Lift search: sample a finite group G (PSL/PGL(2,p) x Z_k, or Z_m x|_r Z_k) of order N in a
 *    window, a fibre count p in {1,2,3}, and d darts per fibre pair layout. Hill-climb the voltages.
 *    Objective: number of (fibre identity, vertex) pairs at distance > D (exact by regularity).
 * 2. Grow by two: insert one vertex per side and anneal degree-preserving swaps (final 20%).
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
#define MAXP 3
#define MAXG 1400
#define MAXV (2 * MAXP * MAXG)
#define HS 8192
#define NB 5
#define POOLCAP 300000
#define STEPS 4000
#define STALL_RESTART 400

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

/* ---------------------------------------------------------------- group tables
 * The current group is a full multiplication table GT[x*GN+y] = x*y with identity 0,
 * and GINV[x] is the inverse of x. */
static int GN;
static int GT_store[MAXG * MAXG];
static int *GT = GT_store;
static int GINV[MAXG];
static int RP[MAXG];

static void compute_inv(void) {
    int N = GN;
    for (int x = 0; x < N; x++) {
        GINV[x] = 0;
        for (int y = 0; y < N; y++)
            if (GT[x * N + y] == 0) { GINV[x] = y; break; }
    }
}

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

/* Direct product of base group b with Z_k: element x*k + c. */
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
    compute_inv();
}

/* Z_m x|_r Z_k: element a*k + b, (a,b)(c,e) = (a + r^b c mod m, b + e mod k). */
static void set_semidirect(int m, int k, int r) {
    int N = m * k;
    GN = N;
    GT = GT_store;
    RP[0] = 1 % m;
    for (int b = 1; b < k; b++) RP[b] = (int)((long)RP[b - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            long aa = ((long)a + (long)RP[b] * c) % m;
            GT[x * N + y] = (int)(aa * k + (b + e) % k);
        }
    }
    compute_inv();
}

/* Pool of group descriptors, grouped by order N (generated in increasing N). */
typedef struct { int m, k, r; } SDesc;
typedef struct { int b, k; } PDesc;
static SDesc SD[POOLCAP];
static PDesc PD[POOLCAP];
static int nsd, npd;
static int sdst[MAXG + 1], sdcn[MAXG + 1], pdst[MAXG + 1], pdcn[MAXG + 1];

static void build_pool(int Nlo, int Nhi) {
    nsd = npd = 0;
    memset(sdst, 0, sizeof sdst);
    memset(sdcn, 0, sizeof sdcn);
    memset(pdst, 0, sizeof pdst);
    memset(pdcn, 0, sizeof pdcn);
    if (Nlo < 1) Nlo = 1;
    if (Nhi > MAXG) Nhi = MAXG;
    for (int N = Nlo; N <= Nhi; N++) {
        sdst[N] = nsd;
        for (int m = 1; m <= N && nsd < POOLCAP; m++) {
            if (N % m) continue;
            int k = N / m;
            if (m == 1) {
                SD[nsd].m = 1; SD[nsd].k = k; SD[nsd].r = 0; nsd++;
                continue;
            }
            for (int r = 1; r < m && nsd < POOLCAP; r++) {
                if (gcd(r, m) != 1) continue;
                if (powmod(r, k, m) != 1 % m) continue;
                SD[nsd].m = m; SD[nsd].k = k; SD[nsd].r = r; nsd++;
            }
        }
        sdcn[N] = nsd - sdst[N];
        pdst[N] = npd;
        for (int b = 0; b < NB; b++) {
            if (!base_tab[b] || base_ord[b] <= 0) continue;
            if (N % base_ord[b]) continue;
            if (npd < POOLCAP) { PD[npd].b = b; PD[npd].k = N / base_ord[b]; npd++; }
        }
        pdcn[N] = npd - pdst[N];
    }
}

/* Sample a group with order in [lo, hi]; prefer the explicit non-metacyclic families half the time. */
static int pick_group(long lo, long hi) {
    if (hi < lo) return 0;
    for (int tries = 0; tries < 60; tries++) {
        int N = (int)(lo + rndint((int)(hi - lo + 1)));
        int ns = sdcn[N], np = pdcn[N];
        if (ns + np == 0) continue;
        if (np > 0 && (ns == 0 || rnd01() < 0.5)) {
            PDesc *q = &PD[pdst[N] + rndint(np)];
            set_product_group(q->b, q->k);
        } else {
            SDesc *q = &SD[sdst[N] + rndint(ns)];
            set_semidirect(q->m, q->k, q->r);
        }
        return 1;
    }
    return 0;
}

/* ---------------------------------------------------------------- voltage lifts
 * p fibres per side, p*d darts. Dart q joins A-fibre DI[q] to B-fibre DJ[q] with voltage DG[q].
 * Each fibre has exactly d darts, so the lift is d-regular. Vertex A(i,x) = i*N + x and
 * B(j,y) = (p+j)*N + y. Dart (i,j,g) joins A(i,x) to B(j, x*g) for all x. */
static int curN, curP;
static int ND;
static int DI[MAXP * MAXD], DJ[MAXP * MAXD], DG[MAXP * MAXD];
static int BI[MAXP * MAXD], BJ[MAXP * MAXD], BG[MAXP * MAXD];
static int LJ[MAXP][MAXD], LG[MAXP][MAXD];   /* A-fibre i, slot t: B-fibre j, voltage g */
static int LI[MAXP][MAXD], LH[MAXP][MAXD];   /* B-fibre j, slot t: A-fibre i, voltage g^-1 */
static int dist_v[MAXV], queue_v[MAXV];

static void rebuild_lists(void) {
    int ca[MAXP] = {0}, cb[MAXP] = {0};
    for (int q = 0; q < ND; q++) {
        int i = DI[q], j = DJ[q], g = DG[q];
        LJ[i][ca[i]] = j;
        LG[i][ca[i]] = g;
        ca[i]++;
        LI[j][cb[j]] = i;
        LH[j][cb[j]] = GINV[g];
        cb[j]++;
    }
}

/* Orbit-reduced objective: BFS from each fibre identity (2p of them). */
static long eval_bad(void) {
    int p = curP, N = curN, V = 2 * p * N, pn = p * N;
    long bad = 0;
    for (int s = 0; s < 2 * p; s++) {
        int src = s * N;
        for (int v = 0; v < V; v++) dist_v[v] = -1;
        int head = 0, tail = 0;
        dist_v[src] = 0;
        queue_v[tail++] = src;
        while (head < tail) {
            int v = queue_v[head++];
            int dv = dist_v[v];
            if (dv >= D) continue;
            if (v < pn) {
                int i = v / N, x = v - i * N;
                const int *row = GT + x * N;
                for (int t = 0; t < d; t++) {
                    int u = (p + LJ[i][t]) * N + row[LG[i][t]];
                    if (dist_v[u] < 0) { dist_v[u] = dv + 1; queue_v[tail++] = u; }
                }
            } else {
                int w = v - pn;
                int j = w / N, y = w - j * N;
                const int *row = GT + y * N;
                for (int t = 0; t < d; t++) {
                    int u = LI[j][t] * N + row[LH[j][t]];
                    if (dist_v[u] < 0) { dist_v[u] = dv + 1; queue_v[tail++] = u; }
                }
            }
        }
        bad += V - tail;
    }
    return bad;
}

/* A voltage for dart q that does not repeat (i, j, g) of another dart. */
static int fresh_g(int q) {
    for (int tries = 0; tries < 100000; tries++) {
        int g = rndint(curN), clash = 0;
        for (int t = 0; t < ND; t++)
            if (t != q && DI[t] == DI[q] && DJ[t] == DJ[q] && DG[t] == g) { clash = 1; break; }
        if (!clash) return g;
    }
    return DG[q];
}

static void init_darts(void) {
    int p = curP;
    ND = p * d;
    for (int t = 0; t < d; t++) {
        int perm[MAXP];
        for (int i = 0; i < p; i++) perm[i] = i;
        for (int i = p - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int s = perm[i]; perm[i] = perm[j]; perm[j] = s;
        }
        for (int i = 0; i < p; i++) {
            int q = t * p + i;
            DI[q] = i;
            DJ[q] = perm[i];
            DG[q] = 0;
        }
    }
    for (int q = 0; q < ND; q++) DG[q] = fresh_g(q);
}

/* Hill-climb over the voltages of one lift shape on the current group. */
static int try_lift(long steps, double until) {
    init_darts();
    rebuild_lists();
    long bad = eval_bad();
    long bestbad = bad;
    memcpy(BI, DI, sizeof(int) * ND);
    memcpy(BJ, DJ, sizeof(int) * ND);
    memcpy(BG, DG, sizeof(int) * ND);
    int stall = 0;
    for (long s = 0; s < steps && bestbad > 0; s++) {
        if ((s & 63) == 0 && now() > until) break;
        int q = rndint(ND);
        int old = DG[q];
        DG[q] = fresh_g(q);
        rebuild_lists();
        long nb = eval_bad();
        if (nb <= bad || rnd01() < 0.01) {
            bad = nb;
        } else {
            DG[q] = old;
            rebuild_lists();
        }
        if (bad < bestbad) {
            bestbad = bad;
            memcpy(BG, DG, sizeof(int) * ND);
            stall = 0;
        } else {
            stall++;
        }
        if (stall > STALL_RESTART && bestbad > 0) {
            memcpy(DG, BG, sizeof(int) * ND);
            for (int k = 0; k < 2; k++) {
                int r2 = rndint(ND);
                DG[r2] = fresh_g(r2);
            }
            rebuild_lists();
            bad = eval_bad();
            stall = 0;
        }
    }
    memcpy(DG, BG, sizeof(int) * ND);
    rebuild_lists();
    return bestbad == 0;
}

static void build_graph(Graph *g) {
    int p = curP, N = curN;
    g->n = 2 * p * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= p * N; }
    for (int q = 0; q < ND; q++)
        for (int x = 0; x < N; x++) {
            int a = DI[q] * N + x;
            int b = (p + DJ[q]) * N + GT[x * N + DG[q]];
            add_edge(g, a, b);
        }
}

/* Search lifts with 2pN > best, sampling N in a narrow band above the current best. */
static void lift_search(Graph *best, double until) {
    static Graph cand;
    long moore = moore_bound();
    int fails = 0;
    while (now() < until) {
        long vlo = best->n + 2;
        if (vlo > moore || vlo > MAXN) return;
        int p = 1 + rndint(MAXP);
        long lo = (vlo + 2 * p - 1) / (2 * p);
        long hi = moore / (2 * p);
        if (hi > MAXN / (2 * p)) hi = MAXN / (2 * p);
        if (hi > MAXG) hi = MAXG;
        long win = lo + lo / 4 + 5;
        if (hi > win) hi = win;
        if (lo > hi) { if (++fails > 2000) return; continue; }
        if (!pick_group(lo, hi)) { if (++fails > 2000) return; continue; }
        fails = 0;
        curP = p;
        curN = GN;
        if (curN < d) continue;
        if (try_lift(STEPS, until)) {
            build_graph(&cand);
            if (cand.n > best->n && is_valid(&cand)) copy_graph(best, &cand);
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

    if (d >= 2 && D >= 2 && best.n < moore_bound()) {
        if (best.n == 0) complete_bipartite(&best);
        init_bases();
        long moore = moore_bound();
        long Nlo = (best.n + 2) / (2 * MAXP);
        if (Nlo < 1) Nlo = 1;
        long Nhi = moore / 2;
        if (Nhi > MAXG) Nhi = MAXG;
        if (Nhi > MAXN / 2) Nhi = MAXN / 2;
        build_pool((int)Nlo, (int)Nhi);
        lift_search(&best, t0 + (t_end - t0) * 0.8);
        if (best.n > 0 && best.n + 2 <= moore_bound()) grow_search(&best, t_end);
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
    """Algebraic candidates valid for diameter D (may be empty). Used as fallbacks and C start graphs."""
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

    best = lib.haar_graph(d, range(d))  # K_{d,d}: valid for D >= 2
    for cand in known_starts(d, D):
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 31 or best[0] >= lib.moore_bound(d, D):
        return best

    # Most of the case budget goes to the engine; keep margin for compile, startup and output.
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
