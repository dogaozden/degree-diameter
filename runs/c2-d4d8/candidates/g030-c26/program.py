"""Bi-Cayley search over non-metacyclic groups, with metacyclic search as a fallback.

Bold change: besides metacyclic groups Z_m x|_r Z_k, the C engine now builds the matrix groups
PSL(2,q) and PGL(2,q) for prime q, as multiplication tables. A 2-fibre lift (one base vertex per
side, d darts) over such a group is a bi-Cayley graph on 2|G| vertices. Voltages are annealed
against the same exact orbit test: left multiplication is a regular automorphism on each fibre,
so BFS from the two fibre identities decides the diameter exactly.

Schedule inside one C run: the matrix-group phase takes about 60% of the budget, with specs in
ascending order of vertex count. A spec that succeeds returns at once, so its leftover time goes
to the next spec. Then the metacyclic search takes the next 25%, and the final phase adds two
vertices per side with degree-preserving annealing.

Python builds the algebraic start (PG(2,q), W(q), Araujo-Pardo-Lopez, or K_{d,d}), checks it with
lib.is_valid, and accepts the C output only if it is valid and strictly larger. Any failure keeps
the valid start.
"""
import time
import itertools

import lib

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 8192
#define MAXD 32
#define MAXW (MAXN / 64)
#define MAXP 2
#define MAXDART (MAXD * MAXP)
#define MAXGRP 4096

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static long MOORE;
static long target_n = 0;
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

/* Number of unordered pairs at distance > D (bitset ball expansion). */
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

/* Group: metacyclic Z_m x|_r Z_k (element a*k+b, (a,b)(c,e) = (a + r^b c, b + e)),
 * or a full multiplication table when tab != NULL (matrix groups). */
typedef struct {
    int N;
    int m, k, r;
    int rp[MAXN];
    int *tab;
} Grp;

static int gmul(const Grp *G, int x, int y) {
    if (G->tab) return G->tab[(size_t)x * G->N + y];
    int a = x / G->k, b = x % G->k, c = y / G->k, e = y % G->k;
    return (int)((a + (long)G->rp[b] * c) % G->m) * G->k + (b + e) % G->k;
}

static void set_group(Grp *G, int m, int k, int r) {
    G->m = m; G->k = k; G->r = r;
    G->N = m * k;
    G->tab = NULL;
    G->rp[0] = 1 % m;
    for (int b = 1; b < k; b++) G->rp[b] = (int)((long)G->rp[b - 1] * r % m);
}

/* Uniformly random metacyclic group of order N (reservoir sampling over all (m, r)). */
static int pick_group(int N, Grp *G) {
    long count = 0;
    int bm = 0, bk = 0, br = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        if (m == 1) {
            count++;
            if (rndint((int)count) == 0) { bm = 1; bk = k; br = 1; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1) continue;
            count++;
            if (rndint((int)count) == 0) { bm = m; bk = k; br = r; }
        }
    }
    if (count == 0) return 0;
    set_group(G, bm, bk, br);
    return 1;
}

/* ---------------- matrix groups PSL(2,q), PGL(2,q), SL(2,q), q prime ---------------- */
/* gtype: 1 = PSL, 2 = PGL, 3 = SL. Elements are coded as ((a*q+b)*q+c)*q+e. */
static int PQ;
static int *IDX = NULL;    /* code -> element index, or -1 */
static int *ECODE = NULL;  /* element index -> code */

static int mdq(long x) {
    x %= PQ;
    if (x < 0) x += PQ;
    return (int)x;
}

static int inv_q(int a) {
    long r = 1, b = a % PQ, e = PQ - 2;
    while (e > 0) {
        if (e & 1) r = r * b % PQ;
        b = b * b % PQ;
        e >>= 1;
    }
    return (int)r;
}

static int enc4(int a, int b, int c, int e) { return ((a * PQ + b) * PQ + c) * PQ + e; }

static void dec4(int code, int *a, int *b, int *c, int *e) {
    *e = code % PQ; code /= PQ;
    *c = code % PQ; code /= PQ;
    *b = code % PQ; code /= PQ;
    *a = code;
}

/* Canonical code of matrix (a,b,c,e) in the group, or -1 if it is not an element. */
static int canon4(int gtype, int a, int b, int c, int e) {
    int det = mdq((long)a * e - (long)b * c);
    if (gtype == 2) {
        if (det == 0) return -1;
        int f = a ? a : (b ? b : (c ? c : e));
        int s = inv_q(f);
        return enc4(mdq((long)a * s), mdq((long)b * s), mdq((long)c * s), mdq((long)e * s));
    }
    if (det != 1) return -1;
    if (gtype == 3) return enc4(a, b, c, e);
    int c1 = enc4(a, b, c, e);
    int c2 = enc4(mdq(-(long)a), mdq(-(long)b), mdq(-(long)c), mdq(-(long)e));
    return c1 < c2 ? c1 : c2;
}

static int expected_order(int gtype, int q) {
    long o = (long)q * ((long)q * q - 1);
    return (int)(gtype == 1 ? o / 2 : o);
}

static void free_matrix_group(Grp *G) {
    free(G->tab);
    G->tab = NULL;
    free(IDX);
    IDX = NULL;
    free(ECODE);
    ECODE = NULL;
}

/* Fills G with the full multiplication table; identity is element 0. */
static int build_matrix_group(int gtype, int q, Grp *G) {
    PQ = q;
    long Q4 = (long)q * q * q * q;
    int want = expected_order(gtype, q);
    if (want < 1 || want > MAXGRP) return 0;
    IDX = malloc(sizeof(int) * (size_t)Q4);
    ECODE = malloc(sizeof(int) * (size_t)want);
    if (!IDX || !ECODE) return 0;
    for (long i = 0; i < Q4; i++) IDX[i] = -1;
    int idcode = canon4(gtype, 1, 0, 0, 1);
    int N = 0;
    ECODE[N] = idcode;
    IDX[idcode] = N;
    N++;
    for (long code = 0; code < Q4; code++) {
        if (code == idcode) continue;
        int a, b, c, e;
        dec4((int)code, &a, &b, &c, &e);
        if (canon4(gtype, a, b, c, e) != code) continue;
        if (N >= want) return 0;
        ECODE[N] = (int)code;
        IDX[code] = N;
        N++;
    }
    if (N != want) return 0;

    G->tab = malloc(sizeof(int) * (size_t)N * (size_t)N);
    if (!G->tab) return 0;
    static int EA[MAXGRP], EB[MAXGRP], EC[MAXGRP], EE[MAXGRP];
    for (int x = 0; x < N; x++) dec4(ECODE[x], &EA[x], &EB[x], &EC[x], &EE[x]);
    for (int x = 0; x < N; x++) {
        int a = EA[x], b = EB[x], c = EC[x], e = EE[x];
        for (int y = 0; y < N; y++) {
            int a2 = EA[y], b2 = EB[y], c2 = EC[y], e2 = EE[y];
            int cc = canon4(gtype,
                            mdq((long)a * a2 + (long)b * c2),
                            mdq((long)a * b2 + (long)b * e2),
                            mdq((long)c * a2 + (long)e * c2),
                            mdq((long)c * b2 + (long)e * e2));
            if (cc < 0 || IDX[cc] < 0) return 0;
            G->tab[(size_t)x * N + y] = IDX[cc];
        }
    }
    G->N = N;
    G->m = G->k = G->r = 0;
    return 1;
}

/* Base multigraph on p + p vertices, d-regular: d random permutations, one dart per fibre each. */
static int di[MAXDART], dj[MAXDART], dg[MAXDART];

static void make_darts(int p) {
    int nd = 0;
    for (int s = 0; s < d; s++) {
        int perm[MAXP];
        for (int i = 0; i < p; i++) perm[i] = i;
        for (int i = p - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
        }
        for (int i = 0; i < p; i++) { di[nd] = i; dj[nd] = perm[i]; nd++; }
    }
}

/* True if voltage g on dart t would duplicate another dart's voltage on the same fibre pair. */
static int clashes(int t, int g, int nd) {
    for (int s = 0; s < nd; s++)
        if (s != t && di[s] == di[t] && dj[s] == dj[t] && dg[s] == g) return 1;
    return 0;
}

/* Vertices: A-fibre i element x -> i*N + x; B-fibre j element x -> (p+j)*N + x. */
static void build_lift(Graph *g, int p, int N, const Grp *G, int nd) {
    int S = p * N;
    g->n = 2 * S;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= S; }
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, di[t] * N + x, S + dj[t] * N + gmul(G, x, dg[t]));
}

static int dist_buf[MAXN], queue_buf[MAXN];

/* Left multiplication is an automorphism acting regularly on each fibre, so the diameter is at
 * most D iff BFS from the identity of every fibre (2p sources) reaches everything within D. */
static long orbit_bad(const Graph *g, int p, int N) {
    int nv = g->n;
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

/* Anneal the voltages of the current darts; leaves dg and g consistent with the result. */
static long anneal(Graph *g, int p, int N, const Grp *G, int nd, int maxit, double until) {
    build_lift(g, p, N, G, nd);
    long bad = orbit_bad(g, p, N);
    double T = 1.0;
    for (int it = 0; it < maxit && bad > 0; it++) {
        if ((it & 63) == 0 && now() > until) break;
        int t = rndint(nd);
        int old = dg[t];
        int ng = rndint(N);
        if (ng == old || clashes(t, ng, nd)) continue;
        dg[t] = ng;
        build_lift(g, p, N, G, nd);
        long nb = orbit_bad(g, p, N);
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) bad = nb;
        else dg[t] = old;
        T *= 0.9995;
        if (T < 0.05) T = 1.0;
    }
    build_lift(g, p, N, G, nd);
    return bad;
}

/* Repeated random group / base / annealing tries at order N until the slice ends. */
static int attempt_order(Graph *best, int p, int N, double until) {
    static Graph cand;
    static Grp G;
    if (N < d) return 0;
    int nd = p * d;
    while (now() < until) {
        if (!pick_group(N, &G)) return 0;
        make_darts(p);
        for (int t = 0; t < nd; t++) dg[t] = -1;
        for (int t = 0; t < nd; t++) {
            int g;
            do { g = rndint(N); } while (clashes(t, g, nd));
            dg[t] = g;
        }
        long bad = anneal(&cand, p, N, &G, nd, 6000, until);
        if (bad == 0 && cand.n > best->n && is_valid(&cand)) {
            copy_graph(best, &cand);
            return 1;
        }
    }
    return 0;
}

/* Bi-Cayley lifts (p = 1) over a fixed matrix group: anneal voltages until one is valid.
 * Returns as soon as one improvement is found, since the same group cannot improve again. */
static void matrix_search(Graph *best, Grp *G, double until) {
    static Graph cand;
    int N = G->N;
    if (N < d) return;
    while (now() < until) {
        make_darts(1);
        int nd = d;
        for (int t = 0; t < nd; t++) dg[t] = -1;
        for (int t = 0; t < nd; t++) {
            int g;
            do { g = rndint(N); } while (clashes(t, g, nd));
            dg[t] = g;
        }
        long bad = anneal(&cand, 1, N, G, nd, 6000, until);
        if (bad == 0 && cand.n > best->n && is_valid(&cand)) {
            copy_graph(best, &cand);
            return;
        }
    }
}

static void matrix_phase(Graph *best, int gtype, int q, double until) {
    static Grp G;
    int want = expected_order(gtype, q);
    if (want < d || want > MAXGRP) return;
    if (2L * want <= best->n || 2L * want > MOORE || 2L * want > MAXN) return;
    if (build_matrix_group(gtype, q, &G)) matrix_search(best, &G, until);
    free_matrix_group(&G);
}

/* Search: adaptive step climbing from the current best, plus direct attempts at a goal order
 * ceil(goal / 2p) per fibre. The goal is the record while below it, and best + 2 once the
 * record is reached, so the search keeps pushing past it. Only adaptive attempts move the step. */
static void search(Graph *best, double until) {
    long step = 1;
    while (now() < until) {
        if (best->n + 2 > MOORE) return;
        int p = rndint(3) == 0 ? 2 : 1;
        long N = 0;
        long goal = 0;
        if (target_n > 0) goal = (target_n > best->n) ? target_n : best->n + 2;
        int use_target = (goal > best->n) && (rndint(2) == 0);
        if (use_target) {
            N = (goal + 2L * p - 1) / (2L * p);
            if (!(2L * p * N <= MOORE && 2L * p * N <= MAXN)) use_target = 0;
        }
        if (!use_target) {
            for (;;) {
                long S = best->n / 2 + step;
                N = (S + p - 1) / p;
                if (N < d) N = d;
                if (2L * p * N <= MOORE && 2L * p * N <= MAXN) break;
                if (p == 2) { p = 1; continue; }
                if (step > 1) { step = 1; continue; }
                return;
            }
        }
        double left = until - now();
        double sl = left / 8;
        if (sl < 0.5) sl = 0.5;
        if (sl > 3.0) sl = 3.0;
        if (sl > left) sl = left;
        int ok = attempt_order(best, p, (int)N, now() + sl);
        if (!use_target) {
            if (ok) { if (step < 512) step *= 2; }
            else if (step > 1) step /= 2;
        }
    }
}

/* Final phase: insert one vertex per side and anneal degree-preserving swaps. */
static int grow_once(const Graph *best, Graph *work, double until) {
    int n = best->n;
    if (n + 2 > MOORE || n + 2 > MAXN) return 0;
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
    while (now() < until && best->n + 2 <= MOORE) {
        double left = until - now();
        double slice = left < 4.0 ? left : (left / 4 > 4.0 ? left / 4 : 4.0);
        if (grow_once(best, &work, now() + slice)) copy_graph(best, &work);
    }
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [target_n [K type q ...]] < start_graph\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    target_n = (argc >= 6) ? atol(argv[5]) : 0;

    int nspec = 0;
    int ptype[32], pq[32];
    if (argc >= 7) {
        int K = atoi(argv[6]);
        for (int i = 0; i < K && nspec < 32 && 8 + 2 * i < argc; i++) {
            ptype[nspec] = atoi(argv[7 + 2 * i]);
            pq[nspec] = atoi(argv[8 + 2 * i]);
            nspec++;
        }
    }

    double t0 = now();
    t_end = t0 + limit * 0.92;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best;
    if (d < 1 || D < 1 || d > MAXD) { complete_bipartite(&best); print_graph(&best); return 0; }
    MOORE = moore_bound();
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (!is_valid(&best)) complete_bipartite(&best);

    if (D >= 2 && best.n < MOORE) {
        double base = now();
        double span = t_end - base;
        if (span < 0) span = 0;
        /* Phase 1: matrix-group bi-Cayley lifts, ascending order. */
        for (int i = 0; i < nspec; i++) {
            double left = base + 0.6 * span - now();
            if (left <= 0) break;
            double slice = left / (nspec - i);
            matrix_phase(&best, ptype[i], pq[i], now() + slice);
        }
        /* Phase 2: metacyclic search. */
        if (best.n + 2 <= MOORE) search(&best, base + 0.85 * span);
    }
    if (best.n + 2 <= MOORE) grow_search(&best, t_end);
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''

# Best known orders (targets for the record-jump phase in C).
RECORDS = {(3, 3): 14, (4, 8): 2184}

_PRIMES = (5, 7, 11, 13, 17, 19, 23, 29, 31)


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


def _matrix_specs(d, lo, hi):
    """(type, q) pairs for PSL(2,q) (type 1) and PGL(2,q) (type 2), q prime, whose
    2-fibre lift has vertex count in (lo, hi]. Ascending by vertex count."""
    out = []
    for q in _PRIMES:
        for typ, order in ((1, q * (q * q - 1) // 2), (2, q * (q * q - 1))):
            if order >= d and order <= 4000 and lo < 2 * order <= hi:
                out.append((2 * order, typ, q))
    out.sort()
    return [(t, q) for _, t, q in out[:12]]


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

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if budget <= 0.2:
        return best

    target = RECORDS.get((d, D), 0)
    specs = []
    if D >= 2:
        specs = _matrix_specs(d, best[0], min(lib.moore_bound(d, D), 8192))
    args = [d, D, seed, round(budget, 3), target, len(specs)]
    for t, q in specs:
        args += [t, q]
    try:
        text = lib.run_c(C_SOURCE, args, stdin_graph=best, timeout=budget + 5)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
