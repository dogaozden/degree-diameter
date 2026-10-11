"""Combined program: Python builds the best known start graph (Araujo-Pardo and Lopez record,
projective plane, GQ for D >= 4, or a PG-based extension). For D = 3 cases where d-1 is not a
prime power, Python also sends a second, much larger component: the incidence graph of PG(2,q)
for the smallest prime power q >= d-1, which has degree q+1 > d. The C engine thins that
component by a simulated-annealing vertex deletion search (a different construction: start from
a Moore-like graph that is too dense and delete vertices until degrees and diameter fit). The
best deletion result and the valid start are then grown by two vertices at a time, as before.

Every returned graph passes lib.is_valid. A failure in C only costs time, because build() keeps
the valid Python fallback.
"""
import itertools
import random
import time

import lib

GQ_Q_MAX = 7      # largest q for which W(q) is built in Python (D >= 4 only)
PG_RAW_Q_MAX = 19 # largest q for which PG(2,q) is sent to C for deletion
TIME_FRAC = 0.85  # fraction of time_limit given to the C engine

C_SOURCE = r'''
/* Bipartite degree-diameter search core.
 *
 * Usage:   prog d D seed time_limit mode   < graph
 *   mode 0: stdin is a valid start graph ("n m" then m lines "u v"), or "0 0" for none.
 *   mode 1: stdin is a union of components. One component is a valid start graph (degree <= d,
 *           diameter <= D). Another component is a raw graph with degree > d (a PG(2,q)
 *           incidence graph). The raw component is thinned by simulated annealing over vertex
 *           deletions, then the better of the thinned result and the valid start is grown.
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
#define MAXP 4

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static double t_end;

/* ------------------------------------------------------------------ utilities */

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

/* Largest possible order of a bipartite graph with max degree d and diameter D. */
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

/* ------------------------------------------------------------------ graph basics */

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

/* ------------------------------------------------------------------ distance check */

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static int badv[MAXN];
static uint64_t *final_reach = RA;
static int final_W = 0;

/* Number of unordered pairs at distance > D (0 means connected with diameter <= D). */
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
    final_reach = cur;
    final_W = W;
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

/* Full validity: simple, bipartite (by side labels), degree <= d, diameter <= D. */
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

/* ------------------------------------------------------------------ input / output */

/* Reads a graph and 2-colours it (components separately). Does not check degrees or diameter.
 * Sets g->n = 0 on malformed input or non-bipartite input. */
static void read_raw(Graph *g) {
    int n, m;
    g->n = 0;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN) return;
    g->n = n;
    for (int v = 0; v < n; v++) { g->deg[v] = 0; g->side[v] = 255; }
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= n || v >= n ||
            u == v || g->deg[u] >= MAXD || g->deg[v] >= MAXD) { g->n = 0; return; }
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
}

static void read_start(Graph *g) {
    read_raw(g);
    if (g->n > 0 && !is_valid(g)) g->n = 0;
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

/* K_{d,d}: always valid for D >= 2. */
static void complete_bipartite(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= d; }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

/* ------------------------------------------------------------------ components */

static int ncomp;

/* comp[v] = component index of v (0..ncomp-1). */
static void label_components(const Graph *g, int *comp) {
    static int queue[MAXN];
    for (int v = 0; v < g->n; v++) comp[v] = -1;
    int c = 0;
    for (int s = 0; s < g->n; s++) {
        if (comp[s] >= 0) continue;
        int head = 0, tail = 0;
        comp[s] = c;
        queue[tail++] = s;
        while (head < tail) {
            int v = queue[head++];
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[v][i];
                if (comp[u] < 0) { comp[u] = c; queue[tail++] = u; }
            }
        }
        c++;
    }
    ncomp = c;
}

/* Copies component c of U into out (vertices relabelled 0..k-1, sides kept). */
static void extract(const Graph *U, const int *comp, int c, Graph *out) {
    static int map[MAXN];
    int k = 0;
    for (int v = 0; v < U->n; v++) if (comp[v] == c) map[v] = k++;
    out->n = k;
    for (int v = 0; v < U->n; v++) if (comp[v] == c) {
        int nv = map[v];
        out->deg[nv] = 0;
        out->side[nv] = U->side[v];
    }
    for (int v = 0; v < U->n; v++) if (comp[v] == c)
        for (int i = 0; i < U->deg[v]; i++) {
            int u = U->adj[v][i];
            if (v < u) add_edge(out, map[v], map[u]);
        }
}

/* ------------------------------------------------------------------ groups */

/* Z_m x|_r Z_k: element (a, b) is the int a*k + b, (a,b)(c,e) = (a + r^b c mod m, b + e mod k). */
typedef struct {
    int m, k, r;
    int rp[MAXN];
} Grp;

static int gmul(const Grp *G, int x, int y) {
    int a = x / G->k, b = x % G->k, c = y / G->k, e = y % G->k;
    return (int)((a + (long)G->rp[b] * c) % G->m) * G->k + (b + e) % G->k;
}

/* Uniformly random (m, k, r) with m*k = N, gcd(r, m) = 1 and r^k = 1 mod m. */
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

/* ------------------------------------------------------------------ Haar graphs */

/* a_x ~ b_{x*s} for x in G and s in S (|S| = d, distinct). d-regular, bipartite. */
static void build_haar(Graph *g, int N, const Grp *G, const int *S) {
    g->n = 2 * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= N; }
    for (int x = 0; x < N; x++)
        for (int i = 0; i < d; i++)
            add_edge(g, x, N + gmul(G, x, S[i]));
}

/* Anneal the connection set S (size d) to minimise bad_pairs. Returns the final count. */
static long haar_anneal(const Grp *G, int N, int *S, double until) {
    static Graph g;
    for (int i = 0; i < d; i++) {
        for (;;) {
            int x = rndint(N), ok = 1;
            for (int j = 0; j < i; j++) if (S[j] == x) { ok = 0; break; }
            if (ok) { S[i] = x; break; }
        }
    }
    build_haar(&g, N, G, S);
    long bad = bad_pairs(&g);
    double T = 0.6;
    long it = 0;
    while (bad > 0) {
        if ((++it & 255) == 0 && now() > until) break;
        int i = rndint(d);
        int x = rndint(N), clash = 0;
        for (int j = 0; j < d; j++) if (S[j] == x) { clash = 1; break; }
        if (clash) continue;
        int old = S[i];
        S[i] = x;
        build_haar(&g, N, G, S);
        long nb = bad_pairs(&g);
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) bad = nb;
        else S[i] = old;
        T *= 0.9995;
        if (T < 0.1) T = 0.6;
    }
    return bad;
}

static void haar_search(Graph *best, double until) {
    static Graph cand;
    static Grp G;
    int S[MAXD];
    long moore = moore_bound();
    while (now() < until) {
        int N = best->n / 2 + 1;
        if (N < d) N = d;
        if (2L * N > moore || 2 * N > MAXN) return;
        if (rndint(3) == 0 && 2L * (N + 1) <= moore && 2 * (N + 1) <= MAXN) N++;
        if (!random_group(N, &G)) continue;
        double slice = until - now();
        if (slice > 2.0) slice = 2.0;
        long bad = haar_anneal(&G, N, S, now() + slice);
        if (bad == 0) {
            build_haar(&cand, N, &G, S);
            if (cand.n > best->n && is_valid(&cand)) copy_graph(best, &cand);
        }
    }
}

/* ------------------------------------------------------------------ voltage lifts */

typedef struct { int i, j, g; } Dart;

/* Random d-regular bipartite base multigraph with p vertices per side, connected. */
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

static void build_lift(Graph *g, int p, int N, const Grp *G, const Dart *dt, int nd) {
    g->n = 2 * p * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= p * N; }
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, dt[t].i * N + x, p * N + dt[t].j * N + gmul(G, x, dt[t].g));
}

static int fresh_voltage(const Dart *dt, int nd, int skip, int i, int j, int N) {
    for (;;) {
        int g = rndint(N), clash = 0;
        for (int t = 0; t < nd; t++)
            if (t != skip && dt[t].i == i && dt[t].j == j && dt[t].g == g) { clash = 1; break; }
        if (!clash) return g;
    }
}

static int lift_try(Graph *g, int p, int N, const Grp *G, int steps) {
    int M[MAXP][MAXP];
    Dart dt[MAXD * MAXP];
    int nd = 0;
    make_base(p, M);
    for (int i = 0; i < p; i++)
        for (int j = 0; j < p; j++)
            for (int c = 0; c < M[i][j]; c++) {
                dt[nd].i = i; dt[nd].j = j;
                dt[nd].g = c == 0 ? 0 : fresh_voltage(dt, nd, -1, i, j, N);
                nd++;
            }
    build_lift(g, p, N, G, dt, nd);
    long bad = bad_pairs(g);
    for (int s = 0; s < steps && bad > 0; s++) {
        if ((s & 15) == 0 && now() > t_end) return 0;
        int t = rndint(nd);
        int old = dt[t].g;
        dt[t].g = fresh_voltage(dt, nd, t, dt[t].i, dt[t].j, N);
        build_lift(g, p, N, G, dt, nd);
        long nb = bad_pairs(g);
        if (nb <= bad || rnd01() < 0.01) bad = nb;
        else dt[t].g = old;
    }
    if (bad != 0) return 0;
    return 1;
}

static void lift_search(Graph *best, double until) {
    static Graph cand;
    static Grp G;
    long moore = moore_bound();
    int fails = 0;
    while (now() < until) {
        int r = rndint(10);
        int p = r < 4 ? 1 : r < 7 ? 2 : r < 9 ? 3 : 4;
        long target = best->n + 2;
        if (target > moore) return;
        int N = (int)((target + 2 * p - 1) / (2 * p)) + rndint(2);
        if (best->n == 0) N = d + rndint(3);
        if (N < d || 2L * p * N > moore || 2 * p * N > MAXN) {
            if (++fails > 1000) return;
            continue;
        }
        if (!random_group(N, &G)) continue;
        int steps = 200 + 400000 / (2 * p * N);
        if (lift_try(&cand, p, N, &G, steps) && cand.n > best->n && is_valid(&cand))
            copy_graph(best, &cand);
    }
}

/* ------------------------------------------------------------------ grow by two */

/* Propose a degree-preserving swap (v,u),(s,t) -> (v,t),(s,u) with side(t) != side(v) and
 * side(s) == side(v). Random mode picks s uniformly. Targeted mode picks an unreached partner
 * w of v and walks from w to t: one step if w is on v's side, two steps otherwise. */
static int propose(const Graph *g, int v, int *pu, int *ps, int *pt, int targeted) {
    int n = g->n;
    int u, s, t;
    if (g->deg[v] == 0) return 0;
    u = g->adj[v][rndint(g->deg[v])];
    if (!targeted) {
        s = rndint(n);
        if (g->side[s] != g->side[v] || g->deg[s] == 0) return 0;
        t = g->adj[s][rndint(g->deg[s])];
    } else {
        int w = -1;
        for (int tries = 0; tries < 64; tries++) {
            int c = rndint(n);
            if (c != v && !(((final_reach[(size_t)v * final_W + c / 64] >> (c % 64)) & 1ULL))) { w = c; break; }
        }
        if (w < 0) return 0;
        int L = g->side[w] == g->side[v] ? 1 : 2;
        t = w;
        for (int k = 0; k < L; k++) {
            if (g->deg[t] == 0) return 0;
            t = g->adj[t][rndint(g->deg[t])];
        }
        if (g->deg[t] == 0) return 0;
        s = g->adj[t][rndint(g->deg[t])];
    }
    if (s == v || t == u || g->side[t] == g->side[v] || g->side[s] != g->side[v]) return 0;
    if (has_edge(g, v, t) || has_edge(g, s, u)) return 0;
    *pu = u; *ps = s; *pt = t;
    return 1;
}

/* Apply the swap, keep or revert by the annealing rule. Returns the bad-pair count of the
 * kept state; reach balls and badv refer to that state on return. */
static long apply_swap(Graph *work, int v, int u, int s, int t, long bad, double T) {
    del_edge(work, v, u);
    del_edge(work, s, t);
    add_edge(work, v, t);
    add_edge(work, s, u);
    long nb = bad_pairs(work);
    if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) return nb;
    del_edge(work, v, t);
    del_edge(work, s, u);
    add_edge(work, v, u);
    add_edge(work, s, t);
    bad_pairs(work);
    return bad;
}

/* Frontier: a graph with best->n + 2 vertices whose repair may be unfinished. */
static int have_frontier = 0;
static Graph frontier;
static double frontier_T = 1.0;

/* Copy best into dst and insert one new vertex per side (degree d each), by random rewiring. */
static void insert_pair(const Graph *best, Graph *dst) {
    int n = best->n;
    copy_graph(dst, best);
    int x = n, y = n + 1;
    dst->n = n + 2;
    dst->deg[x] = dst->deg[y] = 0;
    dst->side[x] = 0;
    dst->side[y] = 1;
    add_edge(dst, x, y);
    static int used[MAXN];
    static int stamp = 0;
    stamp++;
    used[x] = used[y] = stamp;
    for (int k = 0, tries = 0; k < d - 1 && tries < 100000; tries++) {
        int a = rndint(n);
        if (dst->side[a] != 0 || used[a] == stamp || dst->deg[a] == 0) continue;
        int b = dst->adj[a][rndint(dst->deg[a])];
        if (used[b] == stamp || b >= n) continue;
        del_edge(dst, a, b);
        add_edge(dst, x, b);
        add_edge(dst, y, a);
        used[a] = used[b] = stamp;
        k++;
    }
}

/* Coverage-greedy insertion: each rewire (a,b) -> (x,b),(y,a) maximises newly covered vertices. */
static int covX[MAXN], covY[MAXN];

static void insert_pair_greedy(const Graph *best, Graph *dst) {
    int n = best->n;
    copy_graph(dst, best);
    int x = n, y = n + 1;
    dst->n = n + 2;
    dst->deg[x] = dst->deg[y] = 0;
    dst->side[x] = 0;
    dst->side[y] = 1;
    add_edge(dst, x, y);
    static int used[MAXN];
    static int stamp = 0;
    stamp++;
    for (int i = 0; i < n + 2; i++) { covX[i] = 0; covY[i] = 0; }
    for (int k = 0; k < d - 1; k++) {
        int bA = -1, bB = -1;
        double bS = -1e18;
        for (int a = 0; a < n; a++) {
            if (dst->side[a] != 0 || used[a] == stamp || dst->deg[a] == 0) continue;
            for (int i = 0; i < dst->deg[a]; i++) {
                int b = dst->adj[a][i];
                if (b >= n || used[b] == stamp) continue;
                int gain = (!covX[a]) + (!covY[b]);
                for (int j = 0; j < dst->deg[b]; j++) {
                    int s = dst->adj[b][j];
                    if (s != a && s != x && !covX[s]) gain++;
                }
                for (int j = 0; j < dst->deg[a]; j++) {
                    int t = dst->adj[a][j];
                    if (t != b && t != y && !covY[t]) gain++;
                }
                double sc = gain + 0.9 * rnd01();
                if (sc > bS) { bS = sc; bA = a; bB = b; }
            }
        }
        if (bA < 0) break;
        del_edge(dst, bA, bB);
        add_edge(dst, x, bB);
        add_edge(dst, y, bA);
        used[bA] = used[bB] = stamp;
        covX[bA] = 1;
        covY[bB] = 1;
        for (int j = 0; j < dst->deg[bB]; j++) {
            int s = dst->adj[bB][j];
            if (s != x) covX[s] = 1;
        }
        for (int j = 0; j < dst->deg[bA]; j++) {
            int t = dst->adj[bA][j];
            if (t != y) covY[t] = 1;
        }
    }
}

/* Anneal swaps on work until it has no bad pairs (returns 0) or the deadline passes. */
static long anneal_frontier(Graph *work, double until) {
    long bad = bad_pairs(work);
    long it = 0;
    while (bad > 0) {
        if ((++it & 15) == 0 && now() > until) return bad;
        int v = rndint(work->n);
        for (int tries = 0; tries < 30 && badv[v] == 0; tries++) v = rndint(work->n);
        int u, s, t;
        int targeted = rndint(3) != 0;
        if (!propose(work, v, &u, &s, &t, targeted)) continue;
        bad = apply_swap(work, v, u, s, t, bad, frontier_T);
        frontier_T *= 0.9995;
        if (frontier_T < 0.05) frontier_T = 1.0;
    }
    return 0;
}

static void grow_search(Graph *best, double until) {
    int fails = 0;
    while (now() < until && best->n + 2 <= moore_bound() && best->n + 2 <= MAXN) {
        if (!have_frontier) {
            if (rndint(3) != 0) insert_pair_greedy(best, &frontier);
            else insert_pair(best, &frontier);
            have_frontier = 1;
            frontier_T = 1.0;
            fails = 0;
        }
        double left = until - now();
        double slice = left < 4.0 ? left : (left / 2 > 4.0 ? left / 2 : 4.0);
        long bad = anneal_frontier(&frontier, now() + slice);
        if (bad == 0 && is_valid(&frontier)) {
            copy_graph(best, &frontier);
            have_frontier = 0;
        } else if (++fails >= 3) {
            have_frontier = 0;
        }
    }
}

/* ------------------------------------------------------------------ deletion search */

/* Evaluates the subgraph induced by alive vertices al[] (degrees counted inside it):
 * bad = number of alive pairs at distance > D, over = sum of alive-degree excess over d,
 * cnt = number of alive vertices. */
static void del_eval(const Graph *g, const unsigned char *al, long *bad, long *over, int *cnt) {
    int n = g->n, W = (n + 63) / 64;
    uint64_t am[MAXW];
    memset(am, 0, sizeof am);
    int c = 0;
    for (int v = 0; v < n; v++) if (al[v]) { am[v / 64] |= 1ULL << (v % 64); c++; }
    uint64_t *cur = RA, *nxt = RB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++) if (al[v]) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < n; v++) {
            if (!al[v]) continue;
            uint64_t *dst = nxt + (size_t)v * W;
            const uint64_t *src = cur + (size_t)v * W;
            for (int w = 0; w < W; w++) dst[w] = src[w];
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[v][i];
                if (!al[u]) continue;
                const uint64_t *s = cur + (size_t)u * W;
                for (int w = 0; w < W; w++) dst[w] |= s[w];
            }
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
    }
    long tot = 0, ov = 0;
    for (int v = 0; v < n; v++) {
        if (!al[v]) continue;
        const uint64_t *s = cur + (size_t)v * W;
        int cc = 0;
        for (int w = 0; w < W; w++) cc += __builtin_popcountll(s[w] & am[w]);
        tot += c - cc;
        int dv = 0;
        for (int i = 0; i < g->deg[v]; i++) if (al[g->adj[v][i]]) dv++;
        if (dv > d) ov += dv - d;
    }
    *bad = tot / 2;
    *over = ov;
    *cnt = c;
}

/* Starts from the whole raw graph R (degrees above d), removes vertices greedily until degrees
 * fit, then anneals single vertex flips to maximise the number of alive vertices subject to
 * zero bad pairs and zero degree excess. Writes the best feasible induced subgraph to out
 * (out->n = 0 if none was found). */
static void delete_search(const Graph *R, Graph *out, double until) {
    static unsigned char al[MAXN], bestal[MAXN], isov[MAXN];
    static int map[MAXN];
    int n = R->n;
    long bad = 0, over = 0;
    int cnt = 0;
    out->n = 0;
    if (n <= 0) return;
    for (int v = 0; v < n; v++) al[v] = 1;
    del_eval(R, al, &bad, &over, &cnt);

    /* Greedy phase: remove the alive vertex that touches the most over-degree vertices. */
    while (over > 0) {
        for (int v = 0; v < n; v++) {
            isov[v] = 0;
            if (!al[v]) continue;
            int dv = 0;
            for (int i = 0; i < R->deg[v]; i++) if (al[R->adj[v][i]]) dv++;
            isov[v] = dv > d;
        }
        int bu = -1;
        double bs = -1.0;
        for (int u = 0; u < n; u++) {
            if (!al[u]) continue;
            int s = isov[u];
            for (int i = 0; i < R->deg[u]; i++) {
                int x = R->adj[u][i];
                if (al[x] && isov[x]) s++;
            }
            if (s == 0) continue;
            double sc = s + 0.5 * rnd01();
            if (sc > bs) { bs = sc; bu = u; }
        }
        if (bu < 0) return;
        al[bu] = 0;
        del_eval(R, al, &bad, &over, &cnt);
    }

    /* Annealing phase: energy = bad + 2*over - 0.6*alive. */
    double T = 1.5;
    double E = (double)bad + 2.0 * (double)over - 0.6 * cnt;
    long bestcnt = -1;
    if (bad == 0 && over == 0) { bestcnt = cnt; memcpy(bestal, al, n); }
    long it = 0;
    for (;;) {
        if ((++it & 63) == 0 && now() > until) break;
        int v = rndint(n);
        al[v] ^= 1;
        long nbad, nover;
        int ncnt;
        del_eval(R, al, &nbad, &nover, &ncnt);
        double NE = (double)nbad + 2.0 * (double)nover - 0.6 * ncnt;
        if (NE <= E || rnd01() < exp((E - NE) / T)) {
            E = NE; bad = nbad; over = nover; cnt = ncnt;
            if (bad == 0 && over == 0 && cnt > bestcnt) {
                bestcnt = cnt;
                memcpy(bestal, al, n);
            }
        } else {
            al[v] ^= 1;
        }
        T *= 0.99995;
        if (T < 0.08) T = 1.5;
    }
    if (bestcnt < 0) return;

    int k = 0;
    for (int v = 0; v < n; v++) map[v] = bestal[v] ? k++ : -1;
    out->n = k;
    for (int v = 0; v < n; v++)
        if (bestal[v]) { out->deg[map[v]] = 0; out->side[map[v]] = R->side[v]; }
    for (int v = 0; v < n; v++)
        if (bestal[v])
            for (int i = 0; i < R->deg[v]; i++) {
                int u = R->adj[v][i];
                if (bestal[u] && v < u) add_edge(out, map[v], map[u]);
            }
    if (!is_valid(out)) out->n = 0;
}

/* ------------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [mode] < graph\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int mode = argc > 5 ? atoi(argv[5]) : 0;
    double t0 = now();
    t_end = t0 + limit * 0.92;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best;
    if (d < 1 || D < 1 || d > MAXD) { complete_bipartite(&best); print_graph(&best); return 0; }

    if (mode == 1 && D >= 2) {
        static Graph U, A, R, B, tmp;
        static int comp[MAXN];
        int A_ok = 0, B_ok = 0;
        read_raw(&U);
        if (U.n > 0) {
            label_components(&U, comp);
            int raw_c = -1, raw_n = 0;
            for (int c = 0; c < ncomp; c++) {
                int sz = 0, md = 0;
                for (int v = 0; v < U.n; v++)
                    if (comp[v] == c) { sz++; if (U.deg[v] > md) md = U.deg[v]; }
                if (md > d) {
                    if (sz > raw_n) { raw_n = sz; raw_c = c; }
                } else {
                    extract(&U, comp, c, &tmp);
                    if (is_valid(&tmp) && (!A_ok || tmp.n > A.n)) {
                        copy_graph(&A, &tmp);
                        A_ok = 1;
                    }
                }
            }
            if (raw_c >= 0) {
                extract(&U, comp, raw_c, &R);
                delete_search(&R, &B, t0 + (t_end - t0) * 0.35);
                B_ok = B.n > 0 && is_valid(&B);
            }
        }
        if (B_ok && (!A_ok || B.n > A.n)) copy_graph(&best, &B);
        else if (A_ok) copy_graph(&best, &A);
    } else {
        read_start(&best);
    }
    int had_start = best.n > 0;

    if (D >= 2 && best.n < moore_bound()) {
        if (had_start) {
            grow_search(&best, t_end);
        } else {
            double span = t_end - t0;
            haar_search(&best, t0 + span * 0.4);
            double nt = now();
            lift_search(&best, nt + (t_end - nt) * 0.4);
            if (best.n > 0) grow_search(&best, t_end);
        }
    }
    if (best.n == 0) complete_bipartite(&best);
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


# ---------------------------------------------------------------- Python constructions

def _pg_base(d):
    """Incidence graph of PG(2,q), q the largest prime power <= d-1."""
    q = d - 1
    while q >= 2 and not lib.is_prime_power(q):
        q -= 1
    if q < 2:
        return None
    return lib.projective_plane_incidence(q)


def _pg_raw(d):
    """Incidence graph of PG(2,q) for the smallest prime power q >= d-1 (degree q+1 > d).
    Too dense for (d, 3); the C engine deletes vertices from it."""
    q = d - 1
    while q <= PG_RAW_Q_MAX and not lib.is_prime_power(q):
        q += 1
    if q > PG_RAW_Q_MAX or q < 2:
        return None
    return lib.projective_plane_incidence(q)


def _union(a, b):
    """Disjoint union of two graphs (n, edges); vertices of b are shifted by a's order."""
    na, ea = a
    nb, eb = b
    return na + nb, list(ea) + [(u + na, v + na) for u, v in eb]


def _gq_w(q):
    """Point-line incidence graph of the generalized quadrangle W(q): degree q+1, diameter 4."""
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


def _best_gq(d):
    """W(q) for the largest prime power q <= min(d-1, GQ_Q_MAX)."""
    for q in range(min(d - 1, GQ_Q_MAX), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def known_start(d, D):
    """Best known construction Python builds directly for (d, D), or None."""
    if D == 3:
        if lib.is_prime_power(d - 1):
            return lib.projective_plane_incidence(d - 1)       # Moore graph, optimal
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                return lib.araujo_lopez_graph(d - 2)           # record 2(q^2+q+5), q = d-2
            except ValueError:
                return None
        return None
    if D >= 4:
        return _best_gq(d)
    return None


def _two_colour(n, edges):
    """Proper 2-colouring (0/1 per vertex) of a bipartite graph, component by component."""
    adj = lib.adjacency(n, edges)
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
    return color


def _augment(n, edges, d, seed):
    """Add edges between opposite colour classes using spare degree (keeps bipartite, shrinks distances)."""
    rng = random.Random(seed + 7)
    color = _two_colour(n, edges)
    deg = [0] * n
    adj = [set() for _ in range(n)]
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
        adj[u].add(v)
        adj[v].add(u)
    side0 = [u for u in range(n) if color[u] == 0]
    side1 = [v for v in range(n) if color[v] == 1]
    new_edges = list(edges)
    for _ in range(3):
        us = [u for u in side0 if deg[u] < d]
        rng.shuffle(us)
        for u in us:
            if deg[u] >= d:
                continue
            cands = [v for v in side1 if deg[v] < d and v not in adj[u]]
            if not cands:
                continue
            v = rng.choice(cands)
            adj[u].add(v)
            adj[v].add(u)
            deg[u] += 1
            deg[v] += 1
            new_edges.append((u, v))
    return n, new_edges


def _extend(n, edges, d, D, rng, deadline):
    """Greedily add vertices whose neighbourhoods cover all radius-(D-1) balls (keeps diameter D)."""
    edges = list(edges)
    if D < 2 or n == 0:
        return n, edges
    color = _two_colour(n, edges)
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
    while time.monotonic() < deadline:
        full = (1 << n) - 1
        balls = lib._balls(n, edges, D - 1)
        grown = False
        order = [0, 1] if rng.random() < 0.5 else [1, 0]
        for c in order:
            cand = [u for u in range(n) if color[u] == 1 - c and deg[u] < d]
            rng.shuffle(cand)
            covered, chosen = 0, []
            while covered != full and len(chosen) < d and cand:
                best_u, best_gain = -1, 0
                for u in cand:
                    g = (balls[u] & ~covered).bit_count()
                    if g > best_gain:
                        best_u, best_gain = u, g
                if best_u < 0:
                    break
                chosen.append(best_u)
                covered |= balls[best_u]
                cand.remove(best_u)
            if covered == full and chosen:
                x = n
                n += 1
                color.append(c)
                deg.append(len(chosen))
                for u in chosen:
                    edges.append((u, x))
                    deg[u] += 1
                grown = True
                break
        if not grown:
            break
    return n, edges


def _finish(cands, d, D):
    """Largest candidate that passes lib.is_valid, else K_{d,d}."""
    for n, e in sorted(cands, key=lambda c: -c[0]):
        if lib.is_valid(n, e, d, D):
            return n, e
    return lib.haar_graph(d, range(d))


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if D == 2:
        return lib.haar_graph(d, range(d))          # K_{d,d} is extremal for D = 2

    cands = [lib.haar_graph(d, range(d))]           # K_{d,d}: always valid

    start = None
    try:
        start = known_start(d, D)
    except Exception:
        start = None
    if start is not None and not lib.is_valid(start[0], start[1], d, D):
        start = None
    if start is not None:
        cands.append(start)

    base = None
    if start is None and d >= 3 and D == 3:
        try:
            base = _pg_base(d)
            if base is not None:
                cands.append(base)
                aug = _augment(base[0], base[1], d, seed)
                cands.append(_extend(aug[0], aug[1], d, D, rng,
                                     time.monotonic() + 0.05 * time_limit))
        except Exception:
            base = None

    best = _finish(cands, d, D)

    # Moore-extremal start: nothing to search for.
    if start is not None and start[0] >= lib.moore_bound(d, D):
        return best

    budget = TIME_FRAC * time_limit - (time.monotonic() - t0) - 1.5
    if budget > 1.0:
        seedg = start if start is not None else base
        raw = None
        if D == 3 and d >= 4 and not lib.is_prime_power(d - 1) and seedg is not None:
            try:
                raw = _pg_raw(d)
            except Exception:
                raw = None
        try:
            if raw is not None:
                union = _union(seedg, raw)
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), 1],
                                 stdin_graph=union, timeout=budget + 5)
            else:
                stdin_graph = best if best[0] > 2 * d else None
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), 0],
                                 stdin_graph=stdin_graph, timeout=budget + 5)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except (RuntimeError, ValueError):
            pass                                    # keep the valid Python fallback
    return best
