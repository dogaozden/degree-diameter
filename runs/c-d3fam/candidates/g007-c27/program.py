"""Combined program, v2. Target cases (D = 3, d >= 7) get a second, different construction.

Run A is the parent pipeline: the best known construction, augmented, then the C engine grows it
by two (voltage lifts are skipped when there is a start). Run B is new: start from the incidence
graph of PG(2,q') with q' the smallest prime power >= d-1, which has degree q'+1 >= d. Greedily
delete vertices until the maximum degree is <= d, shrink toward 0.88 * Moore bound, and refill
spare degree. The graph is then not diameter-valid, so the C engine runs a RAW repair (annealed
degree-preserving swaps plus spare-degree fills, minimising bad pairs) before growing by two.

Every candidate is checked with lib.is_valid before it can replace the output, and the parent's
valid construction is always kept as the fallback. A failed C run costs only its own budget.
"""
import itertools
import random
import time

import lib

GQ_Q_MAX = 9        # largest q for which the generalized quadrangle W(q) is built in Python
TIME_FRAC = 0.92    # fraction of time_limit spent in total (C stops at 96% of its own budget)
SEED_FRAC = 0.88    # raw seed is shrunk to this fraction of the Moore bound

C_SOURCE = r'''
/* Bipartite degree-diameter search core.
 *
 * Usage:   prog d D seed time_limit [raw]   < start_graph
 * stdin:   "n m" then m lines "u v": a start graph, or "0 0" for none.
 *          With raw = 1 the start only needs to be simple, bipartite, with max degree <= d;
 *          its diameter is repaired first.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * Search:
 *   0. Raw repair (raw = 1 and start invalid): annealing that minimises bad pairs, with
 *      spare-degree fills.
 *   1. Voltage lifts over semidirect products Z_m x| Z_k (only when there is no start).
 *   2. Grow by two: insert one vertex per side using spare degree from d-1 deleted edges,
 *      then repair until every pair is within distance D. Two repair modes alternate:
 *        - annealing: random or targeted degree-preserving swaps, accepted by Metropolis rule;
 *        - tabu: sample several targeted swaps for a bad vertex, apply the best, forbid touching
 *          its vertices for a short tenure (aspiration allowed for a new best count).
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
#define TABU_SAMPLE 16
#define TABU_TENURE 6

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static double t_end;
static int raw_mode = 0;

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
/* Reach balls of the most recent bad_pairs call: bit w of ball v is set iff dist(v,w) <= D. */
static uint64_t *final_reach = RA;
static int final_W = 0;

/* Number of unordered pairs at distance > D (0 means diameter <= D and connected). */
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

/* True if dist(v, w) <= D according to the last bad_pairs call. */
static int reached(int v, int w) {
    return (int)((final_reach[(size_t)v * final_W + w / 64] >> (w % 64)) & 1ULL);
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

static void read_start(Graph *g) {
    int n, m;
    g->n = 0;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN) return;
    g->n = n;
    for (int v = 0; v < n; v++) { g->deg[v] = 0; g->side[v] = 255; }
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= n || v >= n ||
            u == v || g->deg[u] >= MAXD || g->deg[v] >= MAXD || has_edge(g, u, v)) {
            g->n = 0;
            return;
        }
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
    if (raw_mode) {
        /* Raw start: only degree and bipartiteness are required here. */
        for (int v = 0; v < g->n; v++)
            if (g->deg[v] > d) { g->n = 0; return; }
        return;
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

/* K_{d,d}: always valid for D >= 2. */
static void complete_bipartite(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= d; }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
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
    return bad == 0;
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

/* ------------------------------------------------------------------ swaps */

/* Propose a degree-preserving swap (v,u),(s,t) -> (v,t),(s,u) with side(v) != side(t) and
 * side(s) == side(v). Random mode picks s uniformly; targeted mode picks t near an unreached
 * partner w of v (distance 1 if w is on v's side, 2 otherwise), so v gets a short route to w. */
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
            if (c != v && !reached(v, c)) { w = c; break; }
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

/* Apply the swap, accept or revert by the annealing rule. Returns the bad-pair count of the
 * resulting graph; badv and the reach balls are refreshed for whichever state is kept. */
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

/* Add one edge between opposite sides when both ends have spare degree (never increases the
 * bad-pair count). Refreshes *bad and badv when it succeeds. */
static void fill_spare(Graph *g, long *bad) {
    for (int tries = 0; tries < 64; tries++) {
        int v = rndint(g->n);
        if (g->deg[v] >= d) continue;
        int w = rndint(g->n);
        if (w == v || g->side[w] == g->side[v] || g->deg[w] >= d || has_edge(g, v, w)) continue;
        add_edge(g, v, w);
        *bad = bad_pairs(g);
        return;
    }
}

/* Raw repair: start from any simple bipartite graph with max degree <= d and drive the bad-pair
 * count to zero with annealed swaps and spare-degree fills. Returns 1 if the result is valid. */
static int repair_raw(Graph *g, double until) {
    if (g->n <= 0) return 0;
    long bad = bad_pairs(g);
    double T = 1.0;
    long it = 0;
    while (bad > 0) {
        if ((++it & 15) == 0 && now() > until) return 0;
        if ((it & 3) == 0) fill_spare(g, &bad);
        if (bad == 0) break;
        int v = rndint(g->n);
        for (int tries = 0; tries < 30 && badv[v] == 0; tries++) v = rndint(g->n);
        int u, s, t;
        int targeted = rndint(3) != 0;
        if (!propose(g, v, &u, &s, &t, targeted)) continue;
        bad = apply_swap(g, v, u, s, t, bad, T);
        T *= 0.9995;
        if (T < 0.05) T = 1.0;
    }
    return is_valid(g);
}

/* ------------------------------------------------------------------ grow by two */

/* Copy best into work and insert a new adjacent pair (x = n on side 0, y = n+1 on side 1).
 * The pair takes d-1 edges each from deleted old edges, so every degree stays <= d. */
static void insert_pair(const Graph *best, Graph *work) {
    int n = best->n;
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
}

/* Repair mode 1: simulated annealing over swaps. */
static int grow_once(const Graph *best, Graph *work, double until) {
    if (best->n + 2 > moore_bound() || best->n + 2 > MAXN) return 0;
    insert_pair(best, work);
    long bad = bad_pairs(work);
    double T = 1.0;
    long it = 0;
    while (bad > 0) {
        if ((++it & 15) == 0 && now() > until) return 0;
        int v = rndint(work->n);
        for (int tries = 0; tries < 30 && badv[v] == 0; tries++) v = rndint(work->n);
        int u, s, t;
        int targeted = rndint(3) != 0;   /* two thirds of proposals are targeted */
        if (!propose(work, v, &u, &s, &t, targeted)) continue;
        bad = apply_swap(work, v, u, s, t, bad, T);
        T *= 0.9995;
        if (T < 0.05) T = 1.0;
    }
    return is_valid(work);
}

/* Evaluate one swap (v,u),(s,t) -> (v,t),(s,u) without keeping it. Returns the bad-pair count
 * of the modified graph. The graph is restored afterwards, but the reach balls then describe
 * the modified graph, so the caller must call bad_pairs(work) before proposing again. */
static long tabu_eval(Graph *work, int v, int u, int s, int t) {
    del_edge(work, v, u);
    del_edge(work, s, t);
    add_edge(work, v, t);
    add_edge(work, s, u);
    long nb = bad_pairs(work);
    del_edge(work, v, t);
    del_edge(work, s, u);
    add_edge(work, v, u);
    add_edge(work, s, t);
    return nb;
}

/* Repair mode 2: tabu search. Each step samples up to TABU_SAMPLE proposals for a bad vertex,
 * applies the one leaving the fewest bad pairs, and makes its three vertices tabu for a while. */
static int tabu_grow(const Graph *best, Graph *work, double until) {
    if (best->n + 2 > moore_bound() || best->n + 2 > MAXN) return 0;
    insert_pair(best, work);
    static long tabu_until[MAXN];
    for (int i = 0; i < MAXN; i++) tabu_until[i] = 0;
    long bad = bad_pairs(work);
    long bestbad = bad;
    long it = 0;
    while (bad > 0) {
        if ((++it & 7) == 0 && now() > until) return 0;
        int v = rndint(work->n);
        for (int tries = 0; tries < 30 && badv[v] == 0; tries++) v = rndint(work->n);
        int cu[TABU_SAMPLE], cs[TABU_SAMPLE], ct[TABU_SAMPLE], nc = 0;
        for (int c = 0; c < 4 * TABU_SAMPLE && nc < TABU_SAMPLE; c++) {
            int u, s, t;
            if (propose(work, v, &u, &s, &t, rndint(3) != 0)) {
                cu[nc] = u; cs[nc] = s; ct[nc] = t; nc++;
            }
        }
        if (nc == 0) continue;
        int bi = -1;
        long bnb = 0;
        for (int c = 0; c < nc; c++) {
            long nb = tabu_eval(work, v, cu[c], cs[c], ct[c]);
            int is_tabu = tabu_until[v] > it || tabu_until[cs[c]] > it || tabu_until[ct[c]] > it;
            if (is_tabu && nb >= bestbad) continue;   /* aspiration: tabu allowed only if new best */
            if (bi < 0 || nb < bnb || (nb == bnb && rndint(2))) { bi = c; bnb = nb; }
        }
        bad_pairs(work);                               /* resync reach with the unchanged graph */
        if (bi < 0) continue;
        int u = cu[bi], s = cs[bi], t = ct[bi];
        del_edge(work, v, u);
        del_edge(work, s, t);
        add_edge(work, v, t);
        add_edge(work, s, u);
        bad = bad_pairs(work);
        long ten = it + TABU_TENURE + rndint(TABU_TENURE);
        tabu_until[v] = ten;
        tabu_until[s] = ten;
        tabu_until[t] = ten;
        if (bad < bestbad) bestbad = bad;
    }
    return is_valid(work);
}

static void grow_search(Graph *best, double until) {
    static Graph work;
    int attempt = 0;
    while (now() < until && best->n + 2 <= moore_bound()) {
        double left = until - now();
        double slice = left < 4.0 ? left : (left / 2 > 4.0 ? left / 2 : 4.0);
        int ok = (attempt++ & 1) ? tabu_grow(best, &work, now() + slice)
                                 : grow_once(best, &work, now() + slice);
        if (ok) copy_graph(best, &work);
    }
}

/* ------------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [raw] < start_graph\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    raw_mode = argc >= 6 && atoi(argv[5]) == 1;
    double t0 = now();
    t_end = t0 + limit * 0.96;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best;
    if (d < 1 || D < 1 || d > MAXD) { complete_bipartite(&best); print_graph(&best); return 0; }
    read_start(&best);
    int had_start = best.n > 0;

    if (had_start && !is_valid(&best)) {
        /* Raw start: repair its diameter first, with 70% of the budget at most. */
        if (!repair_raw(&best, t0 + (t_end - t0) * 0.7)) best.n = 0;
        had_start = best.n > 0;
    }

    if (D >= 2 && best.n < moore_bound()) {
        /* With a valid start, all time goes to grow-by-two; lifts are only used from scratch. */
        double tl = now();
        double lift_share = had_start ? 0.0 : 0.6;
        lift_search(&best, tl + (t_end - tl) * lift_share);
        if (best.n > 0) grow_search(&best, t_end);
    }
    if (best.n == 0) complete_bipartite(&best);
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


# ---------------------------------------------------------------- helpers

def _two_colour(n, edges):
    """Proper 2-colouring of a bipartite graph, component by component."""
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


def _deleted_plane(d, D, seed):
    """Raw seed (not diameter-valid): PG(2,q') incidence with q' the smallest prime power >= d-1.

    Greedily delete the vertex with the most over-degree neighbours until max degree <= d,
    shrink randomly to SEED_FRAC * Moore bound, then refill spare degree between points and lines.
    Returns (n, edges) with max degree <= d and bipartite, or None.
    """
    q = d - 1
    while not lib.is_prime_power(q):
        q += 1
    n, edges = lib.projective_plane_incidence(q)
    half = n // 2                       # points are 0..half-1, lines half..n-1
    rng = random.Random(seed + 101)
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    alive = [True] * n
    deg = [len(a) for a in adj]

    def remove(x):
        alive[x] = False
        for y in adj[x]:
            if alive[y]:
                deg[y] -= 1

    # Phase 1: greedy deletion until no alive vertex exceeds degree d.
    while any(alive[v] and deg[v] > d for v in range(n)):
        best_s, cand = -1, []
        for x in range(n):
            if not alive[x]:
                continue
            s = sum(1 for y in adj[x] if alive[y] and deg[y] > d)
            if s > best_s:
                best_s, cand = s, [x]
            elif s == best_s:
                cand.append(x)
        remove(rng.choice(cand))

    # Phase 2: random shrink toward the target size.
    target = int(SEED_FRAC * lib.moore_bound(d, D))
    live = [v for v in range(n) if alive[v]]
    rng.shuffle(live)
    count = len(live)
    for x in live:
        if count <= target:
            break
        remove(x)
        count -= 1

    # Phase 3: refill spare degree between alive points and lines.
    pts = [v for v in range(half) if alive[v]]
    lns = [v for v in range(half, n) if alive[v]]
    rng.shuffle(pts)
    for p in pts:
        if deg[p] >= d:
            continue
        opts = [l for l in lns if deg[l] < d and l not in adj[p]]
        rng.shuffle(opts)
        for l in opts:
            if deg[p] >= d:
                break
            if deg[l] >= d:
                continue
            adj[p].add(l)
            adj[l].add(p)
            deg[p] += 1
            deg[l] += 1

    out = [(u, v) for u in range(n) if alive[u] for v in adj[u] if alive[v] and u < v]
    if not out:
        return None
    nn, ee = lib.relabel(out)
    if lib.max_degree(nn, ee) > d or not lib.is_bipartite(nn, ee):
        return None
    return nn, ee


def _pg_base(d):
    """Incidence graph of PG(2,q), q the largest prime power <= d-1."""
    q = d - 1
    while q >= 2 and not lib.is_prime_power(q):
        q -= 1
    if q < 2:
        return None
    return lib.projective_plane_incidence(q)


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
    """Best known construction for (d, D) that Python can build directly, or None."""
    if D == 3:
        if lib.is_prime_power(d - 1):
            return lib.projective_plane_incidence(d - 1)     # Moore graph
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            return lib.araujo_lopez_graph(d - 2)             # record 2(q^2+q+5), q = d-2
        return _pg_base(d)                                   # fallback: PG(2,q), q < d-1
    if D >= 4:
        return _best_gq(d)                                   # diameter 4 <= D
    return None


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    t0 = time.monotonic()

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    kdd = lib.haar_graph(d, range(d))          # K_{d,d}: diameter 2, always valid
    if D == 2:
        return kdd

    best = None
    try:
        best = known_start(d, D)
    except Exception:
        best = None
    if best is None or not lib.is_valid(best[0], best[1], d, D):
        best = kdd

    if best[0] >= lib.moore_bound(d, D):
        return best                            # Moore graph: nothing to search for

    start = best
    try:
        aug = _augment(best[0], best[1], d, seed)
        if lib.is_valid(aug[0], aug[1], d, D):
            start = aug
    except Exception:
        start = best

    def remaining():
        return TIME_FRAC * time_limit - (time.monotonic() - t0) - 1.5

    def consider(graph):
        nonlocal best
        try:
            n, e = graph
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
        except Exception:
            pass

    def run(start_graph, budget, raw):
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), 1 if raw else 0],
                         stdin_graph=start_graph, timeout=budget + 5)
        return lib.parse_graph_text(text)

    if D == 3 and d >= 7:
        # Run A: parent pipeline from the best known construction (half the remaining time).
        budget_a = remaining() * 0.5
        if budget_a > 1.0:
            try:
                consider(run(start, budget_a, False))
            except Exception:
                pass                           # keep the valid construction
        # Run B: new raw-deletion seed from PG(2,q'), repaired by annealing, then grown.
        try:
            raw_seed = _deleted_plane(d, D, seed)
        except Exception:
            raw_seed = None
        budget_b = remaining()
        if raw_seed is not None and budget_b > 1.0:
            try:
                consider(run(raw_seed, budget_b, True))
            except Exception:
                pass
    else:
        budget = remaining()
        if budget > 1.0:
            try:
                consider(run(start, budget, False))
            except Exception:
                pass
    return best
