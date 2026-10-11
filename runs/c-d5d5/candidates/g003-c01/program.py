"""Combined program: known constructions as a start, then a C engine that
(1) searches orbit-reduced bi-Cayley lifts over Z_m x| Z_k (cost = unreached
representative pairs, with base 2-switches and voltage moves),
(2) prunes and refills an annealed larger lift (remove worst pairs, refill
degree slots, anneal 2-switches), and
(3) grows by two vertices and anneals edge swaps until the diameter holds."""
import time

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search core.
 *
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v": a valid start graph, or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * Phases:
 *  1. Lift search. A lift has k vertices per side, group G = Z_m x|_r Z_k2 of order N.
 *     Base darts (i, j, s) give edges A_{i,g} - B_{j, g*s}. Left multiplication is an
 *     automorphism, so diameter <= D iff every representative A_{i,1}, B_{j,1} reaches
 *     all 2kN vertices within D steps. Cost = unreached pairs + duplicate-dart penalty.
 *  2. Prune and refill: anneal a lift a few vertices larger (full bad-pair cost), then
 *     repeatedly remove the worst vertex on each side, refill degree slots, and anneal
 *     2-switches. Any valid graph larger than the best replaces it.
 *  3. Grow by two: add one vertex per side, then anneal swaps until valid.
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
#define MAXG 1024
#define MAXK 4
#define MAXDARTS (MAXD * MAXK)

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static long moore;
static double t_end;
static Graph best;

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
static long compute_moore(void) {
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

/* Remove vertex v (its edges first), moving the last vertex into slot v. */
static void remove_vertex(Graph *g, int v) {
    while (g->deg[v] > 0) {
        int u = g->adj[v][0];
        del_edge(g, v, u);
    }
    int last = g->n - 1;
    if (v != last) {
        for (int i = 0; i < g->deg[last]; i++) {
            int u = g->adj[last][i];
            for (int j = 0; j < g->deg[u]; j++)
                if (g->adj[u][j] == last) { g->adj[u][j] = v; break; }
        }
        g->deg[v] = g->deg[last];
        g->side[v] = g->side[last];
        memcpy(g->adj[v], g->adj[last], sizeof(int) * g->deg[last]);
    }
    g->deg[last] = 0;
    g->n--;
}

/* ------------------------------------------------------------------ distance check */

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static int badv[MAXN]; /* vertices farther than D from each vertex, set by bad_pairs() */

/* Unordered pairs at distance > D. Bitset reachability over D rounds. */
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

/* Full validity: simple, bipartite by side labels, degree <= d, diameter <= D. */
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

/* ------------------------------------------------------------------ groups */

/* Z_m x|_r Z_k: element (a, b) is a*k + b; (a,b)(c,e) = (a + r^b c mod m, b + e mod k). */
typedef struct {
    int m, k, r, N;
    int rp[MAXG]; /* rp[b] = r^b mod m */
} Grp;

static int *MT = NULL;   /* MT[x*N + y] = x*y for the current group */
static long MTcap = 0;

static void set_group(Grp *G) {
    int N = G->m * G->k;
    G->N = N;
    G->rp[0] = 1 % G->m;
    for (int b = 1; b < G->k; b++) G->rp[b] = (int)((long)G->rp[b - 1] * G->r % G->m);
    if ((long)N * N > MTcap) {
        free(MT);
        MTcap = (long)N * N;
        MT = (int *)malloc(sizeof(int) * MTcap);
    }
    for (int x = 0; x < N; x++) {
        int a = x / G->k, b = x % G->k;
        for (int y = 0; y < N; y++) {
            int c = y / G->k, e = y % G->k;
            MT[x * N + y] = (int)(((long)a + (long)G->rp[b] * c) % G->m) * G->k + (b + e) % G->k;
        }
    }
}

/* Uniform random (m, k, r) with m*k = N, gcd(r, m) = 1, r^k = 1 mod m. Sets MT. */
static int random_group(int N, Grp *G) {
    long count = 0;
    int found = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        int rmax = m > 1 ? m : 2;
        for (int r = 1; r < rmax; r++) {
            if (m > 1 && gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            count++;
            if (rndint((int)count) == 0) { G->m = m; G->k = k; G->r = r; found = 1; }
        }
    }
    if (!found) return 0;
    set_group(G);
    return 1;
}

/* ------------------------------------------------------------------ lifts */

typedef struct { int i, j, g; } Dart;     /* A_i -> B_j with voltage g */
typedef struct { int type, t1, t2, old; } Undo;

/* Layered base: d random perfect matchings between k A-vertices and k B-vertices. */
static int layered_darts(int k, int N, Dart *dt) {
    int nd = 0;
    for (int l = 0; l < d; l++) {
        int perm[MAXK];
        for (int i = 0; i < k; i++) perm[i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rndint(i + 1), s = perm[i];
            perm[i] = perm[j];
            perm[j] = s;
        }
        for (int i = 0; i < k; i++) {
            dt[nd].i = i;
            dt[nd].j = perm[i];
            dt[nd].g = rndint(N);
            nd++;
        }
    }
    return nd;
}

/* Move: swap the B-targets of two darts (keeps every degree), or change one voltage. */
static void mutate(Dart *dt, int nd, int k, int N, Undo *u) {
    if (k > 1 && rnd01() < 0.4) {
        u->type = 1;
        u->t1 = rndint(nd);
        u->t2 = rndint(nd);
        int tmp = dt[u->t1].j;
        dt[u->t1].j = dt[u->t2].j;
        dt[u->t2].j = tmp;
    } else {
        u->type = 0;
        u->t1 = rndint(nd);
        u->old = dt[u->t1].g;
        dt[u->t1].g = rndint(N);
    }
}

static void undo_move(Dart *dt, const Undo *u) {
    if (u->type == 1) {
        int tmp = dt[u->t1].j;
        dt[u->t1].j = dt[u->t2].j;
        dt[u->t2].j = tmp;
    } else {
        dt[u->t1].g = u->old;
    }
}

static long dup_pairs(const Dart *dt, int nd) {
    long pen = 0;
    for (int t = 0; t < nd; t++)
        for (int u = 0; u < t; u++)
            if (dt[t].i == dt[u].i && dt[t].j == dt[u].j && dt[t].g == dt[u].g) pen++;
    return pen;
}

/* Orbit-reduced scratch space. */
static int adjL[MAXN][MAXD];
static int degL[MAXN];
static int visL[MAXN];
static int qL[MAXN];
static int stampL = 0;

/* Cost = 1e6 * duplicate darts + unreached (representative, vertex) pairs.
 * Representatives are the vertices r*N (group identity) for r = 0..2k-1. */
static long orbit_cost(const Dart *dt, int nd, int k, int N) {
    int n = 2 * k * N;
    long pen = dup_pairs(dt, nd);
    for (int v = 0; v < n; v++) degL[v] = 0;
    for (int t = 0; t < nd; t++)
        for (int g = 0; g < N; g++) {
            int a = dt[t].i * N + g;
            int b = (k + dt[t].j) * N + MT[g * N + dt[t].g];
            adjL[a][degL[a]++] = b;
            adjL[b][degL[b]++] = a;
        }
    long unreached = 0;
    for (int r = 0; r < 2 * k; r++) {
        int src = r * N;
        stampL++;
        int head = 0, tail = 0;
        visL[src] = stampL;
        qL[tail++] = src;
        for (int lev = 0; lev < D && head < tail; lev++) {
            int end = tail;
            while (head < end) {
                int u = qL[head++];
                for (int i = 0; i < degL[u]; i++) {
                    int v = adjL[u][i];
                    if (visL[v] != stampL) { visL[v] = stampL; qL[tail++] = v; }
                }
            }
        }
        unreached += n - tail;
    }
    return pen * 1000000L + unreached;
}

static void build_lift(Graph *g, int k, int N, const Dart *dt, int nd) {
    g->n = 2 * k * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= k * N; }
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, dt[t].i * N + x, (k + dt[t].j) * N + MT[x * N + dt[t].g]);
}

/* Full cost on the built lift: bad pairs plus a duplicate-dart penalty. */
static long full_cost(Graph *g, int k, int N, const Dart *dt, int nd) {
    build_lift(g, k, N, dt, nd);
    return bad_pairs(g) + dup_pairs(dt, nd) * 100000L;
}

static long anneal_orbit(Dart *dt, int nd, int k, int N, int steps, double until) {
    long c = orbit_cost(dt, nd, k, N);
    Undo u;
    for (int s = 0; s < steps && c > 0; s++) {
        if ((s & 255) == 0 && now() > until) break;
        mutate(dt, nd, k, N, &u);
        long c2 = orbit_cost(dt, nd, k, N);
        if (c2 <= c || rnd01() < 0.01) c = c2;
        else undo_move(dt, &u);
    }
    return c;
}

/* Anneal the darts with full bad-pair cost. Leaves g = the lift of the final darts. */
static void anneal_full(Graph *g, int k, int N, Dart *dt, int nd, int steps, double until) {
    long c = full_cost(g, k, N, dt, nd);
    Undo u;
    for (int s = 0; s < steps && c > 0; s++) {
        if ((s & 15) == 0 && now() > until) break;
        mutate(dt, nd, k, N, &u);
        long c2 = full_cost(g, k, N, dt, nd);
        if (c2 <= c || rnd01() < 0.02) c = c2;
        else undo_move(dt, &u);
    }
    build_lift(g, k, N, dt, nd);
}

/* Phase 1: orbit-reduced lift search. Only accepts strictly larger valid graphs. */
static void lift_phase(double until) {
    static Graph cand;
    static Grp G;
    static Dart dt[MAXDARTS];
    static const int kc[6] = {1, 1, 1, 2, 2, 3};
    int fails = 0;
    while (now() < until && best.n < moore) {
        int k = kc[rndint(6)];
        long target = best.n + 2;
        long N = (target + 2 * k - 1) / (2 * k) + rndint(3);
        if (N < d) N = d;
        if (N > MAXG || 2L * k * N > moore || 2L * k * N > MAXN) {
            if (++fails > 5000) return;
            continue;
        }
        if (!random_group((int)N, &G)) continue;
        int nd = layered_darts(k, (int)N, dt);
        long c = anneal_orbit(dt, nd, k, (int)N, 4000, until);
        if (c == 0) {
            build_lift(&cand, k, (int)N, dt, nd);
            if (cand.n > best.n && is_valid(&cand)) copy_graph(&best, &cand);
        }
    }
}

/* ------------------------------------------------------------------ prune and refill */

/* Greedily add edges between deficient opposite-side vertices. Never increases bad pairs. */
static void fill_pass(Graph *g) {
    static int LA[MAXN], LB[MAXN];
    int na = 0, nb = 0;
    for (int v = 0; v < g->n; v++) {
        if (g->deg[v] >= d) continue;
        if (g->side[v] == 0) LA[na++] = v; else LB[nb++] = v;
    }
    for (int i = na - 1; i > 0; i--) { int j = rndint(i + 1); int t = LA[i]; LA[i] = LA[j]; LA[j] = t; }
    for (int i = nb - 1; i > 0; i--) { int j = rndint(i + 1); int t = LB[i]; LB[i] = LB[j]; LB[j] = t; }
    for (int i = 0; i < na; i++) {
        int a = LA[i];
        for (int j = 0; j < nb && g->deg[a] < d; j++) {
            int b = LB[j];
            if (g->deg[b] >= d || has_edge(g, a, b)) continue;
            add_edge(g, a, b);
        }
    }
}

/* Degree-preserving 2-switch (v-u, s-t) -> (v-t, s-u), v and s on the same side. */
static void switch_move(Graph *g, long *bad, double T) {
    int n = g->n;
    int v = rndint(n);
    if (g->deg[v] == 0) return;
    int u = g->adj[v][rndint(g->deg[v])];
    int s = rndint(n);
    if (s == v || g->side[s] != g->side[v] || g->deg[s] == 0) return;
    int t = g->adj[s][rndint(g->deg[s])];
    if (t == u || has_edge(g, v, t) || has_edge(g, s, u)) return;
    del_edge(g, v, u);
    del_edge(g, s, t);
    add_edge(g, v, t);
    add_edge(g, s, u);
    long nb = bad_pairs(g);
    if (nb <= *bad || rnd01() < exp((double)(*bad - nb) / T)) {
        *bad = nb;
    } else {
        del_edge(g, v, t);
        del_edge(g, s, u);
        add_edge(g, v, u);
        add_edge(g, s, t);
    }
}

/* Vertex on the given side with the most bad pairs (random ties; sometimes uniform). */
static int worst_on(const Graph *g, int side) {
    if (rnd01() < 0.2) {
        for (int tries = 0; tries < 1000; tries++) {
            int v = rndint(g->n);
            if (g->side[v] == side) return v;
        }
    }
    int bestv = -1, ties = 0;
    long bv = -1;
    for (int v = 0; v < g->n; v++) {
        if (g->side[v] != side) continue;
        if ((long)badv[v] > bv) { bv = badv[v]; bestv = v; ties = 1; }
        else if ((long)badv[v] == bv) { ties++; if (rndint(ties) == 0) bestv = v; }
    }
    return bestv;
}

/* Start from a near-valid graph larger than best. Refill, anneal, prune one vertex per side. */
static void prune_round(const Graph *start, double until) {
    static Graph w;
    copy_graph(&w, start);
    long bad = bad_pairs(&w);
    while (bad > 0 && now() < until && w.n - 2 > best.n) {
        fill_pass(&w);
        bad = bad_pairs(&w);
        if (bad == 0) break;
        for (int it = 0; it < 300 && bad > 0; it++) switch_move(&w, &bad, 0.6);
        if (bad == 0) break;
        bad = bad_pairs(&w); /* refresh badv for the current state */
        int a = worst_on(&w, 0), b = worst_on(&w, 1);
        if (a < 0 || b < 0 || a == b) break;
        int hi = a > b ? a : b, lo = a > b ? b : a;
        remove_vertex(&w, hi);
        remove_vertex(&w, lo);
        bad = bad_pairs(&w);
    }
    fill_pass(&w);
    bad = bad_pairs(&w);
    if (bad == 0 && w.n > best.n && is_valid(&w)) copy_graph(&best, &w);
}

/* Phase 2: anneal slightly larger lifts, then prune and refill them. */
static void prune_search(double until) {
    static Graph cand;
    static Grp G;
    static Dart dt[MAXDARTS];
    int fails = 0;
    while (now() < until && best.n > 0) {
        int k = 1 + rndint(4);
        long extra = 2 * (2 + rndint(6));
        long target = (long)best.n + extra;
        long N = (target + 2 * k - 1) / (2 * k);
        if (N < d) N = d;
        if (N > MAXG || 2L * k * N > best.n + 40 || 2L * k * N > MAXN || 2L * k * N > 2 * moore) {
            if (++fails > 1000) return;
            continue;
        }
        if (!random_group((int)N, &G)) continue;
        int nd = layered_darts(k, (int)N, dt);
        int steps = 300 + (int)(200000 / (2L * k * N));
        anneal_full(&cand, k, (int)N, dt, nd, steps, until);
        prune_round(&cand, until);
    }
}

/* ------------------------------------------------------------------ grow by two */

static int grow_once(const Graph *base, Graph *work, double until) {
    int n = base->n;
    if (n + 2 > moore || n + 2 > MAXN) return 0;
    copy_graph(work, base);
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
    int k = 0;
    for (int tries = 0; k < d - 1 && tries < 100000; tries++) {
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

/* Phase 3: repeatedly grow the best graph by two vertices. */
static void grow_search(double until) {
    static Graph work;
    while (now() < until && best.n + 2 <= moore) {
        double left = until - now();
        double slice = left < 4.0 ? left : (left / 4 > 4.0 ? left / 4 : 4.0);
        if (grow_once(&best, &work, now() + slice)) copy_graph(&best, &work);
    }
}

/* ------------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit < start_graph\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    if (d < 1 || d > MAXD || D < 1) {
        printf("0 0\n");
        return 0;
    }
    if (D < 2) {
        printf("2 1\n0 1\n");
        return 0;
    }

    double t0 = now();
    t_end = t0 + limit * 0.9;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();
    moore = compute_moore();

    read_start(&best);
    int had_start = best.n > 0;
    if (best.n == 0) complete_bipartite(&best);
    if (!is_valid(&best)) complete_bipartite(&best);

    double span = t_end - t0;
    if (best.n < moore) {
        lift_phase(t0 + span * (had_start ? 0.25 : 0.40));
        if (best.n > 0 && best.n < moore) prune_search(t0 + span * 0.70);
        if (best.n > 0 && best.n < moore) grow_search(t_end);
    }
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


def _known_start(d, D):
    """Best directly constructible graph for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)           # record family 2(q^2+q+5)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return (1, [])
    if D == 1:
        return (2, [(0, 1)])

    best = lib.haar_graph(d, range(d))   # K_{d,d}: valid for D >= 2

    try:
        start = _known_start(d, D)
    except Exception:
        start = None
    if start is not None and start[0] > best[0] and lib.is_valid(start[0], start[1], d, D):
        best = start

    if best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.5
    if budget < 1.0:
        return best

    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=best, timeout=budget + 5)
        cand = lib.parse_graph_text(text)
        if cand[0] > best[0] and lib.is_valid(cand[0], cand[1], d, D):
            best = cand
    except Exception:
        pass   # keep the valid fallback

    return best
