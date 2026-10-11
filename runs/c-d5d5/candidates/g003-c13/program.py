"""Combined program: orbit-checked voltage lifts over base multigraphs, prune-and-refill
annealing of larger lifts, and grow-by-two annealing. Python supplies the best valid start
(projective planes, Araujo-Pardo-Lopez, generalized quadrangles, K_{d,d}). Every returned graph
is checked with lib.is_valid, and the Python fallback is kept if the C output fails.
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
 * Lifts: a base d-regular bipartite multigraph on p + p vertices, with darts (i, j, g),
 *   lifted over a group G of order N (Z_m x| Z_k). Dart (i, j, g) joins A_{i,x} to
 *   B_{j, x*g}. Left multiplication is an automorphism, so a lift has diameter <= D iff a
 *   BFS of depth D from each of the 2p representatives A_{i,e}, B_{j,e} reaches everything.
 *   Search moves: change a voltage, or swap the B-targets of two darts (both keep regularity).
 * Phases: orbit hill-climb for lifts, prune-and-refill (anneal a larger lift, delete the
 *   worst vertices, refill, anneal 2-switches), and grow-by-two with edge-swap annealing.
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
#define MAXDART (MAXD * MAXP)

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN]; /* 0 = part A, 1 = part B */
} Graph;

typedef struct { int i, j, g; } Dart;

typedef struct {
    int m, k, r;
    int rp[MAXN]; /* rp[b] = r^b mod m */
} Grp;

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
static int badv[MAXN]; /* vertices farther than D from v, set by bad_pairs() */

/* Number of unordered pairs at distance > D (0 means diameter <= D). */
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

/* Z_m x|_r Z_k: element (a, b) is the int a*k + b, (a,b)(c,e) = (a + r^b c mod m, b + e mod k). */
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

/* ------------------------------------------------------------------ base multigraphs and lifts */

/* Random d-regular bipartite multigraph on p + p vertices, as a sum of d random permutation
 * matrices, retried until connected. M[i][j] = number of darts i -> j. */
static void make_base(int p, int M[MAXP][MAXP]) {
    for (;;) {
        memset(M, 0, sizeof(int) * MAXP * MAXP);
        for (int t = 0; t < d; t++) {
            int perm[MAXP];
            for (int i = 0; i < p; i++) perm[i] = i;
            for (int i = p - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int s = perm[i]; perm[i] = perm[j]; perm[j] = s;
            }
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

/* A voltage not used by another dart on the same (i, j) pair. N >= d guarantees one exists. */
static int fresh_voltage(const Dart *dt, int nd, int skip, int i, int j, int N) {
    for (;;) {
        int g = rndint(N), clash = 0;
        for (int t = 0; t < nd; t++)
            if (t != skip && dt[t].i == i && dt[t].j == j && dt[t].g == g) { clash = 1; break; }
        if (!clash) return g;
    }
}

/* Random base multigraph with darts and unique (i, j, g) triples. Returns the dart count p*d. */
static int random_darts(int p, int N, Dart *dt) {
    int M[MAXP][MAXP];
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
    return nd;
}

/* 1 if dart t duplicates the (i, j, g) triple of another dart. */
static int dup_at(const Dart *dt, int nd, int t) {
    for (int s = 0; s < nd; s++)
        if (s != t && dt[s].i == dt[t].i && dt[s].j == dt[t].j && dt[s].g == dt[t].g) return 1;
    return 0;
}

/* Build the full lift graph: A-side 0..pN-1, B-side pN..2pN-1. */
static void build_lift(Graph *g, int p, int N, const Grp *G, const Dart *dt, int nd) {
    g->n = 2 * p * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= p * N; }
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, dt[t].i * N + x, p * N + dt[t].j * N + gmul(G, x, dt[t].g));
}

/* Orbit cost: unreached vertices summed over the 2p representatives. Zero iff valid. */
static int lk_deg[MAXN];
static int lk_adj[MAXN][MAXD];
static int lk_vis[MAXN];
static int lk_dist[MAXN];
static int lk_q[MAXN];
static int lk_stamp = 0;

static long orbit_cost(int p, int N, const Grp *G, const Dart *dt, int nd) {
    int n = 2 * p * N;
    for (int v = 0; v < n; v++) lk_deg[v] = 0;
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++) {
            int a = dt[t].i * N + x;
            int b = (p + dt[t].j) * N + gmul(G, x, dt[t].g);
            lk_adj[a][lk_deg[a]++] = b;
            lk_adj[b][lk_deg[b]++] = a;
        }
    int reps[2 * MAXP], nr = 0;
    for (int i = 0; i < p; i++) reps[nr++] = i * N;
    for (int j = 0; j < p; j++) reps[nr++] = (p + j) * N;
    long total = 0;
    for (int r = 0; r < nr; r++) {
        int src = reps[r];
        lk_stamp++;
        int qh = 0, qt = 0;
        lk_q[qt++] = src;
        lk_vis[src] = lk_stamp;
        lk_dist[src] = 0;
        while (qh < qt) {
            int v = lk_q[qh++];
            if (lk_dist[v] >= D) continue;
            for (int e = 0; e < lk_deg[v]; e++) {
                int u = lk_adj[v][e];
                if (lk_vis[u] != lk_stamp) {
                    lk_vis[u] = lk_stamp;
                    lk_dist[u] = lk_dist[v] + 1;
                    lk_q[qt++] = u;
                }
            }
        }
        total += n - qt;
    }
    return total;
}

/* Hill-climb on the darts of one lift. Returns the final orbit cost (0 = valid lift). */
static long lift_climb(int p, int N, const Grp *G, Dart *dt, int nd, int steps, double until) {
    long cost = orbit_cost(p, N, G, dt, nd);
    for (int s = 0; s < steps && cost > 0; s++) {
        if ((s & 63) == 0 && now() > until) break;
        if (rndint(3) < 2) {
            int t = rndint(nd);
            int old = dt[t].g;
            dt[t].g = rndint(N);
            if (dup_at(dt, nd, t)) { dt[t].g = old; continue; }
            long c2 = orbit_cost(p, N, G, dt, nd);
            if (c2 <= cost || rnd01() < 0.01) cost = c2;
            else dt[t].g = old;
        } else {
            int t1 = rndint(nd), t2 = rndint(nd);
            if (t1 == t2 || dt[t1].j == dt[t2].j) continue;
            int tmp = dt[t1].j;
            dt[t1].j = dt[t2].j;
            dt[t2].j = tmp;
            if (dup_at(dt, nd, t1) || dup_at(dt, nd, t2)) {
                tmp = dt[t1].j; dt[t1].j = dt[t2].j; dt[t2].j = tmp;
                continue;
            }
            long c2 = orbit_cost(p, N, G, dt, nd);
            if (c2 <= cost || rnd01() < 0.01) cost = c2;
            else {
                tmp = dt[t1].j; dt[t1].j = dt[t2].j; dt[t2].j = tmp;
            }
        }
    }
    return cost;
}

/* Orbit-checked lift search. Each success is a valid graph larger than best. */
static void lift_search(Graph *best, double until) {
    static Dart dt[MAXDART];
    static Grp G;
    static Graph cand;
    long moore = moore_bound();
    while (now() < until) {
        if (best->n + 2 > moore) return;
        int p = 1 + rndint(MAXP);
        long target = best->n + 2;
        int N = (int)((target + 2L * p - 1) / (2L * p)) + rndint(3);
        if (N < d) N = d;
        if (2L * p * N > moore || 2L * p * N > MAXN) continue;
        if (!random_group(N, &G)) continue;
        int nd = random_darts(p, N, dt);
        long cost = lift_climb(p, N, &G, dt, nd, 2000, until);
        if (cost == 0) {
            build_lift(&cand, p, N, &G, dt, nd);
            if (cand.n > best->n && is_valid(&cand)) copy_graph(best, &cand);
        }
    }
}

/* Anneal the darts of a random lift to minimise full bad-pair count (need not reach zero).
 * Leaves g = the lift with the final darts; returns its bad-pair count. */
static long lift_anneal(Graph *g, int p, int N, const Grp *G, int steps) {
    Dart dt[MAXDART];
    int nd = random_darts(p, N, dt);
    build_lift(g, p, N, G, dt, nd);
    long bad = bad_pairs(g);
    for (int s = 0; s < steps && bad > 0; s++) {
        if ((s & 15) == 0 && now() > t_end) break;
        int t = rndint(nd);
        int old = dt[t].g;
        dt[t].g = fresh_voltage(dt, nd, t, dt[t].i, dt[t].j, N);
        build_lift(g, p, N, G, dt, nd);
        long nb = bad_pairs(g);
        if (nb <= bad || rnd01() < 0.02) bad = nb;
        else dt[t].g = old;
    }
    build_lift(g, p, N, G, dt, nd);
    return bad_pairs(g);
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

/* One degree-preserving 2-switch (v-u, s-t) -> (v-t, s-u), v and s on the same side.
 * Metropolis acceptance on the bad-pair count. */
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
    int best = -1;
    long bv = -1;
    int ties = 0;
    for (int v = 0; v < g->n; v++) {
        if (g->side[v] != side) continue;
        if ((long)badv[v] > bv) { bv = badv[v]; best = v; ties = 1; }
        else if ((long)badv[v] == bv) { ties++; if (rndint(ties) == 0) best = v; }
    }
    return best;
}

/* Start from a near-valid graph bigger than best. Repeat: refill, anneal 2-switches,
 * then delete one worst vertex per side. A valid result bigger than best replaces best. */
static void prune_round(const Graph *start, Graph *best, double until) {
    static Graph w;
    copy_graph(&w, start);
    long bad = bad_pairs(&w);
    while (bad > 0 && now() < until && w.n - 2 > best->n) {
        fill_pass(&w);
        bad = bad_pairs(&w);
        if (bad == 0) break;
        for (int it = 0; it < 300 && bad > 0; it++) switch_move(&w, &bad, 0.6);
        if (bad == 0) break;
        bad = bad_pairs(&w); /* refresh badv */
        int a = worst_on(&w, 0), b = worst_on(&w, 1);
        if (a < 0 || b < 0 || a == b) break;
        int hi = a > b ? a : b, lo = a > b ? b : a;
        remove_vertex(&w, hi);
        remove_vertex(&w, lo);
        bad = bad_pairs(&w);
    }
    fill_pass(&w);
    bad = bad_pairs(&w);
    if (bad == 0 && w.n > best->n && is_valid(&w)) copy_graph(best, &w);
}

static void prune_search(Graph *best, double until) {
    static Graph cand;
    static Grp G;
    long moore = moore_bound();
    if (best->n == 0) return;
    int fails = 0;
    while (now() < until) {
        int r = rndint(10);
        int p = r < 3 ? 1 : r < 6 ? 2 : r < 9 ? 3 : 4;
        int extra = 2 * (2 + rndint(6)); /* 4..14 extra vertices before pruning */
        long target = (long)best->n + extra;
        int N = (int)((target + 2 * p - 1) / (2 * p));
        if (N < d) N = d;
        if (2L * p * N > (long)best->n + 40 || 2L * p * N > MAXN || 2L * p * N > moore) {
            if (++fails > 1000) return;
            continue;
        }
        if (!random_group(N, &G)) continue;
        int steps = 300 + 200000 / (2 * p * N);
        lift_anneal(&cand, p, N, &G, steps);
        prune_round(&cand, best, until);
    }
}

/* ------------------------------------------------------------------ grow by two */

/* Insert one vertex per side (degree d each) into a copy of best, then anneal edge swaps.
 * Returns 1 if the result is valid with best->n + 2 vertices. */
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
    double t0 = now();
    t_end = t0 + limit * 0.92;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best;
    if (d < 1 || d > MAXD || D < 1) {
        best.n = 1;
        best.deg[0] = 0;
        best.side[0] = 0;
        print_graph(&best);
        return 0;
    }
    if (D == 1) {
        best.n = 2;
        best.deg[0] = best.deg[1] = 0;
        best.side[0] = 0;
        best.side[1] = 1;
        add_edge(&best, 0, 1);
        print_graph(&best);
        return 0;
    }

    read_start(&best);
    int had_start = best.n > 0;
    if (best.n == 0) complete_bipartite(&best);

    long moore = moore_bound();
    if (best.n < moore) {
        double span = t_end - t0;
        (void)had_start;
        lift_search(&best, t0 + span * 0.40);
        if (best.n < moore) prune_search(&best, t0 + span * 0.70);
        if (best.n + 2 <= moore) lift_search(&best, t0 + span * 0.80);
        if (best.n + 2 <= moore) grow_search(&best, t_end);
    }
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python constructions: valid starting points. The C engine only improves them.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo_lopez(d):
    """Araujo-Pardo and Lopez record family for d = q + 2, q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        return lib.araujo_lopez_graph(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
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
    """W(q) for the largest prime power q with q + 1 <= d, capped at q = 5 for speed."""
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _candidates(d, D):
    """Valid constructions for (d, D). Each builder is guarded so one failure cannot break the rest."""
    builders = []
    if D >= 3:
        builders.append(lambda: _best_pg(d))
        builders.append(lambda: _araujo_lopez(d))
    if D >= 4:
        builders.append(lambda: _best_gq(d))
    out = []
    for b in builders:
        try:
            r = b()
        except Exception:
            r = None
        if r is not None:
            out.append(r)
    return out


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d} has diameter 2, so it is valid for D >= 2 and serves as the fallback.
    best = lib.haar_graph(d, range(d))
    for n, e in _candidates(d, D):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if best[0] >= lib.moore_bound(d, D):
        budget = min(budget, 0.5)   # nothing beats a Moore graph; just exercise the engine

    if budget > 0.5:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             stdin_graph=best, timeout=budget + 5)
            n, e = lib.parse_graph_text(text)
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
        except (RuntimeError, ValueError):
            pass   # keep the valid Python-built fallback

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
