"""Spare-slot growth program (v3).

Idea: a PG(2, q) incidence graph with q = d-2 is (d-1)-regular, so every vertex has one
spare degree slot. A new pair (x, y) of vertices is attached to spare slots of the old
graph, each new edge chosen greedily to minimise the number of bad pairs. A tabu walk of
degree-preserving 2-switches repairs whatever is left. Only if that fails does the tabu
growth (degree-stealing) phase run.

Python builds the start graphs (PG(2, d-2) with spare slots, then the Araujo-Lopez graph
as fallback). C does the search. build() always returns a graph that passed lib.is_valid.
"""
import time

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search core, v3.
 *
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v": a valid starting graph, or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * Phases:
 *   1. Lift search over semidirect groups (only when no start graph is given).
 *   2. Spare-slot growth: add a pair (x, y) joined by an edge. Fill x's free degree
 *      with spare vertices of the other side, one edge at a time, each time taking
 *      the sampled candidate that minimises bad pairs. If bad pairs remain, repair
 *      with a tabu walk of degree-preserving 2-switches.
 *   3. Tabu growth: steal edges to give a new pair full degree, then repair.
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
#define CAND 40
#define TENURE 7
#define SAMP 150

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN]; /* 0 = part A, 1 = part B */
} Graph;

typedef struct { int v, u, s, t; } Move; /* remove v-u and s-t, add v-t and s-u */

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
static int badv[MAXN]; /* vertices farther than D from v, after the last bad_pairs() */

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

/* Full validity check: simple, bipartite (by side labels), degree <= d, diameter <= D. */
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

/* Read "n m" + edges from stdin; 2-colour it. Leaves g->n = 0 if absent or invalid. */
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
    int rp[MAXN]; /* rp[b] = r^b mod m */
} Grp;

static int gmul(const Grp *G, int x, int y) {
    int a = x / G->k, b = x % G->k, c = y / G->k, e = y % G->k;
    return (int)((a + (long)G->rp[b] * c) % G->m) * G->k + (b + e) % G->k;
}

/* Pick a uniformly random (m, k, r) with m*k = N, gcd(r, m) = 1 and r^k = 1 mod m. */
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

typedef struct { int i, j, g; } Dart; /* base A-vertex i -> base B-vertex j, voltage g */

/* Random d-regular bipartite base multigraph with p vertices per side, retried until connected. */
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

/* A voltage not used by any other dart between the same pair of base vertices. */
static int fresh_voltage(const Dart *dt, int nd, int skip, int i, int j, int N) {
    for (;;) {
        int g = rndint(N), clash = 0;
        for (int t = 0; t < nd; t++)
            if (t != skip && dt[t].i == i && dt[t].j == j && dt[t].g == g) { clash = 1; break; }
        if (!clash) return g;
    }
}

/* One hill-climb over the voltages of a random base graph and group of order N. */
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
    return 1; /* g was built from the accepted voltages */
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

/* ------------------------------------------------------------------ 2-switch moves */

static void apply_move(Graph *g, const Move *m) {
    del_edge(g, m->v, m->u);
    del_edge(g, m->s, m->t);
    add_edge(g, m->v, m->t);
    add_edge(g, m->s, m->u);
}

static void undo_move(Graph *g, const Move *m) {
    del_edge(g, m->v, m->t);
    del_edge(g, m->s, m->u);
    add_edge(g, m->v, m->u);
    add_edge(g, m->s, m->t);
}

/* Random degree-preserving 2-switch that keeps the bipartition, with v taken from L. */
static int sample_move(const Graph *g, const int *L, int nl, Move *mv) {
    int v = L[rndint(nl)];
    if (g->deg[v] == 0) return 0;
    int u = g->adj[v][rndint(g->deg[v])];
    for (int tries = 0; tries < 50; tries++) {
        int s = rndint(g->n);
        if (s == v || g->side[s] != g->side[v] || g->deg[s] == 0) continue;
        int t = g->adj[s][rndint(g->deg[s])];
        if (t == u || has_edge(g, v, t) || has_edge(g, s, u)) return 0;
        mv->v = v; mv->u = u; mv->s = s; mv->t = t;
        return 1;
    }
    return 0;
}

/* Tabu walk of degree-preserving 2-switches until bad pairs vanish (returns 1) or time runs out. */
static int tabu_repair(Graph *work, double until) {
    static int L[MAXN];
    static long tabu_exp[MAXN];
    long it = 0;
    memset(tabu_exp, 0, sizeof(long) * (size_t)work->n);
    for (;;) {
        if (now() > until) return 0;
        long cur = bad_pairs(work); /* also refreshes badv */
        if (cur == 0) return 1;
        it++;
        int nl = 0;
        for (int v = 0; v < work->n; v++)
            if (badv[v] > 0) L[nl++] = v;
        if (nl == 0) return 0;

        long best_nb = 1L << 60;
        Move bm;
        int found = 0;
        for (int c = 0; c < CAND; c++) {
            Move mv;
            if (!sample_move(work, L, nl, &mv)) continue;
            apply_move(work, &mv);
            long nb = bad_pairs(work);
            undo_move(work, &mv);
            int tabu = tabu_exp[mv.v] > it || tabu_exp[mv.s] > it;
            if (tabu && nb >= cur) continue; /* aspiration: tabu moves only if they improve */
            if (nb < best_nb || (nb == best_nb && rnd01() < 0.5)) {
                best_nb = nb;
                bm = mv;
                found = 1;
            }
        }
        if (!found) continue;
        apply_move(work, &bm);
        tabu_exp[bm.v] = it + TENURE;
        tabu_exp[bm.s] = it + TENURE;
    }
}

/* ------------------------------------------------------------------ tabu growth */

/* Build best + two new vertices (one per side) with stolen edges, then repair. */
static int tabu_attempt(const Graph *best, Graph *work, double until) {
    static int used[MAXN];
    static int stamp = 0;
    int n = best->n;

    copy_graph(work, best);
    int x = n, y = n + 1;
    work->n = n + 2;
    work->deg[x] = work->deg[y] = 0;
    work->side[x] = 0;
    work->side[y] = 1;
    add_edge(work, x, y);
    stamp++;
    used[x] = used[y] = stamp;
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
    if (!tabu_repair(work, until)) return 0;
    return is_valid(work);
}

static void tabu_grow(Graph *best, double until) {
    static Graph work;
    while (now() < until && best->n + 2 <= moore_bound() && best->n + 2 <= MAXN) {
        double left = until - now();
        double slice = left / 3 > 3.0 ? left / 3 : left;
        if (tabu_attempt(best, &work, now() + slice)) copy_graph(best, &work);
    }
}

/* ------------------------------------------------------------------ spare-slot growth */

/* Vertices on `side` that have spare degree, excluding x and anything adjacent to x. */
static int collect_spare(const Graph *g, int side, int x, int *out) {
    int c = 0;
    for (int v = 0; v < g->n; v++) {
        if (v == x || g->side[v] != side || g->deg[v] >= d) continue;
        if (has_edge(g, x, v)) continue;
        out[c++] = v;
    }
    return c;
}

/* Give x edges to spare vertices of `side` until x has degree d (or no spares remain).
 * Each step takes the sampled candidate that minimises the number of bad pairs. */
static void greedy_fill(Graph *g, int x, int side) {
    static int cand[MAXN];
    while (g->deg[x] < d) {
        int c = collect_spare(g, side, x, cand);
        if (c == 0) return;
        int tries = c < SAMP ? c : SAMP;
        int pick = -1;
        long best_nb = 1L << 60;
        for (int t = 0; t < tries; t++) {
            int v = c <= SAMP ? cand[t] : cand[rndint(c)];
            add_edge(g, x, v);
            long nb = bad_pairs(g);
            del_edge(g, x, v);
            if (nb < best_nb || (nb == best_nb && rnd01() < 0.5)) {
                best_nb = nb;
                pick = v;
            }
        }
        add_edge(g, x, pick);
    }
}

/* Add one pair (x, y) on spare slots of best, then repair. On success work is valid with n+2 vertices. */
static int spare_pair_attempt(const Graph *best, Graph *work, double until) {
    copy_graph(work, best);
    int x = best->n, y = best->n + 1;
    work->n = best->n + 2;
    work->deg[x] = work->deg[y] = 0;
    work->side[x] = 0;
    work->side[y] = 1;
    add_edge(work, x, y);
    greedy_fill(work, x, 1);
    greedy_fill(work, y, 0);
    if (bad_pairs(work) == 0) return is_valid(work);
    return tabu_repair(work, until) && is_valid(work);
}

static void spare_grow(Graph *best, double until) {
    static Graph work;
    while (now() < until && best->n + 2 <= moore_bound() && best->n + 2 <= MAXN) {
        int sA = 0, sB = 0;
        for (int v = 0; v < best->n; v++)
            if (best->deg[v] < d) {
                if (best->side[v] == 0) sA++;
                else sB++;
            }
        if (sA < d - 1 || sB < d - 1) return; /* not enough spare slots for a new pair */
        double left = until - now();
        double slice = left / 2 > 2.0 ? left / 2 : left;
        if (spare_pair_attempt(best, &work, now() + slice)) copy_graph(best, &work);
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
    if (d < 1 || D < 1 || d > MAXD) { complete_bipartite(&best); print_graph(&best); return 0; }
    read_start(&best);
    int had_start = best.n > 0;

    if (D >= 2 && best.n < moore_bound()) {
        if (!had_start) lift_search(&best, t0 + (t_end - t0) * 0.5);
        if (best.n > 0) {
            spare_grow(&best, now() + (t_end - now()) * 0.6);
            tabu_grow(&best, t_end);
        }
    }
    if (best.n == 0) complete_bipartite(&best);
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


def known_starts(d, D):
    """Start graphs for (d, D) as (name, graph) pairs, best-known first.

    'moore' is optimal and needs no search. 'spare' is PG(2, d-2): every vertex has one
    free degree slot, which spare-slot growth uses. 'araujo' is the record graph, which has
    no free slots, so it serves as a fallback.
    """
    out = []
    if D == 3 and lib.is_prime_power(d - 1):
        out.append(("moore", lib.projective_plane_incidence(d - 1)))
    if D == 3 and d - 2 >= 2 and lib.is_prime_power(d - 2):
        out.append(("spare", lib.projective_plane_incidence(d - 2)))
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        out.append(("araujo", lib.araujo_lopez_graph(d - 2)))
    return out


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    best = lib.haar_graph(d, range(d))  # K_{d,d}: valid for D >= 2

    def consider(g):
        nonlocal best
        if g is not None and g[0] > best[0] and lib.is_valid(g[0], g[1], d, D):
            best = g

    try:
        starts = known_starts(d, D)
    except Exception:
        starts = []
    for _, g in starts:
        consider(g)
    if best[0] >= lib.moore_bound(d, D):
        return best  # a Moore graph is optimal; nothing to search for

    jobs = [(name, g) for name, g in starts if name != "moore"]
    if not jobs:
        jobs = [("none", None)]
    for i, (name, g) in enumerate(jobs):
        left = 0.85 * time_limit - (time.monotonic() - t0) - 1.5
        if left < 1.0:
            break
        share = left * 0.8 if (i == 0 and len(jobs) > 1) else left
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed + 7919 * i, round(share, 2)],
                             stdin_graph=g, timeout=share + 5)
            consider(lib.parse_graph_text(text))
        except Exception:
            pass  # keep the best valid graph so far
    return best
