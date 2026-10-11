"""Scratch-annealing growth for the d5D5 target: a different construction from the lift parent.

The parent builds a semidirect-product voltage lift and then grows it by two. This version drops
the group structure entirely. For each candidate order 2N it starts from a circulant d-regular
bipartite graph (A_a adjacent to B_{a+s}, s = 0..d-1), randomises it with degree-preserving edge
swaps, and anneals those swaps against the number of vertex pairs at distance > D. A success
at order 2N becomes the new best, and the search moves on to 2N+2. Every swap keeps the graph
d-regular and bipartite, so only the diameter needs repair.

Risk: unstructured annealing is unlikely to reach the 352-vertex lift result within 60 s, so this
variant may score below the parent on d5D5. Fallbacks are kept: the start graph (K_{d,d}, or a known
D=3/D=4 construction) is always returned if no larger valid graph is found. Every output is
checked in C and again in Python with lib.is_valid.
"""
import time

import lib

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 1024
#define MAXD 32
#define MAXW (MAXN / 64)

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

/* ---------------------------------------------------------- adjacency */

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

/* ---------------------------------------------------------- distance */

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];

/* Number of unordered vertex pairs at distance > D. */
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

/* ---------------------------------------------------------- I/O */

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

static void complete_bipartite(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= d; }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

/* ---------------------------------------------------------- scratch annealing */

/* d-regular circulant bipartite graph with N vertices per side (needs N >= d). */
static void circulant(Graph *g, int N) {
    g->n = 2 * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= N; }
    for (int a = 0; a < N; a++)
        for (int s = 0; s < d; s++) add_edge(g, a, N + (a + s) % N);
}

/* Degree-preserving swap proposal: edges (a,b), (c,e) become (a,e), (c,b). */
static int propose(const Graph *g, int N, int *a, int *b, int *c, int *e) {
    int x = rndint(N), y = rndint(N);
    if (x == y || g->deg[x] == 0 || g->deg[y] == 0) return 0;
    int bb = g->adj[x][rndint(g->deg[x])];
    int ee = g->adj[y][rndint(g->deg[y])];
    if (bb == ee || has_edge(g, x, ee) || has_edge(g, y, bb)) return 0;
    *a = x; *b = bb; *c = y; *e = ee;
    return 1;
}

static void apply_swap(Graph *g, int a, int b, int c, int e) {
    del_edge(g, a, b);
    del_edge(g, c, e);
    add_edge(g, a, e);
    add_edge(g, c, b);
}

static void undo_swap(Graph *g, int a, int b, int c, int e) {
    del_edge(g, a, e);
    del_edge(g, c, b);
    add_edge(g, a, b);
    add_edge(g, c, e);
}

static Graph W;

/* Anneal a random-swap randomisation of the circulant until diameter <= D or time runs out. */
static int anneal(Graph *out, int N, double until) {
    circulant(&W, N);
    for (long k = 0, lim = 10L * N * d; k < lim; k++) {
        int a, b, c, e;
        if (propose(&W, N, &a, &b, &c, &e)) apply_swap(&W, a, b, c, e);
    }
    long cost = bad_pairs(&W);
    double t_start = now();
    double span = until - t_start;
    if (span <= 0) return 0;
    double frac = 0.0, T = 0.6;
    long it = 0;
    while (cost > 0) {
        if ((++it & 63) == 0) {
            double tn = now();
            if (tn > until) return 0;
            frac = (tn - t_start) / span;
            T = 0.6 * (1.0 - frac) + 0.03;
        }
        int a, b, c, e;
        if (!propose(&W, N, &a, &b, &c, &e)) continue;
        apply_swap(&W, a, b, c, e);
        long nc = bad_pairs(&W);
        if (nc <= cost || rnd01() < exp(-(double)(nc - cost) / T)) cost = nc;
        else undo_swap(&W, a, b, c, e);
    }
    copy_graph(out, &W);
    return 1;
}

/* ---------------------------------------------------------- main */

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

    static Graph best, cand;
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);

    long moore = moore_bound();
    while (1) {
        int N = best.n / 2 + 1;
        if (N < d) N = d;
        if (2L * N > moore || 2 * N > MAXN) break;
        double tn = now();
        double remain = t_end - tn;
        if (remain < 0.2) break;
        if (!anneal(&cand, N, tn + remain * 0.6)) break;
        if (cand.n > best.n && is_valid(&cand)) copy_graph(&best, &cand);
        else break;
    }

    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


def known_start(d, D):
    """Best known construction Python can build directly for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)
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

    budget = 0.9 * time_limit - (time.monotonic() - t0) - 1.5
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
