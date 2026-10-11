"""Unstructured annealing search for bipartite degree-diameter graphs.

Python supplies a valid start (a projective-plane or Araujo-Pardo-Lopez graph for D = 3 when one applies, otherwise K_{d,d}). The C engine has no voltage-lift phase. It grows the best graph by two vertices per step, in one of two ways, and repairs each candidate with Metropolis annealing on degree-preserving edge switches, with the number of pairs at distance > D as the cost:

  (a) grow: attach two new vertices to the current best and anneal;
  (b) scratch: start from a random bi-circulant d-regular bipartite graph of the target order and anneal.

Bipartiteness and the degree sequence are preserved by every move. Every failed attempt is discarded, so the last valid graph is always kept. C validates the output, and Python re-checks it with lib.is_valid before returning it.
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
#define MAXD 16
#define MAXW (MAXN / 64)

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static double t_end;

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static long moore(void) {
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

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];

/* Number of unordered pairs at distance > D. Zero means diameter <= D. */
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

static int read_start(Graph *g) {
    int n, m;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN || m < 0) return 0;
    g->n = n;
    for (int v = 0; v < n; v++) { g->deg[v] = 0; g->side[v] = 255; }
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= n || v >= n ||
            g->deg[u] >= MAXD || g->deg[v] >= MAXD) return 0;
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
                else if (g->side[u] == g->side[v]) return 0;
            }
        }
    }
    return is_valid(g);
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

/* Random bi-circulant d-regular bipartite graph on n vertices (n/2 >= d). */
static void scratch_bicirc(Graph *g, int n) {
    int M = n / 2;
    g->n = n;
    for (int v = 0; v < n; v++) { g->deg[v] = 0; g->side[v] = v >= M; }
    int sh[MAXD];
    int k = 0;
    while (k < d) {
        int s = rndint(M), ok = 1;
        for (int j = 0; j < k; j++)
            if (sh[j] == s) { ok = 0; break; }
        if (ok) sh[k++] = s;
    }
    for (int i = 0; i < M; i++)
        for (int j = 0; j < d; j++) add_edge(g, i, M + (i + sh[j]) % M);
}

/* Add two vertices (one per side) to best, attaching them by degree-preserving switches. */
static void grow_from(const Graph *best, Graph *w) {
    static unsigned char used[MAXN];
    *w = *best;
    int n = best->n, x = n, y = n + 1;
    w->n = n + 2;
    w->deg[x] = w->deg[y] = 0;
    w->side[x] = 0;
    w->side[y] = 1;
    add_edge(w, x, y);
    memset(used, 0, (size_t)(n + 2));
    used[x] = used[y] = 1;
    int k = 0;
    for (int tries = 0; k < d - 1 && tries < 100000; tries++) {
        int a = rndint(n);
        if (w->side[a] != 0 || used[a] || w->deg[a] == 0) continue;
        int b = w->adj[a][rndint(w->deg[a])];
        if (used[b]) continue;
        del_edge(w, a, b);
        add_edge(w, x, b);
        add_edge(w, y, a);
        used[a] = used[b] = 1;
        k++;
    }
}

/* Metropolis annealing on degree-preserving switches (a,b),(c,e) -> (a,e),(c,b).
 * Returns the final number of bad pairs (0 means success). */
static int side0[MAXN];
static long anneal(Graph *g, double until) {
    int ns0 = 0;
    for (int v = 0; v < g->n; v++)
        if (g->side[v] == 0) side0[ns0++] = v;
    long bad = bad_pairs(g);
    if (bad == 0) return 0;
    double t0 = now(), span = until - t0;
    if (span <= 0 || ns0 < 2) return bad;
    double T = 1.0;
    long it = 0;
    for (;;) {
        if ((it & 63) == 0) {
            double tn = now();
            if (tn >= until) break;
            double f = (tn - t0) / span;
            T = 1.2 * (1.0 - f) + 0.03;
        }
        it++;
        int a = side0[rndint(ns0)];
        if (g->deg[a] == 0) continue;
        int b = g->adj[a][rndint(g->deg[a])];
        int c = side0[rndint(ns0)];
        if (c == a || g->deg[c] == 0) continue;
        int e = g->adj[c][rndint(g->deg[c])];
        if (e == b || has_edge(g, a, e) || has_edge(g, c, b)) continue;
        del_edge(g, a, b);
        del_edge(g, c, e);
        add_edge(g, a, e);
        add_edge(g, c, b);
        long nb = bad_pairs(g);
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) {
            bad = nb;
            if (bad == 0) return 0;
        } else {
            del_edge(g, a, e);
            del_edge(g, c, b);
            add_edge(g, a, b);
            add_edge(g, c, e);
        }
    }
    return bad;
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
    t_end = t0 + limit * 0.95;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 1 || d > MAXD) { printf("1 0\n"); return 0; }
    if (d == 1 || D < 2) { printf("2 1\n0 1\n"); return 0; }

    static Graph best, cand;
    if (!read_start(&best)) complete_bipartite(&best);
    long mb = moore();
    int fails = 0;
    while (1) {
        double tn = now();
        if (tn >= t_end) break;
        if (best.n + 2 > mb || best.n + 2 > MAXN) break;
        double left = t_end - tn;
        double slice = 1.0 + 0.25 * fails;
        if (slice > 15.0) slice = 15.0;
        if (slice > left) slice = left;
        if (rndint(2) == 0) {
            grow_from(&best, &cand);
        } else {
            if (best.n + 2 < 2 * d) break;
            scratch_bicirc(&cand, best.n + 2);
        }
        if (anneal(&cand, tn + slice) == 0 && is_valid(&cand)) {
            best = cand;
            fails = 0;
        } else {
            fails++;
        }
    }
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


def known_start(d, D):
    """Best known construction for D = 3 that Python can build directly, or None.

    Other diameters start from K_{d,d} and rely on the C annealer.
    """
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph
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

    # Use most of the limit; keep a margin for compilation and process startup.
    budget = 0.92 * time_limit - (time.monotonic() - t0) - 1.5
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
