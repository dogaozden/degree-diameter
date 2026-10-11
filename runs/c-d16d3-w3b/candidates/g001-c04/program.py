"""Starter program: Python builds the best known start graph, the C engine searches from it.

Changed approach for D = 3: instead of voltage lifts, the C engine grows the start graph
(Araujo-Pardo-Lopez or projective-plane incidence, whichever is largest for this d) two vertices
at a time. New vertices fill their degree from spare slots and degree-preserving swaps, then
simulated annealing on bad-pair counts repairs distances. build() always returns a valid graph.
"""
import time

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search core, growth variant.
 *
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v": a valid start graph, or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * Method: repeatedly add one vertex x on side A and one vertex y on side B, joined by an
 * edge. x and y are filled to degree d using spare slots of old vertices, and when there are
 * none, by swapping an old edge (a,b) into (x,b),(y,a). Then simulated annealing on
 * degree-preserving double edge swaps drives the number of pairs farther than D apart to 0.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 2048
#define MAXD 32
#define MAXW (MAXN / 64)

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN]; /* 0 = part A, 1 = part B */
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
static int badv[MAXN]; /* badv[v] = number of vertices farther than D from v (last computed) */

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

/* K_{d,d}: valid for D >= 2. */
static void complete_bipartite(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= d; }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

/* ------------------------------------------------------------------ growth step */

/* x (side 0) and y (side 1) are new, joined by an edge, and all old vertices are indices < n_old.
 * Give both degree d: first from spare slots of old vertices, then by swapping an old edge
 * (a,b) into (x,b),(y,a). Returns 1 on success. */
static int fill_new(Graph *g, int x, int y, int n_old) {
    static int cand[MAXN];
    for (int guard = 0; guard < 100000; guard++) {
        int dx = d - g->deg[x], dy = d - g->deg[y];
        if (dx == 0 && dy == 0) return 1;
        if (dx > 0) {
            int c = 0;
            for (int b = 0; b < n_old; b++)
                if (g->side[b] == 1 && g->deg[b] < d && !has_edge(g, x, b)) cand[c++] = b;
            if (c > 0) { add_edge(g, x, cand[rndint(c)]); continue; }
        }
        if (dy > 0) {
            int c = 0;
            for (int a = 0; a < n_old; a++)
                if (g->side[a] == 0 && g->deg[a] < d && !has_edge(g, y, a)) cand[c++] = a;
            if (c > 0) { add_edge(g, y, cand[rndint(c)]); continue; }
        }
        if (dx > 0 && dy > 0) {
            int done = 0;
            for (int tries = 0; tries < 10000 && !done; tries++) {
                int a = rndint(n_old);
                if (g->side[a] != 0 || g->deg[a] == 0) continue;
                int b = g->adj[a][rndint(g->deg[a])];
                if (b >= n_old) continue;
                if (has_edge(g, x, b) || has_edge(g, y, a)) continue;
                del_edge(g, a, b);
                add_edge(g, x, b);
                add_edge(g, y, a);
                done = 1;
            }
            if (!done) return 0;
            continue;
        }
        return 0;
    }
    return 0;
}

/* Simulated annealing on degree-preserving bipartite double edge swaps, guided by bad pairs.
 * Returns 1 when bad pairs reach 0 before `until`. */
static int anneal(Graph *g, double until) {
    long bad = bad_pairs(g);
    double T = 1.0;
    long it = 0;
    while (bad > 0) {
        if ((++it & 15) == 0 && now() > until) return 0;
        int v = rndint(g->n);
        for (int tries = 0; tries < 30 && badv[v] == 0; tries++) v = rndint(g->n);
        if (g->deg[v] == 0) continue;
        int side = g->side[v];
        int u = g->adj[v][rndint(g->deg[v])];
        int s = rndint(g->n);
        if (s == v || g->side[s] != side || g->deg[s] == 0) continue;
        int t = g->adj[s][rndint(g->deg[s])];
        if (t == u || has_edge(g, v, t) || has_edge(g, s, u)) continue;
        del_edge(g, v, u);
        del_edge(g, s, t);
        add_edge(g, v, t);
        add_edge(g, s, u);
        long nb = bad_pairs(g);
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) {
            bad = nb;
        } else {
            del_edge(g, v, t);
            del_edge(g, s, u);
            add_edge(g, v, u);
            add_edge(g, s, t);
        }
        T *= 0.9995;
        if (T < 0.05) T = 1.0;
    }
    return 1;
}

/* Try to grow best by two vertices. Returns 1 and fills work with a valid graph on n+2 vertices. */
static int grow_once(const Graph *best, Graph *work, double until) {
    int n = best->n;
    if (n + 2 > moore_bound() || n + 2 > MAXN) return 0;
    copy_graph(work, best);
    int x = n, y = n + 1;
    work->n = n + 2;
    work->deg[x] = 0;
    work->deg[y] = 0;
    work->side[x] = 0;
    work->side[y] = 1;
    add_edge(work, x, y);
    if (!fill_new(work, x, y, n)) return 0;
    if (!anneal(work, until)) return 0;
    return is_valid(work);
}

static void grow_search(Graph *best, double until) {
    static Graph work;
    while (now() < until && best->n + 2 <= moore_bound()) {
        double left = until - now();
        double slice = left / 3.0;
        if (slice < 3.0) slice = left;
        if (slice > left) slice = left;
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
    if (d < 1 || d > MAXD - 2 || D < 1) {
        printf("0 0\n");
        return 0;
    }
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.2;
    if (t_end < t0) t_end = t0;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best;
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (D >= 2 && best.n + 2 <= moore_bound()) grow_search(&best, t_end);
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


def _d3_starts(d):
    """Known D = 3 constructions with max degree <= d, largest order first: (n, kind, q)."""
    opts = []
    for q in range(2, d + 1):
        if not lib.is_prime_power(q):
            continue
        if q + 1 <= d:
            opts.append((2 * (q * q + q + 1), "pg", q))
        if q >= 3 and q + 2 <= d:
            opts.append((2 * (q * q + q + 5), "af", q))
    opts.sort(reverse=True)
    return opts


def known_start(d, D):
    """Largest verified known construction for (d, D), as (n, edges), or None."""
    if D != 3:
        return None
    for n, kind, q in _d3_starts(d):
        try:
            g = lib.projective_plane_incidence(q) if kind == "pg" else lib.araujo_lopez_graph(q)
        except Exception:
            continue
        if g[0] == n and lib.is_valid(g[0], g[1], d, D):
            return g
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    try:
        best = known_start(d, D)
    except Exception:
        best = None
    if best is None:
        best = lib.haar_graph(d, range(d))   # K_{d,d}: valid for D >= 2

    if best[0] >= lib.moore_bound(d, D) or d > MAXD_PY or D < 2:
        return best   # a Moore graph cannot be beaten; skip the search

    budget = 0.8 * time_limit - (time.monotonic() - t0) - 2.0
    if budget < 1.0:
        return best

    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=best, timeout=budget + 8.0)
        n, edges = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)
    except Exception:
        pass   # keep the valid start graph
    return best


MAXD_PY = 30
