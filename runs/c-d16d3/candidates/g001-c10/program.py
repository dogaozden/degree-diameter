"""Bold variant: fixed-target annealing that adds vertices one at a time to a Moore-like start.

Instead of voltage lifts plus delete-and-reinsert growth, the C engine keeps a graph that
may have spare degree, adds one vertex, and anneals with edge add / shift / swap moves
(all degree-preserving or degree-reducing, so every intermediate graph respects deg <= d)
until the diameter is at most D again. Each success is saved as the new best. The best
valid graph is always kept as the fallback.
"""
import time

import lib

C_SOURCE = r'''
/* Degree-diameter annealer for bipartite graphs.
 *
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v": a valid start graph, or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *          If nothing valid can be produced, prints "0 0".
 *
 * Loop: add one vertex on the smaller side; anneal moves until the graph has diameter <= D:
 *   type 0  add edge (a in A, b in B) between two vertices with spare degree
 *   type 1  move one end of an edge (a,b) -> (a,e) where e has spare degree
 *   type 2  swap (a,b),(c,e) -> (a,e),(c,b)
 * Cost = number of unordered pairs farther than D apart. Every state keeps deg <= d
 * and bipartiteness, so the last accepted state is always a valid graph.
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

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN]; /* 0 = part A, 1 = part B */
} Graph;

typedef struct { int type, a, b, c, e; } Move;

static int d, D;
static double t_end;
static uint64_t rng_state = 88172645463325252ULL;
static Graph best, cur;
static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];

/* ------------------------------------------------------------------ utilities */

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

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

/* Number of unordered pairs at distance > D. Zero means diameter <= D (and connected). */
static long bad_pairs(const Graph *g) {
    int n = g->n, W = (n + 63) / 64;
    uint64_t *cur_r = RA, *nxt = RB;
    memset(cur_r, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++) cur_r[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            const uint64_t *src = cur_r + (size_t)v * W;
            for (int w = 0; w < W; w++) dst[w] = src[w];
            for (int i = 0; i < g->deg[v]; i++) {
                const uint64_t *s = cur_r + (size_t)g->adj[v][i] * W;
                for (int w = 0; w < W; w++) dst[w] |= s[w];
            }
        }
        uint64_t *t = cur_r;
        cur_r = nxt;
        nxt = t;
    }
    long total = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        const uint64_t *s = cur_r + (size_t)v * W;
        for (int w = 0; w < W; w++) c += __builtin_popcountll(s[w]);
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
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= n || v >= n || u == v ||
            g->deg[u] >= d || g->deg[v] >= d || has_edge(g, u, v)) {
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
                if (g->side[u] == 255) {
                    g->side[u] = 1 - g->side[v];
                    queue[tail++] = u;
                } else if (g->side[u] == g->side[v]) {
                    g->n = 0;
                    return;
                }
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

/* ------------------------------------------------------------------ moves */

/* Pick a random move that keeps all degrees <= d and sides bipartite. */
static int propose(const Graph *g, const int *LA, int nA, const int *DA, int ndA,
                   const int *LB, int nB, const int *DB, int ndB, Move *mv) {
    (void)LB;
    int r = rndint(100);
    if (r < 40) { /* add edge between two vertices with spare degree */
        if (ndA == 0 || ndB == 0) return 0;
        int a = DA[rndint(ndA)], b = DB[rndint(ndB)];
        if (has_edge(g, a, b)) return 0;
        mv->type = 0; mv->a = a; mv->b = b;
        return 1;
    }
    if (r < 60) { /* move one end of (a,b) to a spare-degree B vertex e */
        if (ndB == 0) return 0;
        int a = LA[rndint(nA)];
        if (g->deg[a] == 0) return 0;
        int b = g->adj[a][rndint(g->deg[a])];
        int e = DB[rndint(ndB)];
        if (e == b || has_edge(g, a, e)) return 0;
        mv->type = 1; mv->a = a; mv->b = b; mv->e = e;
        return 1;
    }
    /* swap (a,b),(c,e) -> (a,e),(c,b) */
    int a = LA[rndint(nA)], c = LA[rndint(nA)];
    if (a == c || g->deg[a] == 0 || g->deg[c] == 0) return 0;
    int b = g->adj[a][rndint(g->deg[a])];
    int e = g->adj[c][rndint(g->deg[c])];
    if (b == e || has_edge(g, a, e) || has_edge(g, c, b)) return 0;
    mv->type = 2; mv->a = a; mv->b = b; mv->c = c; mv->e = e;
    return 1;
}

static void apply_move(Graph *g, const Move *m) {
    switch (m->type) {
    case 0:
        add_edge(g, m->a, m->b);
        break;
    case 1:
        del_edge(g, m->a, m->b);
        add_edge(g, m->a, m->e);
        break;
    default:
        del_edge(g, m->a, m->b);
        del_edge(g, m->c, m->e);
        add_edge(g, m->a, m->e);
        add_edge(g, m->c, m->b);
        break;
    }
}

static void undo_move(Graph *g, const Move *m) {
    switch (m->type) {
    case 0:
        del_edge(g, m->a, m->b);
        break;
    case 1:
        del_edge(g, m->a, m->e);
        add_edge(g, m->a, m->b);
        break;
    default:
        del_edge(g, m->a, m->e);
        del_edge(g, m->c, m->b);
        add_edge(g, m->a, m->b);
        add_edge(g, m->c, m->e);
        break;
    }
}

/* ------------------------------------------------------------------ annealing */

/* Anneal g until its diameter is <= D. Returns 1 on success (g valid), 0 at deadline. */
static int anneal_to_valid(Graph *g, double until) {
    static int LA[MAXN], LB[MAXN], DA[MAXN], DB[MAXN];
    long bad = bad_pairs(g);
    double T = 1.0;
    while (bad > 0) {
        if (now() > until) return 0;
        int nA = 0, nB = 0, ndA = 0, ndB = 0;
        for (int v = 0; v < g->n; v++) {
            if (g->side[v] == 0) {
                LA[nA++] = v;
                if (g->deg[v] < d) DA[ndA++] = v;
            } else {
                LB[nB++] = v;
                if (g->deg[v] < d) DB[ndB++] = v;
            }
        }
        if (nA == 0 || nB == 0) return 0;
        Move mv;
        if (!propose(g, LA, nA, DA, ndA, LB, nB, DB, ndB, &mv)) continue;
        apply_move(g, &mv);
        long nbad = bad_pairs(g);
        if (nbad <= bad || rnd01() < exp((double)(bad - nbad) / T)) {
            bad = nbad;
        } else {
            undo_move(g, &mv);
        }
        T *= 0.9995;
        if (T < 0.03) T = 1.0;
    }
    return 1;
}

/* Repeatedly add one vertex (on the smaller side) and anneal back to diameter D. */
static void grow_search(double until) {
    long moore = moore_bound();
    copy_graph(&cur, &best);
    while (now() < until) {
        int n = cur.n;
        if (n + 1 > MAXN || (long)(n + 1) > moore) break;
        int ca = 0;
        for (int v = 0; v < n; v++)
            if (cur.side[v] == 0) ca++;
        unsigned char s = (ca * 2 <= n) ? 0 : 1;
        cur.n = n + 1;
        cur.deg[n] = 0;
        cur.side[n] = s;
        if (!anneal_to_valid(&cur, until)) break;
        copy_graph(&best, &cur);
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
    double t0 = now();
    t_end = t0 + limit * 0.92;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (!is_valid(&best)) {
        printf("0 0\n");
        return 0;
    }
    grow_search(t_end);
    if (!is_valid(&best)) {
        printf("0 0\n");
        return 0;
    }
    print_graph(&best);
    return 0;
}
'''


def known_start(d, D):
    """Best algebraic start for (d, D) that Python can build directly, or None."""
    if D != 3 or d < 3:
        return None
    if lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)      # Moore graph: optimal
    if d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)              # record family, order 2(q^2+q+5)
    q = next((x for x in range(d - 1, 1, -1) if lib.is_prime_power(x)), None)
    if q is not None:
        return lib.projective_plane_incidence(q)          # degree q+1 <= d, spare degree to use
    return None


def _fallback(d, D):
    """Always-valid graph: K_{d,d} for D >= 2, K_2 otherwise."""
    if D >= 2:
        return lib.haar_graph(d, range(d))
    return (2, [(0, 1)])


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    best = _fallback(d, D)
    try:
        start = known_start(d, D)
        if start is not None and start[0] > best[0] and lib.is_valid(*start, d, D):
            best = start
    except Exception:
        pass
    if not lib.is_valid(*best, d, D):
        return best
    if best[0] >= lib.moore_bound(d, D):
        return best   # Moore graph: nothing larger exists

    budget = 0.8 * time_limit - 3.0 - (time.monotonic() - t0)
    if budget < 2.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=best, timeout=budget + 5)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(*out, d, D):
            best = out
    except Exception:
        pass
    return best
