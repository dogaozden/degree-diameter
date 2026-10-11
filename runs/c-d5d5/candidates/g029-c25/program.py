"""Fixed-order annealing search for bipartite degree-diameter graphs.

Python picks a valid start (K_{d,d}, or a known construction for D = 3 or 4) and calls the C engine.
The C engine does not search over lifts. It works directly on simple bipartite graphs with exact
degree d, using degree-preserving double-edge switches as moves and the number of unreached
pairs (pairs at distance > D) as the cost, minimised by simulated annealing.

Each attempt is one of two kinds, chosen at random:
  (A) grow: add g pairs of new vertices to the current best by stealing old edges, then anneal.
  (B) fresh: draw a random d-regular bipartite graph on best.n + 2g vertices, then anneal.
A successful attempt replaces the best graph. Failed attempts increase the pair jump g
(up to 6 pairs), so the search can skip over sizes that one-pair steps keep missing.
Every output is re-checked in C and Python; the fallback is always a valid graph.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Degree-diameter bipartite search by annealing over degree-preserving switches.
 *
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v": a valid start graph, or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
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
    unsigned char side[MAXN];
} Graph;

typedef struct { int a, b, c, e; } Swap;

static int d, D;
static double t_end;

/* ------------------------------------------------------------ utilities */

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

/* ------------------------------------------------------------ graph basics */

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

/* ------------------------------------------------------------ distance check */

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static int badv[MAXN];

/* Number of unordered pairs at distance > D; fills badv[v] = unreached count of v. */
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

/* ------------------------------------------------------------ input / output */

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

/* ------------------------------------------------------------ constructions */

/* Random simple d-regular bipartite graph on n vertices (n/2 per side).
 * Each layer is a random perfect matching; conflicts with earlier layers are
 * repaired by random transpositions. Returns 0 on failure. */
static int random_regular(Graph *g, int n) {
    if (n < 2 || (n & 1) || n > MAXN) return 0;
    int half = n / 2;
    g->n = n;
    for (int v = 0; v < n; v++) { g->deg[v] = 0; g->side[v] = v >= half; }
    static int perm[MAXN];
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < half; i++) perm[i] = i;
        for (int i = half - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
        }
        int ok = 0;
        for (int pass = 0; pass < 3000 && !ok; pass++) {
            ok = 1;
            for (int i = 0; i < half; i++) {
                if (!has_edge(g, i, half + perm[i])) continue;
                ok = 0;
                int j = rndint(half);
                int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
            }
        }
        if (!ok) return 0;
        for (int i = 0; i < half; i++) add_edge(g, i, half + perm[i]);
    }
    return 1;
}

/* Grow by g pairs: each pair is a new edge x-y (x side 0, y side 1). x steals d-1 old
 * edges a-b (a side 0, b side 1) by taking b, and y takes a. Each old vertex is used at
 * most once per call, so old and new degrees come out exactly d. */
static int grow_setup(const Graph *best, Graph *work, int g) {
    int n = best->n;
    if (g < 1 || n + 2 * g > MAXN) return 0;
    copy_graph(work, best);
    work->n = n + 2 * g;
    static int used[MAXN];
    static int stamp = 0;
    stamp++;
    for (int p = 0; p < g; p++) {
        int x = n + 2 * p, y = x + 1;
        work->deg[x] = work->deg[y] = 0;
        work->side[x] = 0;
        work->side[y] = 1;
        add_edge(work, x, y);
        used[x] = used[y] = stamp;
    }
    for (int p = 0; p < g; p++) {
        int x = n + 2 * p, y = x + 1;
        int k = 0;
        for (int tries = 0; k < d - 1 && tries < 200000; tries++) {
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
        if (k < d - 1) return 0;
    }
    for (int v = n; v < work->n; v++)
        if (work->deg[v] != d) return 0;
    return 1;
}

/* ------------------------------------------------------------ annealing */

static int pick_side0(const Graph *g) {
    int v;
    do { v = rndint(g->n); } while (g->side[v] != 0);
    return v;
}

/* Vertex on side 0 for the first end of a switch; biased toward vertices in bad pairs. */
static int pick_a(const Graph *g) {
    if (rnd01() < 0.5) {
        for (int t = 0; t < 20; t++) {
            int v = pick_side0(g);
            if (badv[v] > 0) return v;
        }
    }
    return pick_side0(g);
}

/* Double-edge switch: a-b, c-e  ->  a-e, c-b  (a, c side 0; b, e side 1). Degrees are kept. */
static int propose_swap(const Graph *g, Swap *s) {
    int a = pick_a(g);
    if (g->deg[a] == 0) return 0;
    int b = g->adj[a][rndint(g->deg[a])];
    int c = pick_side0(g);
    if (c == a || g->deg[c] == 0) return 0;
    int e = g->adj[c][rndint(g->deg[c])];
    if (b == e) return 0;
    if (has_edge(g, a, e) || has_edge(g, c, b)) return 0;
    s->a = a; s->b = b; s->c = c; s->e = e;
    return 1;
}

static void apply_swap(Graph *g, const Swap *s) {
    del_edge(g, s->a, s->b);
    del_edge(g, s->c, s->e);
    add_edge(g, s->a, s->e);
    add_edge(g, s->c, s->b);
}

static void undo_swap(Graph *g, const Swap *s) {
    del_edge(g, s->a, s->e);
    del_edge(g, s->c, s->b);
    add_edge(g, s->a, s->b);
    add_edge(g, s->c, s->e);
}

/* Simulated annealing on the number of bad pairs. Returns 1 when the diameter bound holds
 * (cost 0), 0 when the time runs out. g is left in its current state either way. */
static int anneal(Graph *g, double until) {
    long cost = bad_pairs(g);
    double T = 2.0;
    long it = 0;
    while (cost > 0) {
        if ((++it & 7) == 0 && now() > until) return 0;
        Swap s;
        if (!propose_swap(g, &s)) continue;
        apply_swap(g, &s);
        long nb = bad_pairs(g);
        if (nb <= cost || rnd01() < exp((double)(cost - nb) / T)) {
            cost = nb;
        } else {
            undo_swap(g, &s);
        }
        T *= 0.9995;
        if (T < 0.05) T = 2.0;
    }
    return 1;
}

/* ------------------------------------------------------------ main search */

static void search(Graph *best, double until) {
    static Graph work;
    long lim = moore_bound();
    if (lim > MAXN) lim = MAXN;
    int fails = 0;
    while (now() < until) {
        int g = 1 + fails / 4;
        if (g > 6) g = 6;
        if (best->n + 2L * g > lim) g = (int)((lim - best->n) / 2);
        if (g < 1) return;
        double left = until - now();
        double slice = left / 3.0;
        if (slice < 1.0) slice = left;
        int ok = 0;
        if (rndint(2) == 0) {
            if (grow_setup(best, &work, g))
                ok = anneal(&work, now() + slice);
        } else {
            int tgt = best->n + 2 * g;
            if (random_regular(&work, tgt))
                ok = anneal(&work, now() + slice);
        }
        if (ok && work.n > best->n && is_valid(&work)) {
            copy_graph(best, &work);
            fails = 0;
        } else {
            fails++;
        }
    }
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
    t_end = t0 + limit * 0.9;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 1 || d > MAXD) { printf("1 0\n"); return 0; }
    if (d == 1 || D < 2) { printf("2 1\n0 1\n"); return 0; }

    static Graph best;
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);

    if (best.n < moore_bound()) search(&best, t_end);
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4, degree q+1."""
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


def known_start(d, D):
    """Best known construction Python can build directly for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)
    if D == 4:
        for q in range(min(d - 1, 7), 1, -1):
            if lib.is_prime_power(q) and q + 1 <= d:
                return _gq_w(q)
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

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if budget < 0.5:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=best, timeout=budget + 5)
        n, edges = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)
    except (RuntimeError, ValueError, OSError):
        pass
    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
