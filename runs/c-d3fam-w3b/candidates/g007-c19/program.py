"""Grow-by-two search for bipartite degree-diameter graphs.

Python supplies the best known start it can build directly (Araujo-Pardo and Lopez for D = 3,
or the projective plane when d-1 is a prime power). C grows that start by two vertices at a time.
The new vertex pair is wired by greedy ball cover: each rewired edge is chosen to add the most
unreached vertices to the balls of the new vertices. The annealed swap repair that follows keeps
two thirds of its proposals targeted at bad pairs. Failed repairs are kept as a frontier across
time slices. build() returns only graphs that pass lib.is_valid.
"""
import time

import lib

TIME_FRAC = 0.93  # fraction of time_limit given to the C engine

C_SOURCE = r'''
/* Bipartite degree-diameter grow-by-two search.
 *
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v": a valid start graph, or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * New in this version: greedy ball-cover insertion. A new vertex pair x (side 0), y (side 1)
 * is wired by rewiring d-1 edges (a,b) with a on side 0 and b on side 1: b becomes a neighbour
 * of x and a becomes a neighbour of y. Each rewiring is chosen greedily to maximise the number
 * of vertices newly covered by the radius-(D-1) balls of x's and y's neighbours.
 * Random insertion is kept for diversity. The annealed targeted swap repair is unchanged.
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

/* ------------------------------------------------------------ reach balls */

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static uint64_t BA[MAXN * MAXW], BB[MAXN * MAXW];
static int badv[MAXN];
static uint64_t *final_reach = RA;
static int final_W = 0;

/* Bit w of row v is set iff dist(v, w) <= R. Result is in cur (one of the two buffers). */
static uint64_t *reach_rounds(const Graph *g, int R, uint64_t *cur, uint64_t *nxt) {
    int n = g->n, W = (n + 63) / 64;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int r = 0; r < R; r++) {
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
    return cur;
}

/* Number of unordered pairs at distance > D. Also fills badv and final_reach. */
static long bad_pairs(const Graph *g) {
    int n = g->n, W = (n + 63) / 64;
    uint64_t *cur = reach_rounds(g, D, RA, RB);
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

static int reached(int v, int w) {
    return (int)((final_reach[(size_t)v * final_W + w / 64] >> (w % 64)) & 1ULL);
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

static void complete_bipartite(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= d; }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

/* ------------------------------------------------------------ insertion */

static int have_frontier = 0;
static Graph frontier;
static double frontier_T = 1.0;

/* Random insertion: rewire d-1 random edges (a,b) to (x,b) and (y,a). */
static void random_insert(const Graph *best, Graph *dst) {
    int n = best->n;
    copy_graph(dst, best);
    int x = n, y = n + 1;
    dst->n = n + 2;
    dst->deg[x] = dst->deg[y] = 0;
    dst->side[x] = 0;
    dst->side[y] = 1;
    add_edge(dst, x, y);
    static char used[MAXN];
    memset(used, 0, sizeof(used));
    used[x] = used[y] = 1;
    for (int k = 0, tries = 0; k < d - 1 && tries < 100000; tries++) {
        int a = rndint(n);
        if (dst->side[a] != 0 || used[a] || dst->deg[a] == 0) continue;
        int b = dst->adj[a][rndint(dst->deg[a])];
        if (used[b] || b >= n) continue;
        del_edge(dst, a, b);
        add_edge(dst, x, b);
        add_edge(dst, y, a);
        used[a] = used[b] = 1;
        k++;
    }
}

/* Greedy ball-cover insertion. Each step picks the rewirable edge (a,b) that most increases
 * the union of radius-(D-1) balls: b's ball covers for x, a's ball covers for y. Ties are
 * broken uniformly at random. */
static void greedy_insert(const Graph *best, Graph *dst) {
    int n = best->n, W = (n + 63) / 64;
    copy_graph(dst, best);
    int x = n, y = n + 1;
    dst->n = n + 2;
    dst->deg[x] = dst->deg[y] = 0;
    dst->side[x] = 0;
    dst->side[y] = 1;
    add_edge(dst, x, y);
    uint64_t *B = reach_rounds(best, D - 1, BA, BB);
    static uint64_t cx[MAXW], cy[MAXW];
    static char used[MAXN];
    memset(cx, 0, sizeof(uint64_t) * W);
    memset(cy, 0, sizeof(uint64_t) * W);
    memset(used, 0, sizeof(used));
    for (int k = 0; k < d - 1; k++) {
        int bestA = -1, bestB = -1;
        long bs = -1;
        int ties = 0;
        for (int a = 0; a < n; a++) {
            if (dst->side[a] != 0 || used[a]) continue;
            for (int i = 0; i < dst->deg[a]; i++) {
                int b = dst->adj[a][i];
                if (used[b] || b >= n) continue;
                long gx = 0, gy = 0;
                const uint64_t *rb = B + (size_t)b * W, *ra = B + (size_t)a * W;
                for (int w = 0; w < W; w++) {
                    gx += __builtin_popcountll(rb[w] & ~cx[w]);
                    gy += __builtin_popcountll(ra[w] & ~cy[w]);
                }
                long s = gx + gy;
                if (s > bs) {
                    bs = s; bestA = a; bestB = b; ties = 1;
                } else if (s == bs && rndint(++ties) == 0) {
                    bestA = a; bestB = b;
                }
            }
        }
        if (bestA < 0) break;
        del_edge(dst, bestA, bestB);
        add_edge(dst, x, bestB);
        add_edge(dst, y, bestA);
        used[bestA] = used[bestB] = 1;
        for (int w = 0; w < W; w++) {
            cx[w] |= B[(size_t)bestB * W + w];
            cy[w] |= B[(size_t)bestA * W + w];
        }
    }
}

/* ------------------------------------------------------------ annealed repair */

static int propose(const Graph *g, int v, int *pu, int *ps, int *pt, int targeted) {
    int n = g->n, u, s, t;
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
            if (rndint(10) < 7) greedy_insert(best, &frontier);
            else random_insert(best, &frontier);
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
        } else if (++fails >= 6) {
            have_frontier = 0;
        }
    }
}

/* ------------------------------------------------------------ main */

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
    if (best.n == 0) complete_bipartite(&best);
    if (D >= 2 && best.n < moore_bound()) grow_search(&best, t_end);
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


# ---------------------------------------------------------------- Python constructions

def known_start(d):
    """Best known D = 3 construction for max degree d, or None."""
    if lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)       # Moore graph, optimal
    if d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            return lib.araujo_lopez_graph(d - 2)           # record 2(q^2+q+5), q = d-2
        except ValueError:
            return None
    return None


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    t0 = time.monotonic()

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    best = lib.haar_graph(d, range(d))                  # K_{d,d}: always valid for D >= 2
    if D == 2:
        return best

    start = None
    if D == 3:
        try:
            start = known_start(d)
        except Exception:
            start = None
    if start is not None and start[0] > best[0] and lib.is_valid(start[0], start[1], d, D):
        best = start

    if best[0] >= lib.moore_bound(d, D):                # Moore-extremal: nothing to search
        return best

    budget = TIME_FRAC * time_limit - (time.monotonic() - t0) - 1.5
    if budget > 1.0:
        stdin_graph = best if best[0] > 2 * d else None
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             stdin_graph=stdin_graph, timeout=budget + 5)
            n, e = lib.parse_graph_text(text)
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
        except (RuntimeError, ValueError):
            pass                                        # keep the valid Python fallback
    return best
