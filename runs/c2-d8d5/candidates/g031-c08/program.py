"""Bold variant: simulated annealing over double-edge swaps on random bipartite d-regular graphs.

For each target order, the C engine starts from a random d-regular bipartite graph and
minimises the number of vertex pairs at distance > D by degree-preserving edge swaps.
A zero-cost state is a valid graph of that order. The order is then grown geometrically.
"""
import itertools
import time

import lib


C_SOURCE = r'''
/* Bipartite degree-diameter search by swap annealing on d-regular graphs.
 * Usage:  prog d D seed time_limit < start_graph
 * stdin:  "n m" + m edge lines (valid start), or "0 0".
 * stdout: "n m" + edge lines, the largest valid graph found.
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

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static int badv[MAXN];
static int cbad[MAXN];
static int blist[MAXN];
static int nbl;

/* Number of unordered pairs at distance > D. Fills badv[v] = number of bad partners of v. */
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
        uint64_t *tmp = cur;
        cur = nxt;
        nxt = tmp;
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

/* Circulant d-regular bipartite graph on sides of size h (requires h >= d). */
static void regular_start(Graph *g, int h) {
    g->n = 2 * h;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= h; }
    for (int a = 0; a < h; a++)
        for (int j = 0; j < d; j++) add_edge(g, a, h + (a + j) % h);
}

/* Propose a double-edge swap: remove a-b and c-e (a,c on side A), add a-e and c-b.
 * With use_bad, a is biased toward vertices holding bad pairs in the accepted state. */
static int pick_swap(const Graph *g, int h, int use_bad, int *A, int *B, int *C, int *E) {
    int a;
    if (use_bad && nbl > 0 && rnd01() < 0.5) {
        int v = blist[rndint(nbl)];
        a = v < h ? v : g->adj[v][rndint(d)];
    } else {
        a = rndint(h);
    }
    int c = rndint(h);
    if (c == a) return 0;
    int b = g->adj[a][rndint(d)];
    int e = g->adj[c][rndint(d)];
    if (has_edge(g, a, e) || has_edge(g, c, b)) return 0;
    *A = a; *B = b; *C = c; *E = e;
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

static void rebuild_blist(int n) {
    nbl = 0;
    for (int v = 0; v < n; v++)
        if (cbad[v]) blist[nbl++] = v;
}

/* Anneal a random d-regular bipartite graph on 2h vertices to zero bad pairs. */
static int anneal(int h, double deadline, Graph *out) {
    static Graph g;
    int a, b, c, e;
    regular_start(&g, h);
    long mix = 4L * g.n * d / 2;
    nbl = 0;
    for (long t = 0; t < mix; t++) {
        if (!pick_swap(&g, h, 0, &a, &b, &c, &e)) continue;
        apply_swap(&g, a, b, c, e);
    }
    long bad = bad_pairs(&g);
    if (bad == 0) { copy_graph(out, &g); return 1; }
    memcpy(cbad, badv, sizeof(int) * g.n);
    rebuild_blist(g.n);

    double start = now();
    double span = deadline - start;
    if (span <= 0) return 0;
    double T = 1.0;
    long it = 0;
    for (;;) {
        if ((++it & 7) == 0) {
            double tn = now();
            if (tn > deadline) return 0;
            double frac = (tn - start) / span;
            T = 0.05 + 0.8 * (1.0 - frac);
        }
        if (!pick_swap(&g, h, 1, &a, &b, &c, &e)) continue;
        apply_swap(&g, a, b, c, e);
        long nb = bad_pairs(&g);
        if (nb <= bad || rnd01() < exp(-(double)(nb - bad) / T)) {
            bad = nb;
            memcpy(cbad, badv, sizeof(int) * g.n);
            rebuild_blist(g.n);
            if (bad == 0) { copy_graph(out, &g); return 1; }
        } else {
            undo_swap(&g, a, b, c, e);
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
    t_end = t0 + limit * 0.92;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }

    static Graph best, cand;
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);

    long moore = moore_bound();
    int step = 2;
    while (now() < t_end) {
        int h = (best.n + 1) / 2 + step / 2;
        if (h < d) h = d;
        if (2L * h > moore || 2L * h > MAXN) {
            if (step > 2) { step = 2; continue; }
            break;
        }
        double remain = t_end - now();
        double slice = remain / 3.0;
        if (slice < 1.0) slice = remain;
        if (anneal(h, now() + slice, &cand) && cand.n > best.n && is_valid(&cand)) {
            copy_graph(&best, &cand);
            if (step < 256) step *= 2;
        } else if (step > 2) {
            step /= 2;
        }
    }

    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    usable = max(1.0, 0.85 * time_limit - 2.0)
    end = t0 + usable

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        """Keep the graph if it is a larger valid graph."""
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact constructions for small cases.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            ar = lib.araujo_lopez_graph(d - 2)
            consider(ar[0], ar[1])
        except (ValueError, RuntimeError):
            pass
    if D == 4 and time.monotonic() < end:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main search: swap annealing on bipartite d-regular graphs, grown from the best so far.
    if D >= 2:
        c_budget = end - time.monotonic() - 0.5
        if c_budget > 1.0:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(c_budget, 2)],
                                 stdin_graph=best, timeout=c_budget + 8)
                out = lib.parse_graph_text(text)
                consider(out[0], out[1])
            except (RuntimeError, ValueError):
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
