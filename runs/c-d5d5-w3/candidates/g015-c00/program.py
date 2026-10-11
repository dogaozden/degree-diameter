"""Scratch grow-and-anneal ladder for bipartite degree-diameter graphs.

This is a deliberately different search from the parent's symmetric lift search. The C engine
keeps a d-regular bipartite graph and grows it by one vertex per side. Each growth step is
repaired with degree-preserving double edge swaps, annealed on the number of vertex pairs at
distance > D. When a step reaches diameter <= D, the ladder moves on to the next order.

Risk: this does not reuse the parent's lift search, so on d5D5 it may fall below the parent's
352. The fallback is the best known construction, or K_{d,d}, which is always valid.
Every output is re-checked in C and again with lib.is_valid in Python.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Scratch grow-and-anneal ladder for bipartite degree-diameter graphs.
 *
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v": a d-regular valid start graph, or "0 0" for K_{d,d}.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * Each ladder step adds one vertex per side, joined to each other, and rewires d-1 edges
 * toward them. The result is d-regular again only after annealing, and the anneal uses
 * 2-switch swaps that keep every degree fixed and the graph simple and bipartite.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 768
#define MAXD 16
#define MAXW (MAXN / 64)

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} G;

static int d, D;
static double t_end;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];

/* Number of unordered pairs at distance > D. Zero means diameter <= D. */
static long bad_pairs(const G *g) {
    int n = g->n, W = (n + 63) / 64;
    uint64_t *cur = RA, *nxt = RB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            const uint64_t *src = cur + (size_t)v * W;
            memcpy(dst, src, sizeof(uint64_t) * W);
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

static int has_edge(const G *g, int u, int v) {
    for (int i = 0; i < g->deg[u]; i++)
        if (g->adj[u][i] == v) return 1;
    return 0;
}

static void add_edge(G *g, int u, int v) {
    g->adj[u][g->deg[u]++] = v;
    g->adj[v][g->deg[v]++] = u;
}

static void del_half(G *g, int u, int v) {
    for (int i = 0; i < g->deg[u]; i++)
        if (g->adj[u][i] == v) {
            g->adj[u][i] = g->adj[u][--g->deg[u]];
            return;
        }
}

static void del_edge(G *g, int u, int v) {
    del_half(g, u, v);
    del_half(g, v, u);
}

static int is_valid(const G *g) {
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

static void complete_bipartite(G *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) {
        g->deg[v] = 0;
        g->side[v] = v >= d;
    }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

/* Reads a d-regular valid bipartite start graph; leaves g->n = 0 otherwise. */
static void read_start(G *g) {
    int n, m;
    g->n = 0;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN || m < 0) return;
    static G tmp;
    tmp.n = n;
    for (int v = 0; v < n; v++) {
        tmp.deg[v] = 0;
        tmp.side[v] = 255;
    }
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= n || v >= n || u == v)
            return;
        if (tmp.deg[u] >= MAXD || tmp.deg[v] >= MAXD || has_edge(&tmp, u, v)) return;
        add_edge(&tmp, u, v);
    }
    for (int v = 0; v < n; v++)
        if (tmp.deg[v] != d) return;
    static int q[MAXN];
    for (int s = 0; s < n; s++) {
        if (tmp.side[s] != 255) continue;
        int head = 0, tail = 0;
        tmp.side[s] = 0;
        q[tail++] = s;
        while (head < tail) {
            int v = q[head++];
            for (int i = 0; i < tmp.deg[v]; i++) {
                int u = tmp.adj[v][i];
                if (tmp.side[u] == 255) {
                    tmp.side[u] = 1 - tmp.side[v];
                    q[tail++] = u;
                } else if (tmp.side[u] == tmp.side[v]) {
                    return;
                }
            }
        }
    }
    if (!is_valid(&tmp)) return;
    *g = tmp;
}

static void print_graph(const G *g) {
    long m = 0;
    for (int u = 0; u < g->n; u++)
        for (int i = 0; i < g->deg[u]; i++)
            if (u < g->adj[u][i]) m++;
    printf("%d %ld\n", g->n, m);
    for (int u = 0; u < g->n; u++)
        for (int i = 0; i < g->deg[u]; i++)
            if (u < g->adj[u][i]) printf("%d %d\n", u, g->adj[u][i]);
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

/* Copies cur into w and adds x (side 0) and y (side 1) joined to each other, then rewires
 * d-1 edges so x and y reach degree d. Degrees of old vertices stay d. */
static void grow_init(const G *cur, G *w) {
    int n = cur->n;
    *w = *cur;
    int x = n, y = n + 1;
    w->n = n + 2;
    w->deg[x] = w->deg[y] = 0;
    w->side[x] = 0;
    w->side[y] = 1;
    add_edge(w, x, y);
    static int used[MAXN];
    static int stamp = 0;
    stamp++;
    used[x] = used[y] = stamp;
    int k = 0;
    for (int tries = 0; k < d - 1 && tries < 200000; tries++) {
        int a = rndint(n);
        if (w->side[a] != 0 || used[a] == stamp || w->deg[a] == 0) continue;
        int b = w->adj[a][rndint(w->deg[a])];
        if (used[b] == stamp) continue;
        del_edge(w, a, b);
        add_edge(w, x, b);
        add_edge(w, y, a);
        used[a] = used[b] = stamp;
        k++;
    }
}

static int S0[MAXN], S1[MAXN], ns0, ns1;

static void build_lists(const G *g) {
    ns0 = ns1 = 0;
    for (int v = 0; v < g->n; v++) {
        if (g->deg[v] == 0) continue;
        if (g->side[v] == 0) S0[ns0++] = v;
        else S1[ns1++] = v;
    }
}

/* Swap edges (a1,b1),(a2,b2) for (a1,b2),(a2,b1). Degrees are unchanged. */
static void swap2(G *g, int a1, int b1, int a2, int b2) {
    del_edge(g, a1, b1);
    del_edge(g, a2, b2);
    add_edge(g, a1, b2);
    add_edge(g, a2, b1);
}

/* Anneal over degree-preserving 2-switches on side-0 pairs. Returns 1 if cost reaches 0. */
static int anneal(G *g, long steps, double until) {
    build_lists(g);
    if (ns0 < 2) return 0;
    long cost = bad_pairs(g);
    for (long s = 0; s < steps && cost > 0; s++) {
        if ((s & 127) == 0 && now() > until) break;
        double T = 1.0 * (1.0 - (double)s / (double)steps) + 0.03;
        int a1 = S0[rndint(ns0)], a2 = S0[rndint(ns0)];
        if (a1 == a2 || g->deg[a1] == 0 || g->deg[a2] == 0) continue;
        int b1 = g->adj[a1][rndint(g->deg[a1])];
        int b2 = g->adj[a2][rndint(g->deg[a2])];
        if (b1 == b2 || has_edge(g, a1, b2) || has_edge(g, a2, b1)) continue;
        swap2(g, a1, b1, a2, b2);
        long c2 = bad_pairs(g);
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) cost = c2;
        else swap2(g, a1, b2, a2, b1);
    }
    return cost == 0;
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
    t_end = t0 + limit * 0.97;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 1 || d > MAXD) { printf("1 0\n"); return 0; }
    if (d == 1 || D < 2) { printf("2 1\n0 1\n"); return 0; }

    static G cur, work;
    read_start(&cur);
    if (cur.n == 0) complete_bipartite(&cur);

    long moore = moore_bound();
    while (now() < t_end) {
        if (cur.n + 2 > moore || cur.n + 2 > MAXN) break;
        int ok = 0;
        while (!ok && now() < t_end) {
            grow_init(&cur, &work);
            ok = anneal(&work, 30000, t_end);
        }
        if (!ok) break;
        cur = work;
    }
    if (!is_valid(&cur)) complete_bipartite(&cur);
    print_graph(&cur);
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
        return lib.projective_plane_incidence(d - 1)
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)
    if D == 4:
        for q in range(min(d - 1, 7), 1, -1):
            if lib.is_prime_power(q) and q + 1 <= d:
                return _gq_w(q)
    return None


def _is_regular(n, edges, d):
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
    return all(x == d for x in deg)


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

    budget = 0.93 * time_limit - (time.monotonic() - t0) - 1.5
    if budget < 0.5:
        return best

    stdin_graph = best if _is_regular(best[0], best[1], d) else None
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=stdin_graph, timeout=budget + 2.5)
        n, edges = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)
    except (RuntimeError, ValueError, OSError):
        pass
    return best
