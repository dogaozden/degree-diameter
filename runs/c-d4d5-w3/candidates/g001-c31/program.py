"""Bold variant: nonabelian bi-Cayley start + scratch-style annealing growth in C.

Pipeline:
  1. Start from the best known construction (or K_{d,d}).
  2. Python searches bi-Cayley graphs over small groups (order N, two sides, connection set
     S of size d): vertices a_x ~ b_{x*s}. These are a different family from the Python lifts
     used before, and they can be larger than the record when diameter D allows it.
  3. C grows the best graph by two vertices at a time, then anneals degree-preserving edge
     swaps (cost = number of pairs farther than D apart) until the grown graph is valid.
Every stage keeps the best fully validated graph, so a failure only loses time.
"""
import math
import random
import time

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter: grow-and-anneal engine.
 * Usage:  prog d D seed time_limit   < start_graph
 * stdin:  "n m" then m lines "u v", or "0 0".
 * stdout: "n m" then edges, the largest valid graph found.
 */
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

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static long moore_bound(void) {
    if (D <= 0 || d <= 0) return 1;
    if (d == 1) return D >= 1 ? 2 : 1;
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

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];

/* Number of unordered pairs at distance greater than D. */
static long bad_pairs(const Graph *g) {
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

static int is_valid(const Graph *g) {
    if (g->n <= 0 || g->n > MAXN) return 0;
    for (int v = 0; v < g->n; v++) {
        if (g->deg[v] > d) return 0;
        for (int i = 0; i < g->deg[v]; i++) {
            int u = g->adj[v][i];
            if (u < 0 || u >= g->n || u == v || g->side[u] == g->side[v]) return 0;
            for (int j = 0; j < i; j++)
                if (g->adj[v][j] == u) return 0;
            int back = 0;
            for (int j = 0; j < g->deg[u]; j++)
                if (g->adj[u][j] == v) back = 1;
            if (!back) return 0;
        }
    }
    return bad_pairs(g) == 0;
}

static void read_start(Graph *g) {
    int n, m;
    g->n = 0;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN || m < 0) return;
    g->n = n;
    for (int v = 0; v < n; v++) { g->deg[v] = 0; g->side[v] = 255; }
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= n || v >= n || u == v ||
            g->deg[u] >= MAXD || g->deg[v] >= MAXD) {
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
                    g->side[u] = (unsigned char)(1 - g->side[v]);
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

static void complete_bipartite(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= d; }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

static void trivial(Graph *g) {
    g->n = 1;
    g->deg[0] = 0;
    g->side[0] = 0;
}

/* Insert x (side 0) and y (side 1) with edge x-y; move d-1 disjoint edges
 * (a_i, b_i) to (x, b_i) and (y, a_i). Degrees of old vertices are unchanged. */
static int grow_insert(const Graph *src, Graph *w) {
    int n = src->n;
    copy_graph(w, src);
    int x = n, y = n + 1;
    w->n = n + 2;
    w->deg[x] = 0;
    w->deg[y] = 0;
    w->side[x] = 0;
    w->side[y] = 1;
    add_edge(w, x, y);
    static int used[MAXN];
    static int stamp = 0;
    stamp++;
    int k = 0;
    for (int tries = 0; k < d - 1 && tries < 100000; tries++) {
        int a = rndint(n);
        if (w->side[a] != 0 || used[a] == stamp || w->deg[a] == 0) continue;
        int b = w->adj[a][rndint(w->deg[a])];
        if (b >= n || used[b] == stamp) continue;
        del_edge(w, a, b);
        add_edge(w, x, b);
        add_edge(w, y, a);
        used[a] = stamp;
        used[b] = stamp;
        k++;
    }
    return 1;
}

/* Degree-preserving swap annealing on the number of bad pairs. */
static int anneal(Graph *w, double until) {
    long bad = bad_pairs(w);
    const long L = 20000;
    const double Tmax = 1.5, Tmin = 0.05;
    for (long it = 0; bad > 0; it++) {
        if ((it & 127) == 0 && now() > until) return 0;
        double T = Tmax * pow(Tmin / Tmax, (double)(it % L) / (double)L);
        int a1 = rndint(w->n);
        if (w->side[a1] != 0 || w->deg[a1] == 0) continue;
        int b1 = w->adj[a1][rndint(w->deg[a1])];
        int b2 = rndint(w->n);
        if (w->side[b2] != 1 || w->deg[b2] == 0) continue;
        int a2 = w->adj[b2][rndint(w->deg[b2])];
        if (a1 == a2 || b1 == b2) continue;
        if (has_edge(w, a1, b2) || has_edge(w, a2, b1)) continue;
        del_edge(w, a1, b1);
        del_edge(w, a2, b2);
        add_edge(w, a1, b2);
        add_edge(w, a2, b1);
        long nb = bad_pairs(w);
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) {
            bad = nb;
        } else {
            del_edge(w, a1, b2);
            del_edge(w, a2, b1);
            add_edge(w, a1, b1);
            add_edge(w, a2, b2);
        }
    }
    return 1;
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
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best, cand;
    if (d < 1 || d > MAXD || D < 1) {
        trivial(&best);
        print_graph(&best);
        return 0;
    }
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (!is_valid(&best)) trivial(&best);

    long mb = moore_bound();
    int fails = 0;
    while (now() < t_end && best.n + 2 <= mb && best.n + 2 <= MAXN) {
        grow_insert(&best, &cand);
        double slice = 5.0;
        if (t_end - now() < slice) slice = t_end - now();
        if (anneal(&cand, now() + slice) && is_valid(&cand)) {
            copy_graph(&best, &cand);
            fails = 0;
        } else if (++fails > 100000) {
            break;
        }
    }
    if (!is_valid(&best)) trivial(&best);
    print_graph(&best);
    return 0;
}
'''


def known_start(d, D):
    """Best construction Python builds directly for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)
    return None


def cayley_start(d, D, floor_n, deadline, rng):
    """Search bi-Cayley graphs a_x ~ b_{x*s} (s in S, |S| = d) over groups of order N.

    Tries the largest N first and returns the first valid graph with order > floor_n,
    or None if the deadline passes first.
    """
    hi = lib.moore_bound(d, D) // 2
    for N in range(hi, floor_n // 2, -1):
        if time.monotonic() > deadline:
            break
        groups = []
        for m in range(1, N + 1):
            if N % m:
                continue
            k = N // m
            rs = [1] if m == 1 else range(1, m)
            for r in rs:
                if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                    groups.append((m, k, r))
        rng.shuffle(groups)
        for m, k, r in groups[:60]:
            if time.monotonic() > deadline:
                break
            order, mul, _ = lib.semidirect_group(m, k, r)
            for _ in range(20):
                S = rng.sample(range(order), d)
                n, edges = lib.group_lift(2, [(0, 1, g) for g in S], order, mul)
                if lib.is_valid(n, edges, d, D):
                    return n, edges
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    rng = random.Random(seed * 7919 + 17)

    best = known_start(d, D)
    if best is None or not lib.is_valid(*best, d, D):
        best = lib.haar_graph(d, range(d))          # K_{d,d}
    if not lib.is_valid(*best, d, D):
        return (1, [])                              # always valid fallback

    if D >= 2:
        cay = cayley_start(d, D, best[0], t0 + 0.25 * time_limit, rng)
        if cay is not None and cay[0] > best[0] and lib.is_valid(*cay, d, D):
            best = cay

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if budget > 0.5 and best[0] + 2 <= lib.moore_bound(d, D):
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, budget], stdin_graph=best,
                             timeout=budget + 5)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(*out, d, D):
                best = out
        except (RuntimeError, ValueError):
            pass
    return best
