"""Cayley-graph search for bipartite degree-diameter graphs.

Python builds the best start it can (projective planes, Araujo-Pardo-Lopez graphs, or K_{d,d}).
The C engine then does two searches:
  1. A randomised sweep of bipartite Cayley graphs over metacyclic groups, from the largest
     order downward, to get a strong floor (the parent's approach).
  2. An exhaustive scan, which is the new part. For d = 3 it tests every connection set
     S = {e, a, b} in every metacyclic group of order N, for N = best/2 + 1, best/2 + 2, ...
     Each test is two BFS runs, so an entire order can be decided exactly. The first order
     that works is kept, and the scan moves on to the next one.
Every returned graph is checked with lib.is_valid, and K_{d,d} or the start graph is the fallback.
"""
import time

import lib

C_SOURCE = r'''
/* Bipartite Cayley-graph search core.
 *
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v" (valid start), or "0 0".
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * Bipartite Cayley graph over a group G of order N with connection set S (|S| = d, e in S):
 *   A_x ~ B_{x s} for s in S. Left multiplication is an automorphism, transitive on each side,
 *   so validity needs only BFS from A_e and from B_e to reach all 2N vertices within D steps.
 *
 * Phases:
 *   1. random_phase: sweep N downward from the Moore limit, sampling groups and sets.
 *   2. scan_phase: sweep N upward from best/2 + 1. For d = 3 each order is decided
 *      exhaustively over all metacyclic groups of order N and all S = {e, a, b}.
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
#define CAY_MAX 1100
#define MAXGRP 4096

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
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

static void copy_graph(Graph *dst, const Graph *src) {
    dst->n = src->n;
    for (int v = 0; v < src->n; v++) {
        dst->deg[v] = src->deg[v];
        dst->side[v] = src->side[v];
        memcpy(dst->adj[v], src->adj[v], sizeof(int) * src->deg[v]);
    }
}

/* ------------------------------------------------------------------ validity */

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];

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
        total += n - c;
    }
    return total / 2;
}

/* Simple, bipartite by side labels, degree <= d, diameter <= D. */
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

/* ------------------------------------------------------------------ groups */

/* Metacyclic groups Z_m x|_r Z_k of order N: list all (m, k, r) with gcd(r, m) = 1, r^k = 1 mod m. */
static int gm_[MAXGRP], gk_[MAXGRP], gr_[MAXGRP];

static int enum_groups(int N) {
    int G = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        if (m == 1) {
            if (G < MAXGRP) { gm_[G] = 1; gk_[G] = k; gr_[G] = 0; G++; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1 || powmod(r, k, m) != 1 % m) continue;
            if (G < MAXGRP) { gm_[G] = m; gk_[G] = k; gr_[G] = r; G++; }
        }
    }
    return G;
}

static int cN;
static int cmul[CAY_MAX * CAY_MAX]; /* cmul[x*N + y] = x*y */
static int cinv[CAY_MAX];
static int crp[CAY_MAX];

static void build_group(int m, int k, int r) {
    int N = m * k;
    for (int b = 0; b < k; b++) crp[b] = (int)powmod(r, b, m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            cmul[x * N + y] = (int)((a + (long)crp[b] * c) % m) * k + (b + e) % k;
        }
    }
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (cmul[x * N + y] == 0) { cinv[x] = y; break; }
    cN = N;
}

/* ------------------------------------------------------------------ Cayley tests */

static int cS[MAXD], cSinv[MAXD];
static int cdist[2 * CAY_MAX], cq[2 * CAY_MAX];

/* BFS from A_e (side 0) or B_e (side 1). Returns 1 if all 2N vertices lie within D steps. */
static int bfs_full(int N, int side) {
    int V = 2 * N, s0 = side ? N : 0;
    for (int v = 0; v < V; v++) cdist[v] = -1;
    int head = 0, tail = 0;
    cdist[s0] = 0;
    cq[tail++] = s0;
    while (head < tail) {
        int v = cq[head++];
        if (cdist[v] >= D) continue;
        if (v < N) {
            const int *row = cmul + v * N;
            for (int i = 0; i < d; i++) {
                int u = N + row[cS[i]];
                if (cdist[u] < 0) { cdist[u] = cdist[v] + 1; cq[tail++] = u; }
            }
        } else {
            const int *row = cmul + (v - N) * N;
            for (int i = 0; i < d; i++) {
                int u = row[cSinv[i]];
                if (cdist[u] < 0) { cdist[u] = cdist[v] + 1; cq[tail++] = u; }
            }
        }
    }
    return tail == V;
}

static int random_set(int N) {
    cS[0] = 0;
    int c = 1;
    for (int tries = 0; c < d; tries++) {
        if (tries > 100000) return 0;
        int x = 1 + rndint(N - 1), dup = 0;
        for (int i = 0; i < c; i++)
            if (cS[i] == x) { dup = 1; break; }
        if (!dup) cS[c++] = x;
    }
    for (int i = 0; i < d; i++) cSinv[i] = cinv[cS[i]];
    return 1;
}

static Graph cand;

/* Build the graph for the current group and S; keep it if valid and larger. */
static int found_graph(Graph *best, int N) {
    cand.n = 2 * N;
    for (int v = 0; v < cand.n; v++) { cand.deg[v] = 0; cand.side[v] = v >= N; }
    for (int x = 0; x < N; x++)
        for (int i = 0; i < d; i++) add_edge(&cand, x, N + cmul[x * N + cS[i]]);
    if (is_valid(&cand) && cand.n > best->n) { copy_graph(best, &cand); return 1; }
    return 0;
}

static long tick = 0;

/* Exhaustive (d = 3) or sampled (other d) search over groups of order N.
 * Returns 1 and updates best if a valid graph of order 2N is found. */
static int cayley_at(Graph *best, int N, double until) {
    int G = enum_groups(N);
    for (int i = G - 1; i > 0; i--) {
        int j = rndint(i + 1), t;
        t = gm_[i]; gm_[i] = gm_[j]; gm_[j] = t;
        t = gk_[i]; gk_[i] = gk_[j]; gk_[j] = t;
        t = gr_[i]; gr_[i] = gr_[j]; gr_[j] = t;
    }
    for (int g = 0; g < G; g++) {
        if (now() >= until) return 0;
        build_group(gm_[g], gk_[g], gr_[g]);
        if (d == 3) {
            for (int a = 1; a < N; a++)
                for (int b = a + 1; b < N; b++) {
                    if ((++tick & 255) == 0 && now() >= until) return 0;
                    cS[0] = 0; cS[1] = a; cS[2] = b;
                    cSinv[0] = 0; cSinv[1] = cinv[a]; cSinv[2] = cinv[b];
                    if (bfs_full(N, 0) && bfs_full(N, 1) && found_graph(best, N)) return 1;
                }
        } else {
            for (int t = 0; t < 3000; t++) {
                if ((++tick & 255) == 0 && now() >= until) return 0;
                if (random_set(N) && bfs_full(N, 0) && bfs_full(N, 1) && found_graph(best, N))
                    return 1;
            }
        }
    }
    return 0;
}

/* Phase 1: sweep N downward from the Moore limit with random groups and sets. */
static void random_phase(Graph *best, double until) {
    long Nmax = moore_bound() / 2;
    if (Nmax > CAY_MAX - 1) Nmax = CAY_MAX - 1;
    long Nmin = best->n / 2 + 1;
    if (Nmin < d + 1) Nmin = d + 1;
    for (long N = Nmax; N >= Nmin && now() < until; N--) {
        int G = enum_groups((int)N);
        if (G == 0) continue;
        int found = 0;
        for (int batch = 0; batch < 15 && !found && now() < until; batch++) {
            int gi = rndint(G);
            build_group(gm_[gi], gk_[gi], gr_[gi]);
            for (int t = 0; t < 200 && !found; t++)
                if (random_set((int)N) && bfs_full((int)N, 0) && bfs_full((int)N, 1)) found = 1;
        }
        if (found && found_graph(best, (int)N)) return;
    }
}

/* Phase 2: scan N upward from best/2 + 1. Each order is decided by cayley_at. */
static void scan_phase(Graph *best, double until) {
    long Nhi = moore_bound() / 2;
    if (Nhi > CAY_MAX - 1) Nhi = CAY_MAX - 1;
    long N = best->n / 2 + 1;
    if (N < d + 1) N = d + 1;
    if (N < 2) N = 2;
    while (N <= Nhi && now() < until) {
        long lo = best->n / 2 + 1;
        if (lo > N) N = lo;
        if (N > Nhi) break;
        if (!cayley_at(best, (int)N, until)) N++;
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
    t_end = t0 + limit * 0.9;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best;
    if (d < 1 || D < 1 || d > MAXD) { printf("0 0\n"); return 0; }
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);

    if (D >= 2 && best.n < moore_bound()) {
        random_phase(&best, t0 + 0.35 * (t_end - t0));
        scan_phase(&best, t_end);
    }
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


def known_start(d, D):
    """Best graph Python can build directly for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)           # record graphs of order 2(q^2+q+5)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    start = known_start(d, D)
    best = start if start is not None else lib.haar_graph(d, range(d))   # K_{d,d}: always valid
    if best[0] >= lib.moore_bound(d, D):
        return best   # Moore graph: nothing to improve
    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if budget > 0.2:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, budget], stdin_graph=start, timeout=budget + 5)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best
