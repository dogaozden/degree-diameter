"""Bi-Cayley / voltage-lift search with simulated annealing over a wide group family.

Strategy for the weak target cases (d >= 2, D >= 2, no Moore-type start):
  * Build a bipartite graph as a lift of a small d-regular base multigraph (p vertices
    per side, p in {1,2,3}) over a semidirect product Z_m x|_r Z_k of order N.
  * Pick a random group of order N and random voltages, then anneal the voltages
    (Metropolis on the number of pairs at distance > D) instead of greedy hill-climbing.
  * Each success raises the target order by 2. The best valid graph is always kept.

Python builds the known starts (Moore graphs, Araujo-Pardo-Lopez), keeps a validated
fallback (K_{d,d} or K_{1,1}), runs the C engine within a safe share of time_limit,
and returns the largest graph that passes lib.is_valid.
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

#define MAXN 2048
#define MAXD 32
#define MAXW (MAXN / 64)
#define MAXP 3
#define MAXGO 1024
#define MAXGRP 4096

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

typedef struct { int m, k, r; } GSpec;
typedef struct { int m, k, r; int rp[MAXGO]; } Grp;
typedef struct { int i, j, g; } Dart;

static int d, D;
static double t_end;
static uint64_t rng_state = 88172645463325252ULL;
static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static Graph best, cand;
static Grp G;
static GSpec gl[MAXGRP];
static int ng, ng_order = -1;
static Dart dt[MAXD * MAXP];
static int nd;

/* ------------------------------------------------------------ utilities */

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

/* K_{d,d}: valid whenever D >= 2. */
static void complete_bipartite(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= d; }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

/* ------------------------------------------------------------ groups */

/* Z_m x|_r Z_k, element (a,b) coded a*k+b, (a,b)(c,e) = (a + r^b c, b + e). */
static int gmul(const Grp *Gp, int x, int y) {
    int a = x / Gp->k, b = x % Gp->k, c = y / Gp->k, e = y % Gp->k;
    return (int)(((long)a + (long)Gp->rp[b] * c) % Gp->m) * Gp->k + (b + e) % Gp->k;
}

static void set_group(GSpec s) {
    G.m = s.m; G.k = s.k; G.r = s.r;
    G.rp[0] = 1 % G.m;
    for (int b = 1; b < G.k; b++) G.rp[b] = (int)((long)G.rp[b - 1] * G.r % G.m);
}

static void enum_groups(int N) {
    if (N == ng_order) return;
    ng_order = N;
    ng = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        if (m == 1) {
            if (ng < MAXGRP) { gl[ng].m = 1; gl[ng].k = k; gl[ng].r = 0; ng++; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1) continue;
            if (ng < MAXGRP) { gl[ng].m = m; gl[ng].k = k; gl[ng].r = r; ng++; }
        }
    }
}

/* ------------------------------------------------------------ lifts */

/* Random d-regular bipartite base multigraph on p+p vertices: sum of d permutations. */
static void make_base(int p, int M[MAXP][MAXP]) {
    for (;;) {
        memset(M, 0, sizeof(int) * MAXP * MAXP);
        for (int t = 0; t < d; t++) {
            int perm[MAXP];
            for (int i = 0; i < p; i++) perm[i] = i;
            for (int i = p - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int s = perm[i]; perm[i] = perm[j]; perm[j] = s;
            }
            for (int i = 0; i < p; i++) M[i][perm[i]]++;
        }
        int seen[2 * MAXP] = {0}, stack[2 * MAXP], top = 0, nseen = 1;
        seen[0] = 1;
        stack[top++] = 0;
        while (top) {
            int v = stack[--top];
            for (int u = 0; u < 2 * p; u++) {
                if (seen[u]) continue;
                int linked = v < p ? (u >= p && M[v][u - p]) : (u < p && M[u][v - p]);
                if (linked) { seen[u] = 1; nseen++; stack[top++] = u; }
            }
        }
        if (nseen == 2 * p) return;
    }
}

static void build_lift(Graph *g, int p, int N) {
    int P2 = p * N;
    g->n = 2 * P2;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= P2; }
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, dt[t].i * N + x, P2 + dt[t].j * N + gmul(&G, x, dt[t].g));
}

/* A voltage not used by another dart in the same (i,j) class (skip = dart to ignore). */
static int fresh_voltage(int skip, int i, int j, int N) {
    for (;;) {
        int g = rndint(N), clash = 0;
        for (int t = 0; t < nd; t++)
            if (t != skip && dt[t].i == i && dt[t].j == j && dt[t].g == g) { clash = 1; break; }
        if (!clash) return g;
    }
}

/* Simulated annealing over the dart voltages; on success g is the valid lift. */
static int anneal(Graph *g, int p, int N, long steps) {
    build_lift(g, p, N);
    long cur = bad_pairs(g);
    double T0 = 1.5, T1 = 0.05;
    for (long s = 0; s < steps && cur > 0; s++) {
        if ((s & 31) == 0 && now() > t_end) break;
        double T = T0 * pow(T1 / T0, (double)s / (double)steps);
        int t = rndint(nd);
        int old = dt[t].g;
        dt[t].g = fresh_voltage(t, dt[t].i, dt[t].j, N);
        build_lift(g, p, N);
        long nb = bad_pairs(g);
        if (nb <= cur || rnd01() < exp((double)(cur - nb) / T)) cur = nb;
        else dt[t].g = old;
    }
    if (cur != 0) return 0;
    build_lift(g, p, N);
    return 1;
}

/* One attempt: random group of order N, random base (p per side), annealed voltages. */
static int attempt(Graph *out, int p, int N, long steps) {
    enum_groups(N);
    if (ng == 0) return 0;
    set_group(gl[rndint(ng)]);
    int M[MAXP][MAXP];
    make_base(p, M);
    nd = 0;
    for (int i = 0; i < p; i++)
        for (int j = 0; j < p; j++)
            for (int c = 0; c < M[i][j]; c++) {
                dt[nd].i = i;
                dt[nd].j = j;
                dt[nd].g = fresh_voltage(-1, i, j, N);
                nd++;
            }
    return anneal(out, p, N, steps);
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
    t_end = t0 + limit * 0.9;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 1 || d > MAXD) { printf("1 0\n"); return 0; }
    if (D < 2 || d < 2) {
        /* K_{1,1}: degree 1, diameter 1. */
        printf("2 1\n0 1\n");
        return 0;
    }

    read_start(&best);
    long moore = moore_bound();

    while (now() < t_end) {
        long need = best.n + 2;
        if (need < 2L * d) need = 2L * d;
        if (need > moore) break;
        int p = 1 + rndint(3);
        long N = (need + 2L * p - 1) / (2L * p);
        if (rndint(3) == 0) N++;
        if (N < d) N = d;
        if (2L * p * N > moore || 2L * p * N > MAXN || N > MAXGO) {
            p = 1;
            N = (need + 1) / 2;
            if (N < d) N = d;
            if (2L * N > moore || 2L * N > MAXN || N > MAXGO) break;
        }
        if (attempt(&cand, p, (int)N, 3000) && cand.n > best.n && is_valid(&cand))
            copy_graph(&best, &cand);
    }

    if (best.n == 0) complete_bipartite(&best);
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


def _consider(best, cand, d, D):
    """Return the larger of best and cand if cand is a valid graph, else best."""
    if cand is None:
        return best
    n, edges = cand
    if n > best[0] and lib.is_valid(n, edges, d, D):
        return (n, list(edges))
    return best


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    best = (1, [])                                   # always valid fallback
    start = known_start(d, D)
    best = _consider(best, start, d, D)
    if D >= 2 and d >= 2:
        best = _consider(best, lib.haar_graph(d, range(d)), d, D)   # K_{d,d}
    best = _consider(best, lib.haar_graph(1, [0]), d, D)           # K_{1,1}

    if best[0] >= lib.moore_bound(d, D) or d < 2 or D < 2:
        return best

    budget = 0.72 * time_limit - (time.monotonic() - t0) - 2.0
    if budget > 1.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             stdin_graph=start, timeout=budget + 8.0)
            best = _consider(best, lib.parse_graph_text(text), d, D)
        except Exception:
            pass   # keep the validated fallback
    return best
