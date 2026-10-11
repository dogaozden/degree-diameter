"""Bold variant: a two-stage search that keeps the best valid graph throughout.

Stage 1 (lifts): hill-climb voltages of small semidirect-product lifts (p = 1 or 2 base
vertices per side) to get a valid graph larger than the current best.
Stage 2 (anneal-grow): repeatedly insert two vertices (one per side) into the best graph,
rewire with degree-preserving edge swaps, and anneal the number of pairs at distance > D
down to zero. Success moves the best graph up by two vertices.

Python always starts from a validated graph and only accepts C output that passes lib.is_valid,
so any C failure falls back to the starting graph.
"""
import time

import lib

C_SOURCE = r'''
/* Two-stage bipartite degree-diameter search.
 * Usage:  prog d D seed time_limit   < start_graph
 * stdin:  "n m" + m edge lines, or "0 0".
 * stdout: "n m" + m edge lines of the largest valid graph found.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 512
#define MAXD 16
#define MAXW (MAXN / 64)
#define MAXP 2

#define T_HOT 0.6
#define T_COLD 0.05
#define COOL 0.9995

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

typedef struct {
    int m, k, r;
    int rp[MAXN];
} Grp;

typedef struct { int i, j, g; } Dart;

static int d, D;
static double t_end;
static uint64_t rng_state = 88172645463325252ULL;

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

/* ------------------------------------------------------------ distance cost */

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static int badv[MAXN]; /* vertices farther than D from v in the last evaluated state */

/* Number of unordered pairs at distance > D. Zero means valid diameter. */
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

/* ------------------------------------------------------------ stage 1: lifts */

static int gmul(const Grp *G, int x, int y) {
    int a = x / G->k, b = x % G->k, c = y / G->k, e = y % G->k;
    return (int)((a + (long)G->rp[b] * c) % G->m) * G->k + (b + e) % G->k;
}

/* Random (m, k, r) with m*k = N, gcd(r, m) = 1, r^k = 1 mod m (uniform over choices). */
static int random_group(int N, Grp *G) {
    long count = 0;
    int found = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        int rmax = m > 1 ? m : 2;
        for (int r = 1; r < rmax; r++) {
            if (m > 1 && gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            count++;
            if (rndint((int)count) == 0) { G->m = m; G->k = k; G->r = r; found = 1; }
        }
    }
    if (!found) return 0;
    G->rp[0] = 1 % G->m;
    for (int b = 1; b < G->k; b++) G->rp[b] = (int)((long)G->rp[b - 1] * G->r % G->m);
    return 1;
}

/* A voltage not used by another dart on the same base pair (i, j). */
static int fresh_g(const Dart *dt, int nd, int skip, int i, int j, int N) {
    for (;;) {
        int g = rndint(N), ok = 1;
        for (int t = 0; t < nd && ok; t++)
            if (t != skip && dt[t].i == i && dt[t].j == j && dt[t].g == g) ok = 0;
        if (ok) return g;
    }
}

static void build_lift(Graph *g, int p, int N, const Grp *G, const Dart *dt, int nd) {
    g->n = 2 * p * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= p * N; }
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, dt[t].i * N + x, p * N + dt[t].j * N + gmul(G, x, dt[t].g));
}

/* Hill-climb the voltages of a random d-regular base with p vertices per side.
 * On success g holds the valid lift. */
static int lift_try(Graph *g, int p, int N, const Grp *G, long steps, double until) {
    Dart dt[MAXD * MAXP];
    int M[MAXP][MAXP], nd = 0;
    memset(M, 0, sizeof M);
    for (int t = 0; t < d; t++) {
        int perm[MAXP];
        for (int i = 0; i < p; i++) perm[i] = i;
        if (p == 2 && (t == 1 || (t >= 2 && rndint(2)))) { perm[0] = 1; perm[1] = 0; }
        for (int i = 0; i < p; i++) M[i][perm[i]]++;
    }
    for (int i = 0; i < p; i++)
        for (int j = 0; j < p; j++)
            for (int c = 0; c < M[i][j]; c++) {
                dt[nd].i = i;
                dt[nd].j = j;
                dt[nd].g = fresh_g(dt, nd, -1, i, j, N);
                nd++;
            }
    build_lift(g, p, N, G, dt, nd);
    long bad = bad_pairs(g);
    for (long s = 0; s < steps && bad > 0; s++) {
        if ((s & 15) == 0 && now() > until) return 0;
        int t = rndint(nd);
        int old = dt[t].g;
        dt[t].g = fresh_g(dt, nd, t, dt[t].i, dt[t].j, N);
        build_lift(g, p, N, G, dt, nd);
        long nb = bad_pairs(g);
        if (nb <= bad || rnd01() < 0.02) bad = nb;
        else dt[t].g = old;
    }
    if (bad != 0) return 0;
    build_lift(g, p, N, G, dt, nd); /* g may hold a rejected proposal; rebuild from accepted voltages */
    return 1;
}

static void lift_stage(Graph *best, double until) {
    static Graph cand;
    static Grp G;
    long cap = moore_bound();
    if (cap > MAXN) cap = MAXN;
    int fails = 0;
    while (now() < until && fails < 5000) {
        int p = 1 + rndint(2);
        long target = best->n + 2;
        if (target > cap) break;
        int N = (int)((target + 2 * p - 1) / (2 * p)) + rndint(3);
        if (N < d || 2L * p * N > cap) { fails++; continue; }
        if (!random_group(N, &G)) { fails++; continue; }
        long steps = 300 + 200000 / (2 * p * N);
        if (lift_try(&cand, p, N, &G, steps, until) && cand.n > best->n && is_valid(&cand))
            copy_graph(best, &cand);
    }
}

/* ------------------------------------------------------------ stage 2: anneal-grow */

/* Insert one vertex per side (joined to each other) and steal d-1 edges to give both degree d. */
static void insert_two(const Graph *src, Graph *dst) {
    int n = src->n;
    copy_graph(dst, src);
    int x = n, y = n + 1;
    dst->n = n + 2;
    dst->deg[x] = dst->deg[y] = 0;
    dst->side[x] = 0;
    dst->side[y] = 1;
    add_edge(dst, x, y);
    static int used[MAXN];
    static int stamp = 0;
    stamp++;
    used[x] = used[y] = stamp;
    int k = 0;
    for (int tries = 0; k < d - 1 && tries < 200000; tries++) {
        int a = rndint(n);
        if (dst->side[a] != 0 || used[a] == stamp || dst->deg[a] == 0) continue;
        int b = dst->adj[a][rndint(dst->deg[a])];
        if (used[b] == stamp) continue;
        del_edge(dst, a, b);
        add_edge(dst, x, b);
        add_edge(dst, y, a);
        used[a] = used[b] = stamp;
        k++;
    }
}

/* Degree-preserving edge swaps, Metropolis on the bad-pair count, until bad == 0.
 * Returns 1 if the graph became valid. The graph is always left in a consistent state. */
static int anneal(Graph *g, double until, long max_it) {
    long bad = bad_pairs(g);
    double T = T_HOT;
    for (long it = 1; bad > 0; it++) {
        if (it > max_it) return 0;
        if ((it & 63) == 0 && now() > until) return 0;
        int n = g->n;
        int v = rndint(n);
        for (int tr = 0; tr < 40 && badv[v] == 0; tr++) v = rndint(n);
        if (g->deg[v] == 0) continue;
        int u = g->adj[v][rndint(g->deg[v])];
        int s = rndint(n);
        if (s == v || g->side[s] != g->side[v] || g->deg[s] == 0) continue;
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
        T *= COOL;
        if (T < T_COLD) T = T_HOT;
    }
    return 1;
}

static void search(Graph *best, double until) {
    static Graph cand;
    long cap = moore_bound();
    if (cap > MAXN) cap = MAXN;
    while (now() < until && best->n + 2 <= cap) {
        double left = until - now();
        double slice = left / 3.0;
        if (slice < 5.0) slice = 5.0;
        if (slice > left) slice = left;
        insert_two(best, &cand);
        if (anneal(&cand, now() + slice, 3000000L) && is_valid(&cand))
            copy_graph(best, &cand);
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
    t_end = t0 + limit * 0.9;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 1) { printf("1 0\n"); return 0; }
    if (d == 1 || D == 1 || d > MAXD) { printf("2 1\n0 1\n"); return 0; }

    static Graph best;
    read_start(&best);
    if (best.n == 0 || !is_valid(&best)) complete_bipartite(&best);

    lift_stage(&best, t0 + 0.35 * (t_end - t0));
    search(&best, t_end);

    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


def known_start(d, D):
    """Best graph Python can build directly for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)
    return None


def fallback(d, D):
    """Always-valid graph: K_{d,d} for D >= 2, else K_{1,1}, else a single vertex."""
    candidates = []
    if D >= 2 and d >= 2:
        candidates.append(lib.haar_graph(d, range(d)))
    candidates.append((2, [(0, 1)]))
    candidates.append((1, []))
    for g in candidates:
        if lib.is_valid(*g, d, D):
            return g
    return (1, [])


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    best = known_start(d, D)
    if best is None or not lib.is_valid(*best, d, D):
        best = fallback(d, D)
    budget = 0.8 * time_limit - (time.monotonic() - t0) - 1.5
    if budget < 0.5:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=best, timeout=budget + 5)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(*out, d, D):
            best = out
    except Exception:
        pass  # keep the valid fallback
    return best
