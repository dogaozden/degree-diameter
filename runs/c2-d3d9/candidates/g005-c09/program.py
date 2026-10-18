"""Starter program: Python builds the best known start graph, the C engine searches from it.

Most improvements belong in C_SOURCE (it runs 10-100x faster than Python).
build() keeps the best valid graph it has, so a broken idea in C can only cost time.

This version replaces the voltage-lift and grow-by-two search with a different
pipeline: bipartite Cayley graphs first, then simulated annealing of 2-switch
edge moves (guided toward bad vertices) on graphs grown two vertices at a time.
"""
import time

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search core (annealing variant).
 *
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v": a valid starting graph, or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * Phases:
 *   1. Bipartite Cayley graphs over metacyclic groups (hill-climb on connection sets).
 *   2. Annealing on 2-switch moves: from the current valid graph, insert one vertex per
 *      side, then anneal the number of pairs at distance > D to zero. On success the
 *      graph is kept and the process grows by two again.
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
#define CAY_MAX 1000

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
static int badv[MAXN]; /* badv[v] = vertices farther than D from v (set by bad_pairs) */

/* Number of unordered pairs at distance > D (0 means diameter <= D). */
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

/* ------------------------------------------------------------------ bipartite Cayley graphs */

static int *cmul = NULL; /* cmul[x*N + y] = x*y */
static int *cinv = NULL; /* cinv[x] = x^{-1} */
static int cN = 0;
static int cS[MAXD], cSinv[MAXD];
static int cdist[2 * CAY_MAX], cq[2 * CAY_MAX];
static Graph cand_g;

/* Multiplication table of Z_m x|_r Z_k (order N = m*k). */
static int build_group(int m, int k, int r) {
    int N = m * k;
    int *rp = malloc(sizeof(int) * (size_t)k);
    if (!rp) return 0;
    cmul = realloc(cmul, sizeof(int) * (size_t)N * N);
    cinv = realloc(cinv, sizeof(int) * (size_t)N);
    if (!cmul || !cinv) { free(rp); return 0; }
    for (int b = 0; b < k; b++) rp[b] = (int)powmod(r, b, m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            cmul[x * N + y] = (int)((a + (long)rp[b] * c) % m) * k + (b + e) % k;
        }
    }
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (cmul[x * N + y] == 0) { cinv[x] = y; break; }
    cN = N;
    free(rp);
    return 1;
}

/* Random connection set S = {e, s_1, ..., s_{d-1}}. Returns 0 on failure. */
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

/* Vertices not within distance D of A_e plus those not within D of B_e. Zero means valid. */
static long cayley_cost(int N) {
    int V = 2 * N;
    long miss = 0;
    for (int i = 0; i < d; i++) cSinv[i] = cinv[cS[i]];
    for (int src = 0; src < 2; src++) {
        int s0 = src ? N : 0;
        for (int v = 0; v < V; v++) cdist[v] = -1;
        int head = 0, tail = 0;
        cdist[s0] = 0;
        cq[tail++] = s0;
        while (head < tail) {
            int v = cq[head++];
            if (cdist[v] >= D) continue;
            if (v < N) {
                for (int i = 0; i < d; i++) {
                    int u = N + cmul[v * N + cS[i]];
                    if (cdist[u] < 0) { cdist[u] = cdist[v] + 1; cq[tail++] = u; }
                }
            } else {
                int y = v - N;
                for (int i = 0; i < d; i++) {
                    int u = cmul[y * N + cSinv[i]];
                    if (cdist[u] < 0) { cdist[u] = cdist[v] + 1; cq[tail++] = u; }
                }
            }
        }
        miss += V - tail;
    }
    return miss;
}

static int cayley_climb(int N, double until, long steps) {
    if (!random_set(N)) return 0;
    long cur = cayley_cost(N);
    for (long s = 0; s < steps && cur > 0; s++) {
        if ((s & 63) == 0 && now() > until) return 0;
        int i = 1 + rndint(d - 1);
        int x, dup;
        do {
            x = 1 + rndint(N - 1);
            dup = 0;
            for (int j = 0; j < d; j++)
                if (cS[j] == x) { dup = 1; break; }
        } while (dup);
        int old = cS[i];
        cS[i] = x;
        long c = cayley_cost(N);
        if (c <= cur || rnd01() < 0.02) cur = c;
        else cS[i] = old;
    }
    if (cur != 0) return 0;
    for (int i = 0; i < d; i++) cSinv[i] = cinv[cS[i]];
    return 1;
}

/* Sweep orders N downward from the Moore limit, with time slices, hill-climbing random
 * metacyclic groups of each order. The first success is the largest Cayley graph found. */
static void cayley_phase(Graph *best, double until) {
    long moore = moore_bound();
    long Nmax = moore / 2;
    if (Nmax > CAY_MAX) Nmax = CAY_MAX;
    long Nmin = best->n / 2 + 1;
    if (Nmin < d + 1) Nmin = d + 1;
    if (Nmin < 2) Nmin = 2;
    static int gm[1024], gk[1024], gr[1024];
    for (long N = Nmax; N >= Nmin; N--) {
        double t_now = now();
        if (t_now > until) break;
        double slice = (until - t_now) / (double)(N - Nmin + 1) * 2.0;
        if (slice > until - t_now) slice = until - t_now;
        double slice_end = t_now + slice;
        int G = 0;
        for (int m = 1; m <= N; m++) {
            if (N % m) continue;
            int k = (int)(N / m);
            if (m == 1) {
                if (G < 1024) { gm[G] = 1; gk[G] = k; gr[G] = 0; G++; }
                continue;
            }
            for (int r = 1; r < m; r++) {
                if (gcd(r, m) != 1 || powmod(r, k, m) != 1 % m) continue;
                if (G < 1024) { gm[G] = m; gk[G] = k; gr[G] = r; G++; }
            }
        }
        if (G == 0) continue;
        int found = 0;
        while (!found && now() < slice_end) {
            int gi = rndint(G);
            if (!build_group(gm[gi], gk[gi], gr[gi])) return;
            for (int rep = 0; rep < 4 && !found && now() < slice_end; rep++)
                if (cayley_climb((int)N, slice_end, 20000)) found = 1;
        }
        if (found) {
            cand_g.n = (int)(2 * N);
            for (int v = 0; v < cand_g.n; v++) { cand_g.deg[v] = 0; cand_g.side[v] = v >= N; }
            for (int x = 0; x < N; x++)
                for (int i = 0; i < d; i++) add_edge(&cand_g, x, (int)N + cmul[x * N + cS[i]]);
            if (is_valid(&cand_g) && cand_g.n > best->n) copy_graph(best, &cand_g);
            return;
        }
    }
}

/* ------------------------------------------------------------------ annealing */

/* Anneal 2-switch moves on g (in place) until its diameter is <= D. Moves are biased
 * toward vertices with far-away partners. Returns 1 if g ends valid, else 0 (g is then
 * a perturbed graph and must be discarded by the caller). */
static int anneal(Graph *g, double until) {
    long bad = bad_pairs(g);
    if (bad == 0) return 1;
    int n = g->n;
    double T = 1.5;
    long it = 0;
    while (bad > 0) {
        if ((++it & 31) == 0 && now() > until) return 0;
        int v = rndint(n);
        for (int tries = 0; tries < 20 && badv[v] == 0; tries++) v = rndint(n);
        if (g->deg[v] == 0) continue;
        int u = g->adj[v][rndint(g->deg[v])];
        int s = rndint(n);
        if (g->side[s] != g->side[v] || s == v || g->deg[s] == 0) continue;
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
        T *= 0.9997;
        if (T < 0.08) T = 1.5;
    }
    return 1;
}

/* Copy best into work with one new vertex per side, both of degree d where possible,
 * by rewiring d-1 edges of the old graph through the new vertices. */
static int grow2(const Graph *best, Graph *work) {
    int n = best->n;
    if (n + 2 > moore_bound() || n + 2 > MAXN) return 0;
    copy_graph(work, best);
    int x = n, y = n + 1;
    work->n = n + 2;
    work->deg[x] = work->deg[y] = 0;
    work->side[x] = 0;
    work->side[y] = 1;
    add_edge(work, x, y);
    static int used[MAXN];
    static int stamp = 0;
    stamp++;
    used[x] = used[y] = stamp;
    for (int k = 0, tries = 0; k < d - 1 && tries < 100000; tries++) {
        int a = rndint(n);
        if (work->side[a] != 0 || used[a] == stamp || work->deg[a] == 0) continue;
        int b = work->adj[a][rndint(work->deg[a])];
        if (used[b] == stamp || b >= n) continue;
        del_edge(work, a, b);
        add_edge(work, x, b);
        add_edge(work, y, a);
        used[a] = used[b] = stamp;
        k++;
    }
    return 1;
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
    t_end = t0 + limit * 0.92;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best;
    if (d < 1 || D < 1 || d > MAXD) { complete_bipartite(&best); print_graph(&best); return 0; }
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);

    if (D >= 2 && d >= 2 && best.n < moore_bound()) {
        double span = t_end - t0;
        cayley_phase(&best, t0 + span * 0.3);

        static Graph cur, work;
        copy_graph(&cur, &best);
        while (now() < t_end && cur.n + 2 <= moore_bound() && cur.n + 2 <= MAXN) {
            if (!grow2(&cur, &work)) break;
            double left = t_end - now();
            double slice = left * 0.3;
            if (slice < 2.0) slice = left;
            if (anneal(&work, now() + slice) && is_valid(&work)) {
                copy_graph(&cur, &work);
                if (work.n > best.n) copy_graph(&best, &work);
            }
        }
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
    best = start if start is not None else lib.haar_graph(d, range(d))   # K_{d,d}
    if not lib.is_valid(best[0], best[1], d, D):
        best = (2, [(0, 1)])   # a single edge: valid for any d >= 1, D >= 1
    budget = 0.88 * time_limit - (time.monotonic() - t0) - 1.5
    if best[0] >= lib.moore_bound(d, D):
        budget = min(budget, 0.5)   # nothing beats a Moore graph; just exercise the C engine
    if budget > 0.2:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, budget], stdin_graph=start, timeout=budget + 5)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except (RuntimeError, ValueError):
            pass   # keep the valid fallback
    return best
