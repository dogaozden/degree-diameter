"""Bipartite degree-diameter search, version 3 (for d=5, D=5 this version has no verified gain).

Changes from the previous version:
  1. Voltage lifts use base graphs with up to 6 vertices per side (previously 4), over cyclic
     and semidirect groups Z_m x| Z_k, with hill-climbing on the voltages.
  2. Growth by two: insert one vertex per side, rewire d-1 edges into the new vertices, then
     anneal degree-preserving 2-switches on the bad-pair count. Each attempt has its own time
     slice and restarts from the best graph so far.
  3. Robust fallbacks: K_{d,d} for D >= 2, K_2 for D = 1, and the Python-built start (projective
     plane or Araujo-Pardo-Lopez) whenever it is valid. Every return value is checked with
     lib.is_valid.
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

#define MAXN 1024
#define MAXD 16
#define MAXW (MAXN / 64)
#define MAXP 6
#define MAXDARTS (MAXP * MAXD)

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN]; /* 0 = part A, 1 = part B */
} Graph;

typedef struct {
    int m, k, r;
    int rp[MAXN]; /* rp[b] = r^b mod m */
} Grp;

typedef struct { int a1, b1, a2, b2; } Move;

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

/* ------------------------------------------------------------ distance check */

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];

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
        const uint64_t *s = cur + (size_t)v * W;
        int c = 0;
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

/* ------------------------------------------------------------ groups */

/* Z_m x|_r Z_k: element (a, b) is the int a*k + b, (a,b)(c,e) = (a + r^b c mod m, b + e mod k). */
static int gmul(const Grp *G, int x, int y) {
    int a = x / G->k, b = x % G->k, c = y / G->k, e = y % G->k;
    return (int)(((long)a + (long)G->rp[b] * c) % G->m) * G->k + (b + e) % G->k;
}

/* Uniformly random (m, k, r) with m*k = N, gcd(r, m) = 1 and r^k = 1 mod m. */
static int random_group(int N, Grp *G) {
    long count = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        int rmax = m > 1 ? m : 2;
        for (int r = 1; r < rmax; r++) {
            if (m > 1 && gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            count++;
            if (rndint((int)count) == 0) { G->m = m; G->k = k; G->r = r; }
        }
    }
    if (!count) return 0;
    G->rp[0] = 1 % G->m;
    for (int b = 1; b < G->k; b++) G->rp[b] = (int)((long)G->rp[b - 1] * G->r % G->m);
    return 1;
}

/* ------------------------------------------------------------ voltage lifts */

/* Lift over a base with p vertices per side: A-vertex i has one dart per permutation t,
 * to base B-vertex dJ, with voltage dG. Result has 2pN vertices, regular of degree d.
 * Returns 0 if two darts give the same edge. */
static int build_lift(Graph *g, int p, int N, const Grp *G,
                      const int *dI, const int *dJ, const int *dG, int nd) {
    g->n = 2 * p * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= p * N; }
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++) {
            int a = dI[t] * N + x;
            int b = p * N + dJ[t] * N + gmul(G, x, dG[t]);
            if (has_edge(g, a, b)) return 0;
            add_edge(g, a, b);
        }
    return 1;
}

static long lift_cost(Graph *g, int p, int N, const Grp *G,
                      const int *dI, const int *dJ, const int *dG, int nd) {
    if (!build_lift(g, p, N, G, dI, dJ, dG, nd)) return 1000000000L;
    return bad_pairs(g);
}

/* Random base permutations, then hill-climb the voltages to zero bad pairs. */
static int lift_try(Graph *g, int p, int N, const Grp *G, int steps, double until) {
    int dI[MAXDARTS], dJ[MAXDARTS], dG[MAXDARTS];
    int perm[MAXP];
    int nd = 0;
    for (int t = 0; t < d; t++) {
        for (int i = 0; i < p; i++) perm[i] = i;
        for (int i = p - 1; i > 0; i--) {
            int j = rndint(i + 1), s = perm[i];
            perm[i] = perm[j];
            perm[j] = s;
        }
        for (int i = 0; i < p; i++) {
            dI[nd] = i;
            dJ[nd] = perm[i];
            dG[nd] = rndint(N);
            nd++;
        }
    }
    long cur = lift_cost(g, p, N, G, dI, dJ, dG, nd);
    for (int s = 0; s < steps && cur > 0; s++) {
        if ((s & 15) == 0 && now() > until) break;
        int t = rndint(nd);
        int old = dG[t];
        dG[t] = rndint(N);
        long nb = lift_cost(g, p, N, G, dI, dJ, dG, nd);
        if (nb <= cur || rnd01() < 0.01) cur = nb;
        else dG[t] = old;
    }
    if (lift_cost(g, p, N, G, dI, dJ, dG, nd) != 0) return 0;
    return is_valid(g);
}

static void lift_search(Graph *best, double until) {
    static Graph cand;
    static Grp G;
    long moore = moore_bound();
    int fails = 0;
    while (now() < until) {
        int r = rndint(12);
        int p = r < 2 ? 1 : r < 4 ? 2 : r < 7 ? 3 : r < 10 ? 4 : r < 11 ? 5 : 6;
        long target = best->n + 2;
        long N = (target + 2L * p - 1) / (2L * p) + rndint(2);
        if (best->n == 0) N = d + rndint(3);
        if (N < d) N = d;
        if (2L * p * N > moore || 2L * p * N > MAXN) {
            if (++fails > 2000) return;
            continue;
        }
        if (!random_group((int)N, &G)) continue;
        int steps = 200 + (int)(400000 / (2L * p * N));
        if (lift_try(&cand, p, (int)N, &G, steps, until) && cand.n > best->n)
            *best = cand;
    }
}

/* ------------------------------------------------------------ 2-switch annealing */

static int propose(const Graph *g, Move *m) {
    int n = g->n;
    int v = rndint(n), w = rndint(n);
    if (g->deg[v] == 0 || g->deg[w] == 0) return 0;
    int u = g->adj[v][rndint(g->deg[v])];
    int x = g->adj[w][rndint(g->deg[w])];
    if (g->side[v] == 0) { m->a1 = v; m->b1 = u; } else { m->a1 = u; m->b1 = v; }
    if (g->side[w] == 0) { m->a2 = w; m->b2 = x; } else { m->a2 = x; m->b2 = w; }
    if (m->a1 == m->a2 || m->b1 == m->b2) return 0;
    if (has_edge(g, m->a1, m->b2) || has_edge(g, m->a2, m->b1)) return 0;
    return 1;
}

static void apply_move(Graph *g, const Move *m) {
    del_edge(g, m->a1, m->b1);
    del_edge(g, m->a2, m->b2);
    add_edge(g, m->a1, m->b2);
    add_edge(g, m->a2, m->b1);
}

static void undo_move(Graph *g, const Move *m) {
    del_edge(g, m->a1, m->b2);
    del_edge(g, m->a2, m->b1);
    add_edge(g, m->a1, m->b1);
    add_edge(g, m->a2, m->b2);
}

/* Metropolis anneal of degree-preserving 2-switches on the bad-pair count.
 * Returns the final bad-pair count (0 means valid diameter). */
static long anneal(Graph *g, double until) {
    long bad = bad_pairs(g);
    double T = 1.0;
    Move m;
    for (long it = 1; bad > 0; it++) {
        if ((it & 31) == 0 && now() > until) break;
        if (!propose(g, &m)) continue;
        apply_move(g, &m);
        long nb = bad_pairs(g);
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) bad = nb;
        else undo_move(g, &m);
        T *= 0.9995;
        if (T < 0.05) T = 1.0;
    }
    return bad;
}

/* Insert one vertex per side (each of degree d) by rewiring d-1 edges of src. */
static void grow2(const Graph *src, Graph *w) {
    static int used[MAXN];
    static int stamp = 0;
    int n = src->n;
    *w = *src;
    int x = n, y = n + 1;
    w->n = n + 2;
    w->deg[x] = w->deg[y] = 0;
    w->side[x] = 0;
    w->side[y] = 1;
    add_edge(w, x, y);
    stamp++;
    used[x] = used[y] = stamp;
    int k = 0;
    for (int tries = 0; k < d - 1 && tries < 100000; tries++) {
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

static void grow_search(Graph *best, double until) {
    static Graph w;
    long moore = moore_bound();
    while (now() < until) {
        if (best->n + 2 > moore || best->n + 2 > MAXN) return;
        double left = until - now();
        double slice = left / 6.0;
        if (slice < 3.0) slice = 3.0;
        if (slice > left) slice = left;
        grow2(best, &w);
        if (anneal(&w, now() + slice) == 0 && is_valid(&w)) *best = w;
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

    if (d < 1 || D < 1 || d > MAXD) { printf("0 0\n"); return 0; }
    if (D == 1) { printf("2 1\n0 1\n"); return 0; }

    static Graph best;
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);

    if (best.n < moore_bound()) {
        double span = t_end - t0;
        lift_search(&best, t0 + span * 0.30);
        grow_search(&best, t_end);
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


def _safe_fallback(d, D):
    """A valid graph that needs no search: K_{d,d} for D >= 2, a single edge for D = 1."""
    if D == 1:
        return (2, [(0, 1)])
    cand = lib.haar_graph(d, range(d))   # K_{d,d}
    if lib.is_valid(*cand, d, D):
        return cand
    return (2, [(0, 1)])


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    fallback = _safe_fallback(d, D)
    start = None
    try:
        s = known_start(d, D)
        if s is not None and lib.is_valid(*s, d, D):
            start = s
    except Exception:
        start = None
    best = start if start is not None else fallback

    # The C engine covers D >= 2 and d <= 16; other cases keep the valid fallback.
    if D < 2 or d < 1 or d > 16:
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if best[0] >= lib.moore_bound(d, D):
        budget = min(budget, 0.5)   # Moore graph: nothing to beat
    if budget > 0.2:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             stdin_graph=start, timeout=budget + 5)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(*out, d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best
