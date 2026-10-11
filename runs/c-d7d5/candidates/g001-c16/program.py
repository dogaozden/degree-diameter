"""Voltage-lift annealing over semidirect-product groups, with a validated fallback chain.

Changed from the parent: the C engine no longer hill-climbs random lifts. Each attempt picks a
random base (p vertices per side, d permutation darts), a random group Z_m x| Z_k of order
N with 2pN near the target, and anneals the voltages (and occasionally a permutation) against the
cost  bad_pairs + DUP_PEN * duplicate_edges. Success at cost 0 raises the target by two vertices.
Python always keeps a validated fallback, so a C failure costs only search time.
"""
import time

import lib

C_SOURCE = r'''
/* Voltage-lift annealing over semidirect products Z_m x|_r Z_k.
 *
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v": a valid start graph, or "0 0".
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * A lift has base: d permutation matrices on p+p vertices (p in 1..4), darts (t,i) with
 * voltage volt[t*p+i]. The lift has 2pN vertices, is d-regular, bipartite by construction.
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
#define MAXP 4
#define DUP_PEN 20.0

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static double t_end;
static Graph best;

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

static void complete_bipartite(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= d; }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

/* ------------------------------------------------------------------ distance check */

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];

/* Unordered pairs at distance > D (unreachable pairs included). 0 means valid diameter. */
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

/* Always-valid fallback chain: K_{d,d} (if D >= 2), then K_{1,1}, then one vertex. */
static void fallback(Graph *g) {
    if (d >= 1 && d <= MAXD) {
        complete_bipartite(g);
        if (is_valid(g)) return;
    }
    g->n = 2;
    g->deg[0] = g->deg[1] = 0;
    g->side[0] = 0;
    g->side[1] = 1;
    add_edge(g, 0, 1);
    if (is_valid(g)) return;
    g->n = 1;
    g->deg[0] = 0;
    g->side[0] = 0;
}

/* ------------------------------------------------------------------ groups */

/* Z_m x|_r Z_k: element (a, b) is the int a*k + b; (a,b)(c,e) = (a + r^b c mod m, b + e mod k). */
typedef struct {
    int m, k, r;
    int rp[MAXN]; /* rp[b] = r^b mod m */
} Grp;

static int gmul(const Grp *G, int x, int y) {
    int a = x / G->k, b = x % G->k, c = y / G->k, e = y % G->k;
    return (int)((a + (long)G->rp[b] * c) % G->m) * G->k + (b + e) % G->k;
}

/* Uniform random (m, k, r) with m*k = N, gcd(r, m) = 1, r^k = 1 mod m (reservoir sampling). */
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
            if (rndint((int)count) == 0) {
                G->m = m; G->k = k; G->r = r;
                found = 1;
            }
        }
    }
    if (!found) return 0;
    G->rp[0] = 1 % G->m;
    for (int b = 1; b < G->k; b++) G->rp[b] = (int)((long)G->rp[b - 1] * G->r % G->m);
    return 1;
}

/* ------------------------------------------------------------------ voltage lifts */

static int perm[MAXD][MAXP];   /* perm[t][i] = B-vertex hit by A-vertex i in permutation t */
static int volt[MAXD * MAXP];  /* dart e = t*p + i has voltage volt[e] */
static long dup_count;
static Graph work;

static void random_perm(int *row, int p) {
    for (int i = 0; i < p; i++) row[i] = i;
    for (int i = p - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int s = row[i]; row[i] = row[j]; row[j] = s;
    }
}

static void build_lift(Graph *g, int p, int N, const Grp *G) {
    g->n = 2 * p * N;
    dup_count = 0;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= p * N; }
    for (int t = 0; t < d; t++)
        for (int i = 0; i < p; i++) {
            int j = perm[t][i];
            int e = t * p + i;
            for (int x = 0; x < N; x++) {
                int a = i * N + x;
                int b = p * N + j * N + gmul(G, x, volt[e]);
                if (has_edge(g, a, b)) dup_count++;
                else add_edge(g, a, b);
            }
        }
}

/* Anneal voltages (and occasionally permutations) until the lift has cost 0. */
static int anneal(Graph *out, int p, int N, const Grp *G, double until) {
    int nd = d * p;
    for (int t = 0; t < d; t++) random_perm(perm[t], p);
    for (int e = 0; e < nd; e++) volt[e] = rndint(N);
    build_lift(&work, p, N, G);
    double cost = (double)bad_pairs(&work) + DUP_PEN * dup_count;
    double T = 2.0;
    long it = 0;
    for (;;) {
        if (cost == 0.0) {
            build_lift(&work, p, N, G);
            if (is_valid(&work)) { copy_graph(out, &work); return 1; }
            return 0;
        }
        if ((++it & 7) == 0 && now() > until) return 0;

        int e = rndint(nd);
        int t = e / p;
        int oldv = volt[e];
        int oldp[MAXP];
        int moved_perm = 0;
        if (p > 1 && rnd01() < 0.03) {
            memcpy(oldp, perm[t], sizeof oldp);
            random_perm(perm[t], p);
            moved_perm = 1;
        } else {
            volt[e] = rndint(N);
            if (volt[e] == oldv) continue;
        }

        build_lift(&work, p, N, G);
        double nc = (double)bad_pairs(&work) + DUP_PEN * dup_count;
        if (nc <= cost || rnd01() < exp(-(nc - cost) / T)) {
            cost = nc;
        } else {
            if (moved_perm) memcpy(perm[t], oldp, sizeof oldp);
            else volt[e] = oldv;
        }
        T *= 0.999;
        if (T < 0.15) T = 2.0;
    }
}

static void lift_search(double until) {
    static Graph cand;
    static Grp G;
    long moore = moore_bound();
    int fails = 0;
    while (now() < until) {
        int p = 1 + rndint(MAXP);
        long target = (long)best.n + 2;
        if (target < 2L * d) target = 2L * d;
        long N = (target + 2 * p - 1) / (2 * p) + rndint(2);
        if (N < 1) N = 1;
        if (2L * p * N > moore || 2L * p * N > MAXN) {
            if (++fails > 1000) return;
            continue;
        }
        if (!random_group((int)N, &G)) {
            if (++fails > 1000) return;
            continue;
        }
        double rem = until - now();
        double slice = rem / 5.0;
        if (slice < 2.0) slice = rem;
        if (slice > 10.0) slice = 10.0;
        if (anneal(&cand, p, (int)N, &G, now() + slice) && cand.n > best.n)
            copy_graph(&best, &cand);
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
    t_end = t0 + limit * 0.92;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 1 || d > MAXD) {
        best.n = 1; best.deg[0] = 0; best.side[0] = 0;
        print_graph(&best);
        return 0;
    }

    read_start(&best);
    if (D >= 2 && best.n < moore_bound()) lift_search(t_end);
    if (best.n == 0 || !is_valid(&best)) fallback(&best);
    print_graph(&best);
    return 0;
}
'''


def known_start(d, D):
    """Best graph Python can build directly for (d, D), or None."""
    try:
        if D == 3 and lib.is_prime_power(d - 1):
            return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
        if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
            return lib.araujo_lopez_graph(d - 2)           # record graphs of order 2(q^2+q+5)
    except Exception:
        return None
    return None


def _fallback(d, D):
    """Largest simple always-valid graph we can name cheaply."""
    candidates = []
    try:
        candidates.append(lib.haar_graph(d, range(d)))     # K_{d,d}
    except Exception:
        pass
    candidates += [(2, [(0, 1)]), (1, [])]
    for g in candidates:
        if lib.is_valid(g[0], g[1], d, D):
            return g
    return (1, [])


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    start = known_start(d, D)
    if start is not None and not lib.is_valid(start[0], start[1], d, D):
        start = None
    best = start if start is not None else _fallback(d, D)

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.5
    if best[0] >= lib.moore_bound(d, D):
        budget = min(budget, 0.5)   # nothing beats a Moore graph; just exercise the C engine
    if budget > 0.2:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             stdin_graph=start, timeout=budget + 8)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass   # keep the validated fallback
    return best
