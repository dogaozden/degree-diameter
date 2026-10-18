"""Cayley-graph search for bipartite degree-diameter graphs, with a lift fallback.

Phase 1 (new idea): Haar-type Cayley graphs. For a group G of order N and a
connection set S = {1, s_2, ..., s_d}, put A-vertices g and B-vertices h with edge
(g, h) iff h = g*s. Left multiplication by G is an automorphism that is transitive on
each side, so the diameter equals max(ecc(A_1), ecc(B_1)). Each candidate therefore
costs two BFS passes over 2N vertices instead of a full bitset all-pairs check.
Groups are semidirect products Z_m x| Z_k, so sampling is cheap and very wide.

Phase 2: voltage lifts over 2-3 base vertices per side, with hill-climbing on the
voltages (general bitset diameter check).

Safety: build() starts from the best known construction and returns the larger graph
only if lib.is_valid accepts it, so a failed search can only cost time.
"""
import time

import lib

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 600
#define MAXV 1200
#define MAXD 16
#define MAXP 3
#define MAXW (MAXV / 64 + 1)

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

/* ------------------------------------------------------------ graphs */

typedef struct {
    int n;
    int deg[MAXV];
    int adj[MAXV][MAXD];
} Graph;

static Graph best; /* best valid graph so far; n == 0 means none */

static void add_edge(Graph *g, int u, int v) {
    g->adj[u][g->deg[u]++] = v;
    g->adj[v][g->deg[v]++] = u;
}

static uint64_t RA[MAXV * MAXW], RB[MAXV * MAXW];

/* Number of unordered pairs at distance > D. */
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
        uint64_t *t = cur; cur = nxt; nxt = t;
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

static int is_bipartite(const Graph *g) {
    static int col[MAXV], q[MAXV];
    for (int v = 0; v < g->n; v++) col[v] = -1;
    for (int s = 0; s < g->n; s++) {
        if (col[s] >= 0) continue;
        int head = 0, tail = 0;
        col[s] = 0;
        q[tail++] = s;
        while (head < tail) {
            int v = q[head++];
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[v][i];
                if (col[u] < 0) { col[u] = 1 - col[v]; q[tail++] = u; }
                else if (col[u] == col[v]) return 0;
            }
        }
    }
    return 1;
}

static int graph_ok(const Graph *g) {
    if (g->n <= 0 || g->n > MAXV) return 0;
    for (int v = 0; v < g->n; v++) {
        if (g->deg[v] > d) return 0;
        for (int i = 0; i < g->deg[v]; i++) {
            int u = g->adj[v][i];
            if (u < 0 || u >= g->n || u == v) return 0;
            for (int j = 0; j < i; j++)
                if (g->adj[v][j] == u) return 0;
        }
    }
    if (!is_bipartite(g)) return 0;
    return bad_pairs(g) == 0;
}

static void print_graph(const Graph *g) {
    if (g->n <= 0) { printf("0 0\n"); return; }
    long m = 0;
    for (int u = 0; u < g->n; u++)
        for (int i = 0; i < g->deg[u]; i++)
            if (u < g->adj[u][i]) m++;
    printf("%d %ld\n", g->n, m);
    for (int u = 0; u < g->n; u++)
        for (int i = 0; i < g->deg[u]; i++)
            if (u < g->adj[u][i]) printf("%d %d\n", u, g->adj[u][i]);
}

/* ------------------------------------------------------------ groups Z_m x| Z_k */

typedef struct {
    int m, k, r;
    int rp[MAXN]; /* rp[b] = r^b mod m */
} Grp;

/* element (a, b) is coded a*k + b; (a,b)(c,e) = (a + r^b c, b + e) */
static int gmul(const Grp *G, int x, int y) {
    int a = x / G->k, b = x % G->k, c = y / G->k, e = y % G->k;
    long ta = ((long)a + (long)G->rp[b] * c) % G->m;
    int tb = (b + e) % G->k;
    return (int)ta * G->k + tb;
}

/* inverse of (a, b) is (-r^(-b) a, -b), and r^(-b) = r^(k-b) */
static int ginv(const Grp *G, int x) {
    int a = x / G->k, b = x % G->k;
    int nb = (G->k - b) % G->k;
    long t = (long)G->rp[nb] * a % G->m;
    long na = (G->m - t) % G->m;
    return (int)na * G->k + nb;
}

/* Uniform random (m, k, r) with m*k = N, gcd(r, m) = 1 and r^k = 1 mod m. */
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
    for (int b = 1; b < G->k; b++)
        G->rp[b] = (int)((long)G->rp[b - 1] * G->r % G->m);
    return 1;
}

/* ------------------------------------------------------------ Cayley (Haar-type) search */

/* Vertex layout: A-vertex g is g, B-vertex h is N + h. Edge A g ~ B (g * s), s in S.
 * Left multiplication is an automorphism transitive on each side, so the diameter is
 * max(ecc(A identity), ecc(B identity)): two BFS passes suffice. */
static int nb_tab[2 * MAXN][MAXD];
static int dist_[2 * MAXN], qbuf[2 * MAXN];

static void cayley_tab(const Grp *G, int N, const int *S, const int *Si) {
    for (int g = 0; g < N; g++)
        for (int t = 0; t < d; t++) nb_tab[g][t] = N + gmul(G, g, S[t]);
    for (int h = 0; h < N; h++)
        for (int t = 0; t < d; t++) nb_tab[N + h][t] = gmul(G, h, Si[t]);
}

static int reach_all(int V, int src) {
    for (int v = 0; v < V; v++) dist_[v] = -1;
    int head = 0, tail = 0;
    dist_[src] = 0;
    qbuf[tail++] = src;
    while (head < tail) {
        int v = qbuf[head++];
        if (dist_[v] >= D) continue;
        for (int t = 0; t < d; t++) {
            int u = nb_tab[v][t];
            if (dist_[u] < 0) { dist_[u] = dist_[v] + 1; qbuf[tail++] = u; }
        }
    }
    return tail == V;
}

static void cayley_search(double until) {
    static Graph cand;
    static int S[MAXD], Si[MAXD];
    long moore = moore_bound();
    while (now() < until) {
        int lo = best.n / 2 + 1;
        if (lo < d) lo = d;
        int N = lo + rndint(6);
        if (N > MAXN || 2L * N > moore) {
            N = lo;
            if (N > MAXN || 2L * N > moore) return;
        }
        Grp G;
        if (!random_group(N, &G)) continue;
        S[0] = 0; /* identity: WLOG 1 in S */
        int ok = 1;
        for (int t = 1; t < d && ok; t++) {
            int x = 0, fresh = 0, tries = 0;
            while (!fresh && tries++ < 1000) {
                x = 1 + rndint(N - 1);
                fresh = 1;
                for (int s = 0; s < t; s++)
                    if (S[s] == x) { fresh = 0; break; }
            }
            if (!fresh) ok = 0;
            else S[t] = x;
        }
        if (!ok) continue;
        for (int t = 0; t < d; t++) Si[t] = ginv(&G, S[t]);
        cayley_tab(&G, N, S, Si);
        if (reach_all(2 * N, 0) && reach_all(2 * N, N)) {
            cand.n = 2 * N;
            for (int v = 0; v < cand.n; v++) cand.deg[v] = 0;
            for (int g = 0; g < N; g++)
                for (int t = 0; t < d; t++)
                    add_edge(&cand, g, N + gmul(&G, g, S[t]));
            if (cand.n > best.n && graph_ok(&cand)) best = cand;
        }
    }
}

/* ------------------------------------------------------------ voltage lifts, p = 2..3 */

typedef struct { int i, j, g; } Dart;

static int fresh(const Dart *dt, int nd, int skip, int i, int j, int N) {
    for (;;) {
        int g = rndint(N), clash = 0;
        for (int t = 0; t < nd; t++)
            if (t != skip && dt[t].i == i && dt[t].j == j && dt[t].g == g) { clash = 1; break; }
        if (!clash) return g;
    }
}

static void lift_build(Graph *g, int p, int N, const Grp *G, const Dart *dt, int nd) {
    g->n = 2 * p * N;
    for (int v = 0; v < g->n; v++) g->deg[v] = 0;
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, dt[t].i * N + x, p * N + dt[t].j * N + gmul(G, x, dt[t].g));
}

static void lift_phase(double until) {
    static Graph cand;
    static Grp G;
    static Dart dt[MAXD * MAXP];
    long moore = moore_bound();
    while (now() < until) {
        int p = 2 + rndint(2);
        int target = best.n + 2 + rndint(24);
        int N = (target + 2 * p - 1) / (2 * p);
        if (N < d + 1) N = d + 1;
        if (N > MAXN || 2L * p * N > MAXV || 2L * p * N > moore) continue;
        if (!random_group(N, &G)) continue;
        int nd = 0;
        for (int t = 0; t < d; t++) {
            int perm[MAXP];
            for (int i = 0; i < p; i++) perm[i] = i;
            for (int i = p - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int s = perm[i]; perm[i] = perm[j]; perm[j] = s;
            }
            for (int i = 0; i < p; i++) {
                dt[nd].i = i;
                dt[nd].j = perm[i];
                dt[nd].g = 0;
                nd++;
            }
        }
        for (int t = 0; t < nd; t++)
            dt[t].g = fresh(dt, t, -1, dt[t].i, dt[t].j, N);
        lift_build(&cand, p, N, &G, dt, nd);
        long bad = bad_pairs(&cand);
        for (int s = 0; s < 400 && bad > 0; s++) {
            if ((s & 7) == 0 && now() > until) break;
            int t = rndint(nd);
            int old = dt[t].g;
            dt[t].g = fresh(dt, nd, t, dt[t].i, dt[t].j, N);
            lift_build(&cand, p, N, &G, dt, nd);
            long nb = bad_pairs(&cand);
            if (nb <= bad || rnd01() < 0.02) bad = nb;
            else dt[t].g = old;
        }
        if (bad == 0 && cand.n > best.n && graph_ok(&cand)) best = cand;
    }
}

/* ------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit\n", argv[0]);
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

    best.n = 0;
    if (d < 2 || d > MAXD || D < 2) { print_graph(&best); return 0; }

    /* trivial fallback: K_{d,d} has diameter 2 */
    {
        static Graph kb;
        kb.n = 2 * d;
        for (int v = 0; v < kb.n; v++) kb.deg[v] = 0;
        for (int a = 0; a < d; a++)
            for (int b = 0; b < d; b++) add_edge(&kb, a, d + b);
        if (graph_ok(&kb)) best = kb;
    }

    if (best.n < moore_bound()) {
        double split = t0 + (t_end - t0) * 0.6;
        cayley_search(split);
        lift_phase(t_end);
    }
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
    if start is None:
        start = lib.haar_graph(d, range(d))           # K_{d,d}
    best = start
    if not lib.is_valid(best[0], best[1], d, D):
        best = (2, [(0, 1)])                           # K_2 is valid for any d >= 1, D >= 1

    if best[0] < lib.moore_bound(d, D):
        budget = 0.85 * time_limit - (time.monotonic() - t0) - 2.0
        if budget > 1.0:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                                 stdin_graph=None, timeout=budget + 8)
                n, edges = lib.parse_graph_text(text)
                if n > best[0] and lib.is_valid(n, edges, d, D):
                    best = (n, edges)
            except (RuntimeError, ValueError):
                pass   # keep the valid fallback
    return best
