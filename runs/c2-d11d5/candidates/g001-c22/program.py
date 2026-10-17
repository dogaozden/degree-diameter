"""Bipartite degree-diameter search: Cayley-graph annealing with a two-BFS check.

New in this version:
  * Bipartite Cayley graphs over semidirect products Z_m x| Z_k. Vertices are (g, side),
    and (g, 0) ~ (g*s, 1) for s in a connection set S of size d. Left multiplication is an
    automorphism that preserves sides, so the diameter check needs only two BFS runs, from
    (1,0) and (1,1), instead of the all-pairs bitset check.
  * Simulated annealing over S. The cost is the number of vertices left unreached within D
    steps by those two BFS runs. Each move rewrites one neighbour column of a lookup table.
  * An adaptive ladder over the group order N. It jumps up while attempts succeed, halves
    the jump on failure, and retries N+1 near the frontier. The final graph is rebuilt and
    checked with lib-equivalent validity before it is returned.
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

#define MAXN 12000
#define MAXW (MAXN / 64 + 1)
#define MAXD 32
#define MAXH (MAXN / 2)

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

typedef struct {
    int m, k, r;
    int rp[MAXH]; /* rp[b] = r^b mod m */
} Grp;

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

/* ------------------------------------------------------------ full check */

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];

/* Number of unordered pairs at distance > D. Zero means diameter <= D (and connected). */
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

/* K_{1,1}: optimal when d = 1 or D = 1. */
static void single_edge(Graph *g) {
    g->n = 2;
    g->deg[0] = g->deg[1] = 0;
    g->side[0] = 0;
    g->side[1] = 1;
    add_edge(g, 0, 1);
}

/* ------------------------------------------------------------ groups */

/* Z_m x|_r Z_k: element (a, b) is a*k + b, and (a,b)(c,e) = (a + r^b c mod m, b + e mod k). */
static int gmul(const Grp *G, int x, int y) {
    int a = x / G->k, b = x % G->k, c = y / G->k, e = y % G->k;
    return (int)(((long)a + (long)G->rp[b] * c) % G->m) * G->k + (b + e) % G->k;
}

/* Inverse of (a, b) is (-r^(-b) a, -b). Since r^k = 1, r^(-b) = r^(k-b). */
static int ginv(const Grp *G, int x) {
    int a = x / G->k, b = x % G->k;
    int nb = (G->k - b) % G->k;
    long t = (long)G->rp[nb] * a % G->m;
    int na = (int)((G->m - t) % G->m);
    return na * G->k + nb;
}

/* Uniformly random factorisation N = m*k with r of order dividing k modulo m. */
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

/* ------------------------------------------------------------ Cayley search */

/* Bipartite Cayley graph: vertices g (side 0) and NN+g (side 1), with
 * (g,0) ~ (g*s,1) for s in SS. Neighbour table nbr[v*d + j]. */
static const Grp *CG;
static int NN, VV;
static int SS[MAXD], SI[MAXD];
static int nbr[MAXN * MAXD];
static int GA[MAXH], GB[MAXH];
static unsigned vis[MAXN];
static unsigned vstamp = 0;
static int qbuf[MAXN];
static int saved[MAXN];

static int in_set(int s, int upto) {
    for (int t = 0; t < upto; t++)
        if (SS[t] == s) return 1;
    return 0;
}

/* Rewrite neighbour column j from the current SS[j], SI[j]. */
static void set_column(int j) {
    const Grp *G = CG;
    int m = G->m, k = G->k;
    int s = SS[j], si = SI[j];
    int c = s / k, e = s % k;
    int ci = si / k, ei = si % k;
    for (int g = 0; g < NN; g++) {
        int a = GA[g], b = GB[g];
        int t = b + e; if (t >= k) t -= k;
        int ti = b + ei; if (ti >= k) ti -= k;
        int x = (int)(((long)a + (long)G->rp[b] * c) % m) * k + t;
        int y = (int)(((long)a + (long)G->rp[b] * ci) % m) * k + ti;
        nbr[(long)g * d + j] = NN + x;
        nbr[(long)(NN + g) * d + j] = y;
    }
}

/* BFS up to depth D; returns how many vertices are within D of src. */
static int reach_count(int src) {
    unsigned st = ++vstamp;
    int head = 0, tail = 0;
    vis[src] = st;
    qbuf[tail++] = src;
    for (int lev = 0; lev < D && head < tail; lev++) {
        int end = tail;
        while (head < end) {
            const int *row = nbr + (long)qbuf[head++] * d;
            for (int j = 0; j < d; j++) {
                int w = row[j];
                if (vis[w] != st) { vis[w] = st; qbuf[tail++] = w; }
            }
        }
    }
    return tail;
}

/* Two BFS runs cover all pairs: left multiplication is a side-preserving automorphism. */
static long eval_cost(void) {
    long a = VV - reach_count(0);
    long b = VV - reach_count(NN);
    return a + b;
}

/* Anneal the connection set on a random group of order N. Returns 1 on success. */
static int cayley_attempt(const Grp *G, int N, long steps, double until) {
    CG = G;
    NN = N;
    VV = 2 * N;
    for (int x = 0; x < N; x++) { GA[x] = x / G->k; GB[x] = x % G->k; }
    for (int j = 0; j < d; j++) {
        int s;
        do { s = rndint(N); } while (in_set(s, j));
        SS[j] = s;
        SI[j] = ginv(G, s);
    }
    for (int j = 0; j < d; j++) set_column(j);
    long f = eval_cost();
    for (long it = 0; it < steps && f > 0 && N > d; it++) {
        if ((it & 127) == 0 && now() > until) break;
        double T = 1.5 * pow(0.02, (double)it / (double)steps) + 0.02;
        int j = rndint(d);
        int s;
        do { s = rndint(N); } while (in_set(s, d));
        int olds = SS[j], oldsi = SI[j];
        for (int v = 0; v < VV; v++) saved[v] = nbr[(long)v * d + j];
        SS[j] = s;
        SI[j] = ginv(G, s);
        set_column(j);
        long f2 = eval_cost();
        if (f2 <= f || rnd01() < exp((double)(f - f2) / T)) {
            f = f2;
        } else {
            SS[j] = olds;
            SI[j] = oldsi;
            for (int v = 0; v < VV; v++) nbr[(long)v * d + j] = saved[v];
        }
    }
    return f == 0;
}

static int have_cayley = 0;
static Grp bestG;
static int bestN = 0;
static int bestS[MAXD];

/* Adaptive ladder over group orders N: jump up while attempts succeed, back off on failure. */
static void cayley_search(int start_n) {
    long moore = moore_bound();
    static Grp G;
    int cur = start_n / 2;
    if (cur < d) cur = d;
    int inc = cur / 50 + 1;
    while (now() < t_end) {
        int target = cur + inc;
        if (2L * target > moore || target > MAXH) {
            if (inc == 1) break;
            inc = 1;
            continue;
        }
        if (!random_group(target, &G)) break;
        long steps = 30000 + 10L * target;
        int ok = cayley_attempt(&G, target, steps, t_end);
        if (ok) {
            cur = target;
            bestG = G;
            bestN = target;
            memcpy(bestS, SS, sizeof(int) * d);
            have_cayley = 1;
            inc = inc * 2;
            if (inc > cur / 25 + 1) inc = cur / 25 + 1;
        } else {
            inc = inc / 2;
            if (inc < 1) inc = 1;
        }
    }
}

static void build_cayley(Graph *g, const Grp *G, int N, const int *S) {
    g->n = 2 * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= N; }
    for (int x = 0; x < N; x++)
        for (int j = 0; j < d; j++)
            add_edge(g, x, N + gmul(G, x, S[j]));
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
    t_end = t0 + limit * 0.88;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best, out;
    if (d < 1 || d > MAXD || D < 1) { printf("1 0\n"); return 0; }
    if (d == 1 || D == 1) { single_edge(&best); print_graph(&best); return 0; }

    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (!is_valid(&best)) complete_bipartite(&best);

    cayley_search(best.n);

    if (have_cayley && 2L * bestN > best.n) {
        build_cayley(&out, &bestG, bestN, bestS);
        if (is_valid(&out)) copy_graph(&best, &out);
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
    if not lib.is_valid(*best, d, D):
        best = (2, [(0, 1)])   # K_{1,1} is valid for any D >= 1
    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if best[0] >= lib.moore_bound(d, D):
        budget = min(budget, 0.5)   # nothing beats a Moore graph
    if budget > 0.5:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             stdin_graph=start, timeout=budget + 5)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(*out, d, D):
                best = out
        except (RuntimeError, ValueError):
            pass   # keep the valid fallback
    return best
