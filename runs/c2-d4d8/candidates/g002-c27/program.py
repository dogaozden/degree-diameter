"""Voltage-lift search with a fast group-symmetric evaluator.

Every lift here is a bi-Cayley-type graph: vertex (block i, x) joined to (block j, x*g) for each dart
(i, j, g), where x*g is multiplication in a semidirect product Z_m x| Z_k. Left multiplication is an
automorphism, so the diameter check needs only 2p breadth-first searches (one per block representative)
instead of a full all-pairs bitset pass. That makes annealing over voltages roughly 100x faster than the
old bitset check. The fallback is the Python start graph, and every returned graph is checked with lib.
"""
import time

import lib

C_SOURCE = r'''
/* Group-lift annealing for bipartite degree-diameter graphs.
 *
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v" (valid start graph), or "0 0".
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * Method: choose a random group G = Z_m x|_r Z_k of order N and p base vertices per side. Build a
 * random d-regular base multigraph with p + p vertices and give each dart a voltage in G. The lift has
 * 2pN vertices. Left multiplication by G is an automorphism, so the diameter is at most D iff a BFS
 * from each of the 2p representatives A(i,e), B(j,e) reaches every vertex within D steps. Annealing
 * over voltages minimises the total number of unreached (source, vertex) pairs.
 */
#define _POSIX_C_SOURCE 200809L
#include <limits.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 4096
#define MAXD 32
#define MAXW (MAXN / 64)
#define MAXP 6
#define MAXDARTS (MAXD * MAXP)

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

static void add_edge(Graph *g, int u, int v) {
    g->adj[u][g->deg[u]++] = v;
    g->adj[v][g->deg[v]++] = u;
}

static int has_edge(const Graph *g, int u, int v) {
    for (int i = 0; i < g->deg[u]; i++)
        if (g->adj[u][i] == v) return 1;
    return 0;
}

/* Number of unordered pairs at distance > D (0 means diameter <= D). */
static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
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

/* Always valid fallback: K_{d,d} when D >= 2, a single edge otherwise. */
static void complete_bipartite(Graph *g) {
    int k = D >= 2 ? d : 1;
    g->n = 2 * k;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= k; }
    for (int a = 0; a < k; a++)
        for (int b = 0; b < k; b++) add_edge(g, a, k + b);
}

/* ------------------------------------------------------------------ groups */

/* G = Z_m x|_r Z_k, element (a, b) coded as a*k + b, product (a,b)(c,e) = (a + r^b c, b + e). */
static int GM, GK, GR, GN;
static int rp[MAXN]; /* rp[b] = r^b mod m */

static void set_group(int m, int k, int r) {
    GM = m; GK = k; GR = r; GN = m * k;
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
}

static int gmul(int x, int y) {
    int a = x / GK, b = x % GK, c = y / GK, e = y % GK;
    return (int)(((long)a + (long)rp[b] * c) % GM) * GK + (b + e) % GK;
}

static int ginv(int x) {
    int a = x / GK, b = x % GK;
    int nb = (GK - b) % GK;
    long t = ((long)rp[nb] * a) % GM;
    int na = (int)((GM - t) % GM);
    return na * GK + nb;
}

/* Uniformly random semidirect product of order N (m*k = N, gcd(r,m)=1, r^k = 1 mod m). */
static int random_group(int N) {
    long count = 0;
    int bm = 1, bk = N, br = 1;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        int rmax = m > 1 ? m : 2;
        for (int r = 1; r < rmax; r++) {
            if (m > 1 && gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            count++;
            if (rndint((int)count) == 0) { bm = m; bk = k; br = r; }
        }
    }
    set_group(bm, bk, br);
    return count > 0;
}

/* ------------------------------------------------------------------ lift state */

static int P, PN, NV, NL;
static int dI[MAXDARTS], dJ[MAXDARTS], dG[MAXDARTS];
static int permF[MAXDARTS][MAXN]; /* A(i,x) -> B(j, x*g) */
static int permB[MAXDARTS][MAXN]; /* B(j,y) -> A(i, y*g^-1) */
static int blkA[MAXP][MAXD], blkB[MAXP][MAXD];
static int nA[MAXP], nB[MAXP];
static int mark[MAXN], queue_[MAXN];
static int vstamp = 0;

static void set_dart(int t, int g) {
    int gi = ginv(g);
    dG[t] = g;
    for (int x = 0; x < GN; x++) {
        permF[t][x] = gmul(x, g);
        permB[t][x] = gmul(x, gi);
    }
}

/* True if voltage g on dart t clashes with an earlier dart (s < lim) on the same base pair. */
static int clashes(int t, int lim, int g) {
    for (int s = 0; s < lim; s++)
        if (s != t && dI[s] == dI[t] && dJ[s] == dJ[t] && dG[s] == g) return 1;
    return 0;
}

static int pick_voltage(int t, int lim) {
    for (int tries = 0; tries < 64; tries++) {
        int g = rndint(GN);
        if (!clashes(t, lim, g)) return g;
    }
    for (int g = 0; g < GN; g++)
        if (!clashes(t, lim, g)) return g;
    return -1;
}

/* Random d-regular base on p + p vertices (sum of d permutation matrices), then distinct voltages. */
static void init_lift_base(int p) {
    P = p;
    PN = p * GN;
    NV = 2 * PN;
    int M[MAXP][MAXP];
    memset(M, 0, sizeof M);
    for (int t = 0; t < d; t++) {
        int perm[MAXP];
        for (int i = 0; i < p; i++) perm[i] = i;
        for (int i = p - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int s = perm[i]; perm[i] = perm[j]; perm[j] = s;
        }
        for (int i = 0; i < p; i++) M[i][perm[i]]++;
    }
    NL = 0;
    for (int i = 0; i < p; i++) { nA[i] = 0; nB[i] = 0; }
    for (int i = 0; i < p; i++)
        for (int j = 0; j < p; j++)
            for (int c = 0; c < M[i][j]; c++) { dI[NL] = i; dJ[NL] = j; NL++; }
    for (int t = 0; t < NL; t++) {
        int g = pick_voltage(t, t);
        if (g < 0) g = 0;
        set_dart(t, g);
    }
    for (int t = 0; t < NL; t++) {
        blkA[dI[t]][nA[dI[t]]++] = t;
        blkB[dJ[t]][nB[dJ[t]]++] = t;
    }
}

/* BFS from src over the lift; returns the number of vertices NOT within distance D. */
static int bfs_unreached(int src) {
    if (vstamp == INT_MAX) { memset(mark, 0, sizeof mark); vstamp = 0; }
    int stamp = ++vstamp;
    int head = 0, tail = 0;
    queue_[tail++] = src;
    mark[src] = stamp;
    for (int dist = 0; dist < D && head < tail; dist++) {
        int lend = tail;
        while (head < lend) {
            int v = queue_[head++];
            if (v < PN) {
                int i = v / GN, x = v - i * GN;
                for (int q = 0; q < d; q++) {
                    int t = blkA[i][q];
                    int w = PN + dJ[t] * GN + permF[t][x];
                    if (mark[w] != stamp) { mark[w] = stamp; queue_[tail++] = w; }
                }
            } else {
                int y0 = v - PN, j = y0 / GN, y = y0 - j * GN;
                for (int q = 0; q < d; q++) {
                    int t = blkB[j][q];
                    int w = dI[t] * GN + permB[t][y];
                    if (mark[w] != stamp) { mark[w] = stamp; queue_[tail++] = w; }
                }
            }
        }
    }
    return NV - tail;
}

/* Total unreached (source, vertex) pairs over the 2P block representatives. */
static long full_cost(void) {
    long c = 0;
    for (int i = 0; i < P; i++) c += bfs_unreached(i * GN);
    for (int j = 0; j < P; j++) c += bfs_unreached(PN + j * GN);
    return c;
}

/* Anneal voltages until cost 0 (success) or the deadline passes. */
static int lift_anneal(double until) {
    long cost = full_cost();
    if (cost == 0) return 1;
    double start = now();
    double span = until - start;
    if (span <= 0) return 0;
    double T0 = 1.0 + cost / 100.0;
    double T = T0;
    long it = 0;
    while (cost > 0) {
        if ((++it & 31) == 0) {
            double tn = now();
            if (tn > until) return 0;
            T = T0 * (1.0 - (tn - start) / span) + 0.1;
        }
        int t = rndint(NL);
        int old = dG[t];
        int ng = pick_voltage(t, NL);
        if (ng < 0 || ng == old) continue;
        set_dart(t, ng);
        long nc = full_cost();
        if (nc <= cost || rnd01() < exp((double)(cost - nc) / T)) cost = nc;
        else set_dart(t, old);
    }
    return 1;
}

static void export_lift(Graph *g) {
    g->n = NV;
    for (int v = 0; v < NV; v++) { g->deg[v] = 0; g->side[v] = v >= PN; }
    for (int t = 0; t < NL; t++)
        for (int x = 0; x < GN; x++)
            add_edge(g, dI[t] * GN + x, PN + dJ[t] * GN + permF[t][x]);
}

/* Repeatedly try random groups and base graphs just above the current best order. */
static void lift_search(Graph *best, double until) {
    static Graph cand;
    long moore = moore_bound();
    long cap = moore < MAXN ? moore : MAXN;
    int fails = 0;
    while (now() < until) {
        int r = rndint(10);
        int p = r < 4 ? 1 : r < 7 ? 2 : r < 9 ? 3 : 4;
        if (p > MAXP) p = MAXP;
        long per = 2L * p;
        int bn = best->n;
        long N;
        if (bn == 0) {
            N = d + rndint(d + 1);
        } else {
            long baseN = (bn + per - 1) / per;
            N = baseN + 1 + rndint(1 + (int)(baseN / 50));
        }
        if (N > cap / per) N = cap / per;
        if (N < d || per * N <= bn) {
            if (++fails > 1000) return;
            continue;
        }
        random_group((int)N);
        init_lift_base(p);
        double slice = (until - now()) / 8.0;
        if (slice < 0.3) slice = 0.3;
        if (slice > 3.0) slice = 3.0;
        double attempt_end = now() + slice;
        if (attempt_end > until) attempt_end = until;
        if (lift_anneal(attempt_end)) {
            export_lift(&cand);
            if (cand.n > best->n && is_valid(&cand)) *best = cand;
        }
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

    static Graph best;
    if (d < 1 || D < 1 || d > MAXD) {
        complete_bipartite(&best);
        print_graph(&best);
        return 0;
    }
    read_start(&best);
    if (D >= 2 && d >= 2 && best.n < moore_bound()) lift_search(&best, t_end);
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


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    start = known_start(d, D)
    best = start if start is not None else lib.haar_graph(d, range(d))   # K_{d,d}
    if not lib.is_valid(*best, d, D):
        best = (2, [(0, 1)])   # safe fallback: a single edge (valid for D >= 1, d >= 1)

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if best[0] >= lib.moore_bound(d, D):
        budget = min(budget, 0.5)   # nothing beats a Moore graph; just exercise the C engine
    if budget > 0.2:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             stdin_graph=start, timeout=budget + 5)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best
