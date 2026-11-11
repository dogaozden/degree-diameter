"""Bi-Cayley search over semidirect products Z_m x| Z_k2, with BFS-based diameter checks.

Each bipartite Cayley graph Bi(G, S) on vertices a_g, b_h (a_g ~ b_{gs} for s in S) has
|S| = d. Left multiplication is an automorphism, so the diameter is checked from a_e and b_e only.
The C engine climbs upward in group order G from the best graph's size, annealing S for each G.
Python builds exact Moore/record graphs first and falls back to K_{d,d}; every result is validated.
"""
import time

import lib

C_SOURCE = r'''
/* Bi-Cayley group-connection-set search.
 * Usage: prog d D seed time_limit < start_graph
 * stdin: "n m" + m edges, or "0 0". stdout: "n m" + edges of the best valid graph.
 *
 * Group G = Z_m x|_r Z_k2 (element a*k2+b). Graph: a_g = g, b_h = G+h, edge a_g ~ b_{g*s}, s in S, |S| = d.
 * Distinct s gives simple d-regular bipartite graphs. Vertex-transitivity on each side means the
 * diameter is at most D iff BFS from a_e and from b_e reaches everything within D steps.
 * Simulated annealing on S (one element replaced per move) minimises the unreached count.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 9600
#define MAXD 32
#define MAXW ((MAXN + 63) / 64)
#define GCAP 2000
#define ITERS 8000

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

typedef struct {
    int m, k2, r;
} Grp;

static int d, D;
static double T_END;

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

static int gcd_int(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static long powmod(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    if (b < 0) b += m;
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

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];

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

static void complete_bipartite(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= d; }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

/* ------------------------------------------------------------ groups */

static int pick_group(int G, Grp *g) {
    int divs[128], nd = 0;
    for (int k = 1; k <= G && nd < 128; k++)
        if (G % k == 0) divs[nd++] = k;
    for (int att = 0; att < 400; att++) {
        int k2 = divs[rndint(nd)];
        int m = G / k2;
        int r = 1 % m;
        if (m >= 3 && k2 >= 2 && rndint(4) != 0) {
            r = 2 + rndint(m - 2);
            if (gcd_int(r, m) != 1 || powmod(r, k2, m) != 1 % m) continue;
        }
        g->m = m;
        g->k2 = k2;
        g->r = r;
        return 1;
    }
    return 0;
}

static int MT[GCAP * GCAP];
static int INV[GCAP];

/* Multiplication table and inverses for Z_m x|_r Z_k2 with element a*k2+b. */
static void build_group(const Grp *g, int *M, int *inv) {
    int m = g->m, k2 = g->k2, G = m * k2;
    static int rp[GCAP + 1];
    rp[0] = 1 % m;
    for (int b = 1; b < k2; b++) rp[b] = (int)((long)rp[b - 1] * g->r % m);
    for (int x = 0; x < G; x++) {
        int a = x / k2, b = x % k2;
        for (int y = 0; y < G; y++) {
            int c = y / k2, e = y % k2;
            long t = (a + (long)rp[b] * c) % m;
            M[(size_t)x * G + y] = (int)(t * k2 + (b + e) % k2);
        }
    }
    for (int x = 0; x < G; x++)
        for (int y = 0; y < G; y++)
            if (M[(size_t)x * G + y] == 0) { inv[x] = y; break; }
}

/* ------------------------------------------------------------ bi-Cayley search */

static int S[MAXD], Si[MAXD];
static int inS[GCAP];
static int distv[2 * GCAP], qu[2 * GCAP];

/* Unreached (source, vertex) pairs for sources a_e and b_e, with distances up to D. */
static long cost_of(int G) {
    long total = 0;
    int N = 2 * G;
    for (int src = 0; src < 2; src++) {
        int s0 = src ? G : 0;
        for (int i = 0; i < N; i++) distv[i] = -1;
        distv[s0] = 0;
        int head = 0, tail = 0;
        qu[tail++] = s0;
        while (head < tail) {
            int u = qu[head++];
            int du = distv[u];
            if (du >= D) continue;
            if (u < G) {
                const int *row = MT + (size_t)u * G;
                for (int i = 0; i < d; i++) {
                    int v = G + row[S[i]];
                    if (distv[v] < 0) { distv[v] = du + 1; qu[tail++] = v; }
                }
            } else {
                const int *row = MT + (size_t)(u - G) * G;
                for (int i = 0; i < d; i++) {
                    int v = row[Si[i]];
                    if (distv[v] < 0) { distv[v] = du + 1; qu[tail++] = v; }
                }
            }
        }
        total += N - tail;
    }
    return total;
}

static int sa_run(int G, int iters, double until) {
    for (int x = 0; x < G; x++) inS[x] = 0;
    for (int i = 0; i < d; i++) {
        int x;
        do { x = rndint(G); } while (inS[x]);
        inS[x] = 1;
        S[i] = x;
        Si[i] = INV[x];
    }
    long cost = cost_of(G);
    double c0 = (double)cost + 1.0;
    for (int t = 0; t < iters && cost > 0; t++) {
        if ((t & 63) == 0 && now() > until) break;
        double frac = 1.0 - (double)t / iters;
        double temp = 0.3 + 0.01 * c0 * frac;
        int i = rndint(d);
        int x = rndint(G);
        if (inS[x]) continue;
        int old = S[i];
        inS[old] = 0;
        inS[x] = 1;
        S[i] = x;
        Si[i] = INV[x];
        long c2 = cost_of(G);
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
        } else {
            inS[x] = 0;
            inS[old] = 1;
            S[i] = old;
            Si[i] = INV[old];
        }
    }
    return cost == 0;
}

static Graph best, cand;

static void graph_from_sol(int G, Graph *g) {
    g->n = 2 * G;
    for (int v = 0; v < g->n; v++) {
        g->deg[v] = 0;
        g->side[v] = (unsigned char)(v >= G);
    }
    for (int a = 0; a < G; a++)
        for (int i = 0; i < d; i++)
            add_edge(g, a, G + MT[(size_t)a * G + S[i]]);
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
    T_END = t0 + limit * 0.92;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 1) { printf("1 0\n"); return 0; }
    if (D == 1 || d > MAXD) { printf("2 1\n0 1\n"); return 0; }

    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);

    long moore = moore_bound();
    long gmax_l = moore / 2;
    if (gmax_l > GCAP) gmax_l = GCAP;
    int Gmax = (int)gmax_l;
    int Gmin = best.n / 2 + 1;
    if (Gmin < d) Gmin = d;
    int win = 3;

    while (now() < T_END && Gmin <= Gmax) {
        int G = Gmin + rndint(win);
        if (G > Gmax) G = Gmax;
        if (G < d) G = d;
        Grp grp;
        if (!pick_group(G, &grp)) { if (win < 40) win++; continue; }
        build_group(&grp, MT, INV);
        if (sa_run(G, ITERS, T_END)) {
            graph_from_sol(G, &cand);
            if (cand.n > best.n && is_valid(&cand)) {
                copy_graph(&best, &cand);
                Gmin = G + 1;
                win = 3;
                continue;
            }
        }
        if (win < 40) win++;
    }

    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


def _exact(d, D):
    """Best exact construction Python knows for (d, D): Moore graph or record-order graph, else None."""
    if D == 3:
        if d - 1 >= 2 and lib.is_prime_power(d - 1):
            return lib.projective_plane_incidence(d - 1)
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            return lib.araujo_lopez_graph(d - 2)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}: valid for D >= 2
    start = None
    try:
        ex = _exact(d, D)
    except ValueError:
        ex = None
    if ex is not None and ex[0] > best[0] and lib.is_valid(ex[0], ex[1], d, D):
        best = ex
        start = ex

    if best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.85 * time_limit - 2.5 - (time.monotonic() - t0)
    if budget < 1.0:
        return best

    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=start, timeout=budget + 4)
        out = lib.parse_graph_text(text)
    except Exception:
        return best

    if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
        best = out
    return best
