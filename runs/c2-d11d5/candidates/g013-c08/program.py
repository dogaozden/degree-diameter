"""Bi-Cayley voltage-lift annealer in C, plus grow-by-two, under an order ladder in Python.

New in this version: the voltage-lift search runs in C ("lift" mode) instead of numpy.
Groups are Z_m x| Z_k2 and the base has K blocks per side. Each of the d layers is a
permutation of the blocks with a group voltage. Left multiplication by any group element is
an automorphism that preserves blocks, so the check reduces to distances from the 2K block
representatives. Each layer's voltage or permutation is changed incrementally. Moves are
guided by unreached representatives, and the search restarts when it stalls.

The C "grow" mode (grow-by-two with annealed edge swaps) is applied to the best graph.
Every returned graph is checked with lib.is_valid. K_{d,d} is the fallback.
"""
import itertools
import math
import random
import time

import lib


C_SOURCE = r'''
/* Two modes, chosen by argv[1]:
 *   lift d D seed time K M K2 R : anneal a bi-Cayley lift over Z_M x| Z_K2 (R^K2 = 1 mod M)
 *                                 with K blocks per side. Prints the first valid lift found,
 *                                 or "0 0".
 *   grow d D seed time < graph  : grow-by-two from a valid start graph; prints the best graph.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 8192
#define MAXD 32
#define MAXK 8
#define MAXW (MAXN / 64)
#define MAXPW 256

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static uint64_t rng_state = 88172645463325252ULL;
static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static int badv[MAXN];

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

/* Number of unordered pairs at distance > D; also sets badv[v]. */
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

static double t_end;
static Graph gbest, gwork;
static int used[MAXN];
static int stamp = 0;

/* One grow-by-two attempt starting from best; on success work holds n+2 valid vertices. */
static int grow_once(const Graph *best, Graph *work, double until) {
    int n = best->n;
    if (n + 2 > moore_bound() || n + 2 > MAXN) return 0;
    copy_graph(work, best);
    int x = n, y = n + 1;
    work->n = n + 2;
    work->deg[x] = work->deg[y] = 0;
    work->side[x] = 0;
    work->side[y] = 1;
    add_edge(work, x, y);
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
    long bad = bad_pairs(work);
    double T = 1.0;
    long it = 0;
    while (bad > 0) {
        if ((++it & 15) == 0 && now() > until) return 0;
        int v = rndint(work->n);
        for (int tries = 0; tries < 30 && badv[v] == 0; tries++) v = rndint(work->n);
        if (work->deg[v] == 0) continue;
        int u = work->adj[v][rndint(work->deg[v])];
        int s = rndint(work->n);
        if (work->side[s] != work->side[v] || s == v || work->deg[s] == 0) continue;
        int t = work->adj[s][rndint(work->deg[s])];
        if (t == u || has_edge(work, v, t) || has_edge(work, s, u)) continue;
        del_edge(work, v, u);
        del_edge(work, s, t);
        add_edge(work, v, t);
        add_edge(work, s, u);
        long nb2 = bad_pairs(work);
        if (nb2 <= bad || rnd01() < exp((double)(bad - nb2) / T)) {
            bad = nb2;
        } else {
            del_edge(work, v, t);
            del_edge(work, s, u);
            add_edge(work, v, u);
            add_edge(work, s, t);
        }
        T *= 0.9995;
        if (T < 0.05) T = 1.0;
    }
    return is_valid(work);
}

static void grow_search(double until) {
    while (now() < until && gbest.n + 2 <= moore_bound()) {
        double left = until - now();
        double slice = left < 4.0 ? left : (left / 4 > 4.0 ? left / 4 : 4.0);
        if (grow_once(&gbest, &gwork, now() + slice)) copy_graph(&gbest, &gwork);
    }
}

/* ------------------------------------------------------------------ lift mode */
/* Vertices: A block i, element g -> i*G + g (i < K); B block p, element h -> (K+p)*G + h.
 * Layer l sends A block i to B block perm[l][i] with voltage sv[l][i]:
 *   A_{i,g} ~ B_{perm, g*s}.
 * Left multiplication is an automorphism, so the check needs only the 2K representatives.
 */
static int K, G, M, K2, RR;
static int pw[MAXPW];
static int perm[MAXD][MAXK], iperm[MAXD][MAXK], sv[MAXD][MAXK];
static int nb[MAXD][MAXN];
static uint32_t BUF0[MAXN], BUF1[MAXN], SCR[MAXN];
static uint32_t *RC, *RN;

/* Group product in Z_M x| Z_K2, element (a,b) coded as a*K2+b, with (a,b)(c,e) = (a + r^b c, b+e). */
static int gmul(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, e = y % K2;
    return ((a + pw[b] * c) % M) * K2 + (b + e) % K2;
}

/* Inverse of (a,b) is (-r^(-b) a, -b). */
static int ginv(int x) {
    int a = x / K2, b = x % K2;
    int nbb = (K2 - b) % K2;
    int t = (pw[nbb] * a) % M;
    int ia = (M - t) % M;
    return ia * K2 + nbb;
}

static void update_layer(int l) {
    for (int i = 0; i < K; i++) iperm[l][perm[l][i]] = i;
    for (int i = 0; i < K; i++) {
        int s = sv[l][i], base = i * G, bb = (K + perm[l][i]) * G;
        for (int g = 0; g < G; g++) nb[l][base + g] = bb + gmul(g, s);
    }
    for (int p = 0; p < K; p++) {
        int i = iperm[l][p], si = ginv(sv[l][i]), bb = (K + p) * G;
        for (int h = 0; h < G; h++) nb[l][bb + h] = i * G + gmul(h, si);
    }
}

/* Sum over all vertices of the number of representatives not reached within D steps.
 * Writes the reach bitmask of every vertex into dst. */
static long eval_reach(uint32_t *dst) {
    int N = 2 * K * G;
    uint32_t *cur = dst, *nxt = SCR;
    for (int v = 0; v < N; v++) cur[v] = 0;
    for (int b = 0; b < 2 * K; b++) cur[b * G] = 1u << b;
    for (int t = 0; t < D; t++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint32_t x = cur[v];
            for (int l = 0; l < d; l++) x |= cur[nb[l][v]];
            nxt[v] = x;
            changed |= (x != cur[v]);
        }
        uint32_t *tmp = cur;
        cur = nxt;
        nxt = tmp;
        if (!changed) break;
    }
    if (cur != dst) memcpy(dst, cur, sizeof(uint32_t) * (size_t)N);
    long unreached = 0;
    for (int v = 0; v < N; v++) unreached += 2 * K - __builtin_popcount(dst[v]);
    return unreached;
}

/* Duplicate darts: same (block i, block p, voltage) in two layers. */
static long dup_count(void) {
    long c = 0;
    for (int l1 = 0; l1 < d; l1++)
        for (int l2 = l1 + 1; l2 < d; l2++)
            for (int i = 0; i < K; i++)
                if (perm[l1][i] == perm[l2][i] && sv[l1][i] == sv[l2][i]) c++;
    return c;
}

static long full_cost(uint32_t *dst) {
    return eval_reach(dst) + 50L * dup_count();
}

static void random_init(void) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < K; i++) perm[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = perm[l][i];
            perm[l][i] = perm[l][j];
            perm[l][j] = t;
        }
        for (int i = 0; i < K; i++) sv[l][i] = rndint(G);
        update_layer(l);
    }
}

static int accept_move(long nc, long cost, double T) {
    if (nc <= cost) return 1;
    return rnd01() < exp(-(double)(nc - cost) / T);
}

/* One annealing run from a random start. Returns 1 when a valid lift is found. */
static int anneal(double deadline) {
    int N = 2 * K * G;
    uint32_t FULL = (1u << (2 * K)) - 1u;
    long patience = 3000 + 2L * N;
    random_init();
    long cost = full_cost(RC);
    long best = cost, last = 0;
    double T = fmax(1.0, 0.05 * (double)cost);
    for (long it = 0; ; it++) {
        if (cost == 0) return 1;
        if ((it & 31) == 0 && now() > deadline) return 0;
        if (it - last > patience) return 0;
        T *= 0.9997;
        if (T < 0.3) T = 0.3;

        if (K >= 2 && rnd01() < 0.3) {
            /* Swap two block targets inside one layer (keeps it a permutation). */
            int l = rndint(d);
            int i1 = rndint(K), i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            int tmp = perm[l][i1];
            perm[l][i1] = perm[l][i2];
            perm[l][i2] = tmp;
            update_layer(l);
            long nc = full_cost(RN);
            if (accept_move(nc, cost, T)) {
                cost = nc;
                uint32_t *tp = RC; RC = RN; RN = tp;
                if (cost < best) { best = cost; last = it; }
            } else {
                tmp = perm[l][i1];
                perm[l][i1] = perm[l][i2];
                perm[l][i2] = tmp;
                update_layer(l);
            }
        } else {
            /* Change one voltage, preferably one that touches an unreached representative. */
            int l = rndint(d), i = rndint(K);
            if (rnd01() < 0.5) {
                int v = rndint(N);
                for (int tries = 0; tries < 30 && RC[v] == FULL; tries++) v = rndint(N);
                if (RC[v] != FULL) {
                    int blk = v / G;
                    if (blk < K) i = blk;
                    else i = iperm[l][blk - K];
                }
            }
            int old = sv[l][i], nw = rndint(G);
            if (nw == old) continue;
            sv[l][i] = nw;
            update_layer(l);
            long nc = full_cost(RN);
            if (accept_move(nc, cost, T)) {
                cost = nc;
                uint32_t *tp = RC; RC = RN; RN = tp;
                if (cost < best) { best = cost; last = it; }
            } else {
                sv[l][i] = old;
                update_layer(l);
            }
        }
    }
}

static int lift_search(double deadline) {
    while (now() < deadline) {
        if (anneal(deadline)) return 1;
    }
    return 0;
}

static int dup_before(int u, int l, int v) {
    for (int l2 = 0; l2 < l; l2++)
        if (nb[l2][u] == v) return 1;
    return 0;
}

static void print_lift(void) {
    int KG = K * G, N = 2 * K * G;
    long m = 0;
    for (int u = 0; u < KG; u++)
        for (int l = 0; l < d; l++)
            if (!dup_before(u, l, nb[l][u])) m++;
    printf("%d %ld\n", N, m);
    for (int u = 0; u < KG; u++)
        for (int l = 0; l < d; l++) {
            int v = nb[l][u];
            if (!dup_before(u, l, v)) printf("%d %d\n", u, v);
        }
}

static int lift_main(int argc, char **argv) {
    if (argc < 10) { printf("0 0\n"); return 0; }
    d = atoi(argv[2]);
    D = atoi(argv[3]);
    long seed = atol(argv[4]);
    double limit = atof(argv[5]);
    K = atoi(argv[6]);
    M = atoi(argv[7]);
    K2 = atoi(argv[8]);
    RR = atoi(argv[9]);
    if (d < 1 || d > MAXD || D < 2 || K < 1 || K > MAXK || M < 2 || K2 < 1 || K2 >= MAXPW) {
        printf("0 0\n");
        return 0;
    }
    G = M * K2;
    if (2L * K * G > MAXN) { printf("0 0\n"); return 0; }
    RR = ((RR % M) + M) % M;
    pw[0] = 1 % M;
    for (int t = 1; t <= K2; t++) pw[t] = (int)((long)pw[t - 1] * RR % M);
    if (pw[K2] != 1 % M) { printf("0 0\n"); return 0; }
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.2;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();
    RC = BUF0;
    RN = BUF1;
    if (lift_search(t_end)) print_lift();
    else printf("0 0\n");
    return 0;
}

static int grow_main(int argc, char **argv) {
    if (argc < 6) { printf("0 0\n"); return 0; }
    d = atoi(argv[2]);
    D = atoi(argv[3]);
    long seed = atol(argv[4]);
    double limit = atof(argv[5]);
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.2;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();
    if (d < 1 || D < 2 || d > MAXD) { printf("0 0\n"); return 0; }
    read_start(&gbest);
    if (gbest.n == 0) { printf("0 0\n"); return 0; }
    grow_search(t_end);
    if (!is_valid(&gbest)) { printf("0 0\n"); return 0; }
    print_graph(&gbest);
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 2) {
        fprintf(stderr, "usage: prog lift|grow ...\n");
        return 2;
    }
    if (strcmp(argv[1], "lift") == 0) return lift_main(argc, argv);
    if (strcmp(argv[1], "grow") == 0) return grow_main(argc, argv);
    printf("0 0\n");
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Small exact constructions.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


# ----------------------------------------------------------------------------
# Saturation: greedily add missing bipartite edges between deficient vertices.
# Distances only shrink, so validity is kept; callers still verify with lib.is_valid.
# ----------------------------------------------------------------------------

def _saturate(n, edges, d, D):
    """Greedily add missing bipartite edges between deficient vertices; returns (n, edges)."""
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            x = stack.pop()
            for y in adj[x]:
                if color[y] == -1:
                    color[y] = 1 - color[x]
                    stack.append(y)
    A = [v for v in range(n) if color[v] == 0 and len(adj[v]) < d]
    B = [v for v in range(n) if color[v] == 1 and len(adj[v]) < d]
    out = {(min(u, v), max(u, v)) for u, v in edges}
    for a in A:
        for b in B:
            if len(adj[a]) >= d:
                break
            if len(adj[b]) >= d or b in adj[a]:
                continue
            adj[a].add(b)
            adj[b].add(a)
            out.add((min(a, b), max(a, b)))
    return n, sorted(out)


def _safe_saturate(n, edges, d, D):
    """Saturate, but fall back to the input if anything goes wrong or the result is invalid."""
    try:
        sn, se = _saturate(n, edges, d, D)
        if lib.is_valid(sn, se, d, D):
            return sn, se
    except Exception:
        pass
    return n, edges


# ----------------------------------------------------------------------------
# Group sampling for Z_m x| Z_k2 (the C lift annealer does the rest).
# ----------------------------------------------------------------------------

_KS = (1, 2, 3, 4)


def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, -(-target // k2))
        if k2 == 1:
            r = 1
        elif k2 == 2 and rng.random() < 0.3:
            r = m - 1
            if math.gcd(r, m) != 1 or pow(r, 2, m) != 1 % m:
                continue
        else:
            r = None
            for _ in range(60):
                c = rng.randrange(2, m) if m > 2 else 1
                if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                    r = c
                    break
            if r is None:
                continue
        return m, k2, r
    return None


def _lift_c(d, D, seed, k, m, k2, r, budget):
    """Run the C lift annealer for one group; returns (n, edges) or None."""
    text = lib.run_c(C_SOURCE, ["lift", d, D, seed, round(budget, 2), k, m, k2, r],
                     stdin_graph=None, timeout=budget + 10.0)
    n, edges = lib.parse_graph_text(text)
    if n <= 0 or not edges:
        return None
    return n, edges


# ----------------------------------------------------------------------------
# build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    total = max(1.0, 0.85 * time_limit - 1.5)
    final = t0 + total
    rng = random.Random(seed)

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    def consider_saturated(n, e):
        sn, se = _safe_saturate(n, e, d, D)
        consider(sn, se)
        consider(n, e)

    # Exact constructions (calibration-style cases return immediately).
    if D >= 3:
        try:
            pg = _best_pg(d)
            if pg is not None:
                consider(pg[0], pg[1])
                if D == 3 and lib.is_prime_power(d - 1):
                    return best
        except Exception:
            pass
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            consider_saturated(*lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass
    if D == 4 and time.monotonic() < final:
        try:
            for q in range(min(d - 1, 9), 1, -1):
                if lib.is_prime_power(q):
                    consider(*_gq_w(q))
                    break
        except Exception:
            pass

    # Phase 1: C voltage-lift annealing over semidirect groups, on an order ladder.
    # A success raises the goal above the new graph; failures ease it back.
    CAP = 7900.0  # keep lifts inside the C engine's MAXN
    lift_frac = 0.75 if best_n <= 3000 else 0.65
    lift_deadline = t0 + lift_frac * total
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}
    goal = float(best_n) * 1.05

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while d <= 31:
        left = lift_deadline - time.monotonic()
        if left < 1.0:
            break
        k = pick_k()
        goal = min(goal, CAP)
        target = max(2, int(goal // (2 * k)) + rng.randrange(0, 3))
        g = _sample_group(target, rng)
        if g is None:
            goal = max(float(best_n) * 1.02, goal * 0.99)
            continue
        m, k2, r = g
        G = m * k2
        if 2 * k * G <= best_n:
            goal = max(goal, best_n * 1.02)
            continue
        if 2 * k * G > 8000:
            goal = max(float(best_n) * 1.02, goal * 0.97)
            continue
        budget = min(4.0, left)
        trials[k] += 1
        res = None
        try:
            res = _lift_c(d, D, rng.randrange(1 << 30), k, m, k2, r, budget)
        except Exception:
            res = None
        if res is not None:
            wins[k] += 1
            consider_saturated(res[0], res[1])
            goal = max(goal, best_n * 1.04)
        else:
            goal = max(float(best_n) * 1.02, goal * 0.99)

    # Phase 2: C grow-by-two from the best graph, using the remaining time.
    remaining = final - time.monotonic() - 2.0
    if remaining > 2.0 and best_n > 2 * d:
        try:
            text = lib.run_c(C_SOURCE, ["grow", d, D, seed, round(remaining, 2)],
                             stdin_graph=best, timeout=remaining + 10)
            out = lib.parse_graph_text(text)
            consider_saturated(out[0], out[1])
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
