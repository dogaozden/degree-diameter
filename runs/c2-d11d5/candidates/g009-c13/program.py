"""Voltage-lift annealing in C, saturation, and C grow-by-two.

New in this version: LIFT_C is a C annealer for bi-Cayley lifts over semidirect products
Z_m x| Z_k2 (group law computed inline, no tables). It samples base size k and the group, anneals
voltages and layer permutations against unreached pairs, and keeps the largest lift with zero
cost. Python then saturates the result and hands it to the grow-by-two engine (GROW_C).

Every returned graph is checked with lib.is_valid, and K_{d,d} or a known construction is the fallback.
"""
import itertools
import time

import lib


LIFT_C = r'''
/* Bi-Cayley lift annealer over G = Z_m x| Z_k2 (element a*k2+b, (a,b)(c,e) = (a + r^b c, b+e)).
 * Base: K vertices per side. Layer l joins A_i to B_{perm[l][i]} with voltage S[l][i]:
 * A_{i,g} ~ B_{p, g*s}. Left multiplication is an automorphism, so BFS from one vertex per block
 * decides the diameter. Cost = unreached (block rep, vertex) pairs + PEN * duplicate darts.
 * Usage: prog d D seed time_limit   (stdin ignored). stdout: best valid lift as "n m" + edges.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXD 40
#define MAXK 8
#define MAXN 32768
#define PEN 1000L

static int d, D, K, G, M, K2, R;
static int PW[64];
static int perm[MAXD][MAXK];
static int S[MAXD][MAXK];
static int nbr[MAXN][MAXD];
static int N;
static uint32_t vis[MAXN];
static int qu[MAXN];
static uint32_t stamp = 0;
static uint64_t rs = 88172645463325252ULL;
static double tend;
static int bestN = 0, bestM = 0;
static int bu[MAXN / 2 * MAXD];
static int bv[MAXN / 2 * MAXD];

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int gcdi(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static int powmod(int b, int e, int m) {
    long r = 1 % m, x = b % m;
    while (e) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return (int)r;
}

static inline int gmul(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, e = y % K2;
    int t = (int)((a + (long)PW[b] * c) % M);
    return t * K2 + (b + e) % K2;
}

static inline int ginv(int x) {
    int a = x / K2, b = x % K2;
    int nb = (K2 - b) % K2;
    int t = (int)((long)PW[nb] * a % M);
    return ((M - t) % M) * K2 + nb;
}

/* Sample Z_m x| Z_k2 with m*k2 >= target and 2*K*G <= MAXN. */
static int sample_group(int target) {
    static const int k2s[20] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36};
    for (int tries = 0; tries < 400; tries++) {
        int k2 = k2s[rndint(20)];
        int m = (target + k2 - 1) / k2;
        if (m < 2) m = 2;
        if (2L * K * m * k2 > MAXN) continue;
        int r = 1;
        if (k2 > 1 && m > 2 && rnd01() >= 0.3) {
            r = -1;
            for (int t = 0; t < 60; t++) {
                int c = 2 + rndint(m - 2);
                if (gcdi(c, m) == 1 && powmod(c, k2, m) == 1 % m) { r = c; break; }
            }
            if (r < 0) continue;
        }
        M = m; K2 = k2; R = r; G = m * k2;
        PW[0] = 1 % m;
        for (int t = 1; t < K2; t++) PW[t] = (int)((long)PW[t - 1] * r % m);
        return 1;
    }
    return 0;
}

/* Write the neighbours of A block i and B block perm[l][i] for layer l. */
static void set_dart(int l, int i) {
    int j = perm[l][i], s = S[l][i], si = ginv(s);
    for (int g = 0; g < G; g++) nbr[i * G + g][l] = (K + j) * G + gmul(g, s);
    for (int h = 0; h < G; h++) nbr[(K + j) * G + h][l] = i * G + gmul(h, si);
}

static long dupcount(void) {
    static int ki[MAXD * MAXK], kj[MAXD * MAXK], ks[MAXD * MAXK];
    int L = d * K, t = 0;
    for (int l = 0; l < d; l++)
        for (int i = 0; i < K; i++) {
            ki[t] = i; kj[t] = perm[l][i]; ks[t] = S[l][i]; t++;
        }
    long c = 0;
    for (int a = 0; a < L; a++)
        for (int b = 0; b < a; b++)
            if (ki[a] == ki[b] && kj[a] == kj[b] && ks[a] == ks[b]) c++;
    return c;
}

/* Total number of (block representative, vertex) pairs at distance > D. */
static long unreached(void) {
    long total = 0;
    for (int b = 0; b < 2 * K; b++) {
        int src = b * G;
        stamp++;
        if (stamp == 0) { memset(vis, 0, sizeof vis); stamp = 1; }
        int head = 0, tail = 0;
        vis[src] = stamp;
        qu[tail++] = src;
        for (int depth = 0; depth < D && head < tail; depth++) {
            int end = tail;
            while (head < end) {
                int v = qu[head++];
                for (int l = 0; l < d; l++) {
                    int u = nbr[v][l];
                    if (vis[u] != stamp) { vis[u] = stamp; qu[tail++] = u; }
                }
            }
        }
        total += N - tail;
    }
    return total;
}

static long eval_cost(void) { return unreached() + PEN * dupcount(); }

static void save_best(void) {
    int cnt = 0;
    for (int u = 0; u < K * G; u++)
        for (int l = 0; l < d; l++) {
            bu[cnt] = u;
            bv[cnt] = nbr[u][l];
            cnt++;
        }
    bestN = 2 * K * G;
    bestM = cnt;
}

/* Simulated annealing on one configuration. Returns 1 if cost reached 0. */
static int run_sa(long patience) {
    long cost = eval_cost();
    long bestc = cost;
    double T0 = 0.02 * (double)(cost > 1 ? cost : 1);
    if (T0 < 2.0) T0 = 2.0;
    double T = T0;
    long last = 0;
    for (long t = 1; cost > 0; t++) {
        if (t - last > patience) return 0;
        if ((t & 63) == 0 && now() > tend) return 0;
        T *= 0.9997;
        if (T < 0.3) T = T0;
        if (K >= 2 && rnd01() < 0.25) {
            int l = rndint(d), i1 = rndint(K), i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            int tmp = perm[l][i1]; perm[l][i1] = perm[l][i2]; perm[l][i2] = tmp;
            set_dart(l, i1);
            set_dart(l, i2);
            long c2 = eval_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                tmp = perm[l][i1]; perm[l][i1] = perm[l][i2]; perm[l][i2] = tmp;
                set_dart(l, i1);
                set_dart(l, i2);
            }
        } else {
            int l = rndint(d), i = rndint(K);
            int old = S[l][i], nw = rndint(G);
            if (nw == old) continue;
            S[l][i] = nw;
            set_dart(l, i);
            long c2 = eval_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                S[l][i] = old;
                set_dart(l, i);
            }
        }
        if (cost < bestc) { bestc = cost; last = t; }
    }
    return 1;
}

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
    tend = t0 + limit * 0.9 - 0.3;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    if (d < 2 || d > MAXD || D < 2) { printf("0 0\n"); return 0; }

    static const int KS[5] = {1, 2, 3, 4, 6};
    int wins[5] = {0, 0, 0, 0, 0}, trials[5] = {0, 0, 0, 0, 0};
    double goal = 16.0;
    while (now() < tend) {
        int bi = 0;
        double bs = -1.0;
        for (int q = 0; q < 5; q++) {
            double sc = (wins[q] + 1.0) / (trials[q] + 2.0) + 0.05 * rnd01();
            if (sc > bs) { bs = sc; bi = q; }
        }
        if (rnd01() < 0.2) bi = rndint(5);
        K = KS[bi];
        int target = (int)(goal / (2.0 * K)) + rndint(3);
        if (target < 2) target = 2;
        if (!sample_group(target)) {
            goal *= 0.95;
            if (goal < 8.0) goal = 8.0;
            continue;
        }
        for (int l = 0; l < d; l++) {
            for (int i = 0; i < K; i++) perm[l][i] = i;
            for (int i = K - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int tmp = perm[l][i]; perm[l][i] = perm[l][j]; perm[l][j] = tmp;
            }
            for (int i = 0; i < K; i++) S[l][i] = rndint(G);
        }
        N = 2 * K * G;
        for (int l = 0; l < d; l++)
            for (int i = 0; i < K; i++) set_dart(l, i);
        trials[bi]++;
        int ok = run_sa(15000);
        if (ok) {
            wins[bi]++;
            if (N > bestN) save_best();
            goal = N * 1.02 + 2.0;
        } else {
            double floorg = bestN + 1.0;
            goal *= 0.985;
            if (goal < floorg) goal = floorg;
            if (goal < 8.0) goal = 8.0;
        }
    }
    if (bestN == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", bestN, bestM);
    for (int e = 0; e < bestM; e++) printf("%d %d\n", bu[e], bv[e]);
    return 0;
}
'''


GROW_C = r'''
/* Grow-by-two search core.
 * Usage:  prog d D seed time_limit < start_graph
 * stdin:  "n m" + m edge lines (valid bipartite start), or "0 0".
 * stdout: "n m" + edges of the best valid graph found (never worse than the input).
 *
 * Each step inserts one vertex on each side, using the spare degree freed by d-1 deleted
 * edges, then anneals degree-preserving edge swaps until every pair is within distance D.
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
#define MAXW (MAXN / 64)

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
        long nb = bad_pairs(work);
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) {
            bad = nb;
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

    # Phase 1: C voltage-lift annealer over semidirect products (new fast search core).
    if 3 <= d <= 32 and time.monotonic() < final:
        lift_end = t0 + 0.7 * total
        budget = lift_end - time.monotonic()
        if budget > 1.0:
            try:
                text = lib.run_c(LIFT_C, [d, D, seed, round(budget, 2)],
                                 stdin_graph=None, timeout=budget + 10)
                n, e = lib.parse_graph_text(text)
                if n > 0:
                    consider_saturated(n, e)
            except Exception:
                pass

    # Phase 2: C grow-by-two from the best graph, using the remaining time.
    remaining = final - time.monotonic() - 2.0
    if remaining > 2.0 and best_n > 2 * d and d <= 32:
        try:
            text = lib.run_c(GROW_C, [d, D, seed, round(remaining, 2)],
                             stdin_graph=best, timeout=remaining + 10)
            out = lib.parse_graph_text(text)
            if out[0] > 0:
                consider_saturated(out[0], out[1])
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
