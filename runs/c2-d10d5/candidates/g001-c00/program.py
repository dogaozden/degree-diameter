"""Combined degree-diameter search.

Python: picks the best exact or known start (projective plane, Araujo-Pardo-Lopez, or K_{d,d}),
then calls the C engine and keeps the result only if lib.is_valid accepts it.

C: (1) bi-Cayley voltage lifts over Z_m x| Z_k with simulated annealing on the layer and voltage
model, with a bandit over the base size k and stagnation restarts; (2) a time-sliced grow-by-two
step that adds one vertex per side and anneals degree-preserving edge swaps.
"""
import time

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search core.
 *
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v": a valid start graph, or "0 0".
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * Phase 1: bi-Cayley lifts. Vertices A_{i,g} = i*G + g and B_{j,h} = (K+j)*G + h, with
 *          G = |Z_m x| Z_k|. Layer l pairs A_i with B_{lay[l][i]} via voltage S[l][i]:
 *          A_{i,g} ~ B_{j, g*s}. Each layer is a permutation, so the graph is d-regular.
 *          Annealing minimises unreached (block, vertex) pairs plus duplicate-edge penalty.
 * Phase 2: grow by two from the best graph, then anneal edge swaps.
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
#define MAXK 4
#define MAXL 32
#define MAXGRP 64
#define PENALTY 1000L

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

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

static void copy_graph(Graph *dst, const Graph *src) {
    dst->n = src->n;
    for (int v = 0; v < src->n; v++) {
        dst->deg[v] = src->deg[v];
        dst->side[v] = src->side[v];
        memcpy(dst->adj[v], src->adj[v], sizeof(int) * src->deg[v]);
    }
}

/* ------------------------------------------------------------ distance check */

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static int badv[MAXN];

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

/* ------------------------------------------------------------ group Z_m x| Z_k */

/* Element (a, b) is the int a*gk + b; (a,b)(c,e) = (a + r^b c mod m, b + e mod gk). */
static int gk, gm, G;
static int grp[MAXGRP]; /* grp[b] = r^b mod m */

static int gmul(int x, int y) {
    int a = x / gk, b = x % gk, c = y / gk, e = y % gk;
    return (int)(((long)a + (long)grp[b] * c) % gm) * gk + (b + e) % gk;
}

/* Inverse of (a, b) is (-r^(-b) a, -b) and r^(-b) = r^(gk-b). */
static int ginv(int x) {
    int a = x / gk, b = x % gk;
    int nb = (gk - b) % gk;
    long v = ((long)grp[nb] * a) % gm;
    return (int)((gm - v) % gm) * gk + nb;
}

static const int K2S[18] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24};

/* Random group of order >= target, with gcd(r, m) = 1 and r^k2 = 1 mod m. Sets G on success. */
static int sample_group(int target) {
    for (int tries = 0; tries < 200; tries++) {
        int k2 = K2S[rndint(18)];
        int m = (target + k2 - 1) / k2;
        if (m < 2) m = 2;
        int r = -1;
        if (k2 == 1) {
            r = 1;
        } else if (k2 == 2 && rndint(10) < 3) {
            r = m - 1; /* dihedral-type */
            if (gcd(r, m) != 1 || powmod(r, 2, m) != 1 % m) r = -1;
        } else {
            for (int t = 0; t < 60; t++) {
                int c = (m > 2) ? 2 + rndint(m - 2) : 1;
                if (gcd(c, m) == 1 && powmod(c, k2, m) == 1 % m) { r = c; break; }
            }
        }
        if (r < 0) continue;
        gk = k2;
        gm = m;
        grp[0] = 1 % m;
        for (int b = 1; b < k2; b++) grp[b] = (int)((long)grp[b - 1] * r % m);
        G = m * k2;
        return 1;
    }
    return 0;
}

/* ------------------------------------------------------------ bi-Cayley lifts */

static int K;                       /* base size: K blocks per side */
static int lay[MAXL][MAXK];         /* lay[l][i] = B-block of A-block i in layer l */
static int Sv[MAXL][MAXK];          /* voltage */
static int nbr[MAXL][MAXN];         /* nbr[l][v] = neighbour of v in layer l */
static unsigned short reach[MAXN], cand_reach[MAXN], bufA[MAXN], bufB[MAXN];
static int badlist[MAXN];
static int trials[MAXK + 1], wins[MAXK + 1];

static void set_dart(int l, int i) {
    int j = lay[l][i], s = Sv[l][i], si = ginv(s);
    for (int g = 0; g < G; g++) {
        nbr[l][i * G + g] = (K + j) * G + gmul(g, s);
        nbr[l][(K + j) * G + g] = i * G + gmul(g, si);
    }
}

/* Duplicate-edge keys (i, lay, voltage): count entries that repeat an earlier one. */
static long dupcount(void) {
    long dup = 0;
    for (int i = 0; i < K; i++)
        for (int l = 0; l < d; l++)
            for (int l2 = 0; l2 < l; l2++)
                if (lay[l2][i] == lay[l][i] && Sv[l2][i] == Sv[l][i]) { dup++; break; }
    return dup;
}

/* Fills cand_reach with reach bitmasks over block representatives; returns the cost. */
static long eval_state(void) {
    int N = 2 * K * G;
    unsigned short *cur = bufA, *nxt = bufB;
    for (int v = 0; v < N; v++) cur[v] = 0;
    for (int b = 0; b < 2 * K; b++) cur[b * G] = (unsigned short)(1u << b);
    for (int t = 0; t < D; t++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            unsigned short x = cur[v];
            for (int l = 0; l < d; l++) x |= cur[nbr[l][v]];
            nxt[v] = x;
            if (x != cur[v]) changed = 1;
        }
        unsigned short *tmp = cur;
        cur = nxt;
        nxt = tmp;
        if (!changed) break;
    }
    long unreached = 0;
    for (int v = 0; v < N; v++) unreached += 2 * K - __builtin_popcount((unsigned)cur[v]);
    memcpy(cand_reach, cur, sizeof(unsigned short) * N);
    return unreached + PENALTY * dupcount();
}

static void random_state(void) {
    for (int l = 0; l < d; l++) {
        int p[MAXK];
        for (int i = 0; i < K; i++) p[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = p[i]; p[i] = p[j]; p[j] = t;
        }
        for (int i = 0; i < K; i++) lay[l][i] = p[i];
        for (int i = 0; i < K; i++) Sv[l][i] = rndint(G);
    }
    for (int l = 0; l < d; l++)
        for (int i = 0; i < K; i++) set_dart(l, i);
}

/* Annealing over layers and voltages. Returns 1 if the current state has zero cost. */
static int run_search(int iters, int patience, double deadline) {
    int N = 2 * K * G;
    unsigned short full = (unsigned short)((1u << (2 * K)) - 1);
    random_state();
    long cost = eval_state();
    memcpy(reach, cand_reach, sizeof(unsigned short) * N);
    double c0 = cost > 1 ? (double)cost : 1.0;
    long best_cost = cost;
    int last = 0;
    for (int t = 0; t < iters && cost > 0; t++) {
        if (t - last > patience) break;
        if ((t & 31) == 0 && now() > deadline) break;
        double temp = 0.01 * c0 * (1.0 - (double)t / iters);
        if (temp < 0.5) temp = 0.5;

        int l = 0, i1 = -1, i2 = -1, old = 0, swapped = 0;
        if (K >= 2 && rnd01() < 0.25) {
            /* layer-swap move: exchange the B-targets of two A-blocks in one layer */
            swapped = 1;
            l = rndint(d);
            i1 = rndint(K);
            i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            int tmp = lay[l][i1]; lay[l][i1] = lay[l][i2]; lay[l][i2] = tmp;
            set_dart(l, i1);
            set_dart(l, i2);
        } else {
            /* voltage move, defect-targeted with probability 0.4 */
            int nb = 0;
            if (rnd01() < 0.4)
                for (int v = 0; v < N; v++)
                    if (reach[v] != full) badlist[nb++] = v;
            if (nb > 0) {
                int u = badlist[rndint(nb)];
                int blk = u / G;
                l = rndint(d);
                if (blk < K) {
                    i1 = blk;
                } else {
                    i1 = -1;
                    for (int q = 0; q < K; q++)
                        if (lay[l][q] == blk - K) { i1 = q; break; }
                }
                if (i1 < 0) continue;
            } else {
                l = rndint(d);
                i1 = rndint(K);
            }
            old = Sv[l][i1];
            int nw = rndint(G);
            if (nw == old) continue;
            Sv[l][i1] = nw;
            set_dart(l, i1);
        }

        long c2 = eval_state();
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
            memcpy(reach, cand_reach, sizeof(unsigned short) * N);
            if (cost < best_cost) { best_cost = cost; last = t; }
        } else if (swapped) {
            int tmp = lay[l][i1]; lay[l][i1] = lay[l][i2]; lay[l][i2] = tmp;
            set_dart(l, i1);
            set_dart(l, i2);
        } else {
            Sv[l][i1] = old;
            set_dart(l, i1);
        }
    }
    return cost == 0;
}

/* Export the current zero-cost lift as a graph (A side 0, B side 1). */
static void build_graph(Graph *g) {
    int A = K * G, N = 2 * A;
    g->n = N;
    for (int v = 0; v < N; v++) { g->deg[v] = 0; g->side[v] = v >= A; }
    for (int l = 0; l < d; l++)
        for (int v = 0; v < A; v++) add_edge(g, v, nbr[l][v]);
}

static int pick_k(void) {
    if (rnd01() < 0.2) return 1 + rndint(MAXK);
    int bk = 1;
    double bv = -1.0;
    for (int k = 1; k <= MAXK; k++) {
        double v = (wins[k] + 1.0) / (trials[k] + 2.0) + 0.02 * rnd01();
        if (v > bv) { bv = v; bk = k; }
    }
    return bk;
}

static void lift_search(Graph *best, double until) {
    static Graph cand;
    long moore = moore_bound();
    while (now() < until) {
        if (best->n + 2 > moore || best->n + 2 > MAXN) return;
        int k = pick_k();
        int base = best->n / (2 * k);
        int target = base + 1 + rndint(base / 8 + 2);
        if (!sample_group(target)) continue;
        K = k;
        int N = 2 * K * G;
        if (N <= best->n || N > MAXN || N > moore) continue;
        trials[k]++;
        if (run_search(4000, 1200, until)) {
            wins[k]++;
            build_graph(&cand);
            if (cand.n > best->n && is_valid(&cand)) copy_graph(best, &cand);
        }
    }
}

/* ------------------------------------------------------------ grow by two */

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

static void grow_search(Graph *best, double until) {
    static Graph work;
    while (now() < until && best->n + 2 <= moore_bound() && best->n + 2 <= MAXN) {
        double left = until - now();
        double slice = left < 4.0 ? left : (left / 4 > 4.0 ? left / 4 : 4.0);
        if (grow_once(best, &work, now() + slice)) copy_graph(best, &work);
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
    t_end = t0 + limit * 0.93;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 1 || d > MAXD) { printf("0 0\n"); return 0; }

    static Graph best;
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);

    if (D >= 2 && best.n < moore_bound()) {
        double lift_end = t0 + (t_end - t0) * 0.9;
        lift_search(&best, lift_end);
        grow_search(&best, t_end);
    }
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def known_start(d, D):
    """Best exact or known construction for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)           # record order 2(q^2+q+5)
    if D >= 3:
        return _best_pg(d)                             # valid for any D >= 3
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    start = known_start(d, D)
    if start is not None and start[0] > best[0] and lib.is_valid(start[0], start[1], d, D):
        best = start

    if best[0] >= lib.moore_bound(d, D):
        return best   # Moore graph: nothing can beat it

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.5
    if budget < 0.5:
        return best

    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=best, timeout=budget + 5)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except (RuntimeError, ValueError):
        pass   # keep the valid fallback
    return best
