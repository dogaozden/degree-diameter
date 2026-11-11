"""Merged search: the best known construction is the start, then one C engine runs
bi-Cayley (voltage-lift) annealing over semidirect-product groups and grow-by-two
from the best graph found so far. Every returned graph is checked with lib.is_valid."""
import itertools
import time

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search core.
 *
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v": a valid start graph, or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * Phases:
 *   1. Bi-Cayley lifts: k base vertices per side, group Z_m x| Z_k2, each layer a
 *      permutation of blocks with one voltage. Simulated annealing on the number of
 *      (block representative, vertex) pairs left unreached within D steps.
 *   2. Grow by two: insert one vertex per side, then anneal degree-preserving swaps
 *      until every pair is within D steps.
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
#define MAXK 4
#define MAXG 4096
#define PENALTY 1000

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

typedef struct {
    int m, k, r;
    int rp[16];
} Grp;

static int d, D;
static double t_end;
static uint64_t rng_state = 88172645463325252ULL;

/* ------------------------------------------------------------------ utilities */

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

static int gcd_int(int a, int b) {
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
static int badv[MAXN];

/* Number of unordered pairs at distance > D. Fills badv[] with per-vertex counts. */
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

/* ------------------------------------------------------------------ groups */

/* Z_m x|_r Z_k: element (a, b) is a*k + b; (a,b)(c,e) = (a + r^b c mod m, b + e mod k). */
static Grp CG;
static int GSZ = 0;

static int gmul(const Grp *G, int x, int y) {
    int a = x / G->k, b = x % G->k, c = y / G->k, e = y % G->k;
    return (int)(((long)a + (long)G->rp[b] * c) % G->m) * G->k + (b + e) % G->k;
}

/* Inverse of (a, b) is (-r^(-b) a, -b). */
static int ginv(const Grp *G, int x) {
    int a = x / G->k, b = x % G->k;
    int nb = (G->k - b) % G->k;
    long c = (G->m - ((long)G->rp[nb] * a) % G->m) % G->m;
    return (int)c * G->k + nb;
}

/* Sample a group of order m*k2 >= target into CG. */
static int sample_group(int target) {
    static const int K2[16] = {1, 1, 1, 2, 2, 2, 3, 4, 4, 5, 6, 8, 9, 10, 12, 16};
    for (int attempt = 0; attempt < 300; attempt++) {
        int k2 = K2[rndint(16)];
        int m = (target + k2 - 1) / k2;
        if (m < 2) m = 2;
        if (m * k2 > MAXG) continue;
        int r = 1 % m;
        if (k2 > 1 && m > 2) {
            int found = 0;
            for (int t = 0; t < 60 && !found; t++) {
                int c = 2 + rndint(m - 2);
                if (gcd_int(c, m) == 1 && powmod(c, k2, m) == 1 % m) { r = c; found = 1; }
            }
            if (!found) continue;
        }
        CG.m = m;
        CG.k = k2;
        CG.r = r;
        CG.rp[0] = 1 % m;
        for (int b = 1; b < k2; b++) CG.rp[b] = (int)((long)CG.rp[b - 1] * r % m);
        return 1;
    }
    return 0;
}

/* ------------------------------------------------------------------ bi-Cayley lifts */

/* Layer l maps A-block i to B-block layers[l][i] with voltage svol[l][i]:
 * A_{i,g} ~ B_{j,g*s}. Vertices: A block i is i*GSZ + g, B block j is (k+j)*GSZ + h. */
static int layers[MAXD][MAXK];
static int svol[MAXD][MAXK];
static int nbr[MAXD][MAXN];
static uint32_t REACH[MAXN], NEXTR[MAXN];

static void set_dart(int k, int l, int i, int j, int s) {
    int G = GSZ;
    int si = ginv(&CG, s);
    for (int g = 0; g < G; g++) {
        nbr[l][i * G + g] = (k + j) * G + gmul(&CG, g, s);
        nbr[l][(k + j) * G + g] = i * G + gmul(&CG, g, si);
    }
}

/* Unreached (block representative, vertex) pairs. Zero means diameter <= D. */
static long unreached(int k) {
    int N = 2 * k * GSZ;
    for (int v = 0; v < N; v++) REACH[v] = 0;
    for (int b = 0; b < 2 * k; b++) REACH[b * GSZ] |= 1u << b;
    for (int r = 0; r < D; r++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint32_t x = REACH[v];
            for (int l = 0; l < d; l++) x |= REACH[nbr[l][v]];
            NEXTR[v] = x;
            if (x != REACH[v]) changed = 1;
        }
        memcpy(REACH, NEXTR, sizeof(uint32_t) * (size_t)N);
        if (!changed) break;
    }
    long cnt = 0;
    for (int v = 0; v < N; v++) cnt += __builtin_popcount(REACH[v]);
    return (long)2 * k * N - cnt;
}

/* Number of duplicate darts (same block pair and same voltage in two layers). */
static long dupcount(int k) {
    long c = 0;
    int F = d * k;
    for (int f = 0; f < F; f++) {
        int l = f / k, i = f % k;
        for (int g = f + 1; g < F; g++) {
            int l2 = g / k, i2 = g % k;
            if (i == i2 && layers[l][i] == layers[l2][i2] && svol[l][i] == svol[l2][i2]) c++;
        }
    }
    return c;
}

/* Simulated annealing over layers and voltages. Returns 1 when the lift has diameter <= D. */
static int anneal(int k, double deadline, int iters, int patience) {
    int G = GSZ;
    int perm[MAXK];
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < k; i++) perm[i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int s = perm[i]; perm[i] = perm[j]; perm[j] = s;
        }
        for (int i = 0; i < k; i++) {
            layers[l][i] = perm[i];
            svol[l][i] = rndint(G);
            set_dart(k, l, i, perm[i], svol[l][i]);
        }
    }
    long cost = unreached(k) + PENALTY * dupcount(k);
    double c0 = cost > 1 ? (double)cost : 1.0;
    long best_cost = cost;
    int last = 0;
    for (int t = 0; t < iters && cost > 0; t++) {
        if (((t & 63) == 0) && now() > deadline) break;
        if (t - last > patience) break;
        double temp = 0.01 * c0 * (1.0 - (double)t / iters);
        if (temp < 0.5) temp = 0.5;
        long c2;
        if (k >= 2 && rnd01() < 0.25) {
            /* layer swap: exchange the B-targets of two A-blocks in one layer */
            int l = rndint(d);
            int i1 = rndint(k), i2 = rndint(k - 1);
            if (i2 >= i1) i2++;
            int tmp = layers[l][i1]; layers[l][i1] = layers[l][i2]; layers[l][i2] = tmp;
            set_dart(k, l, i1, layers[l][i1], svol[l][i1]);
            set_dart(k, l, i2, layers[l][i2], svol[l][i2]);
            c2 = unreached(k) + PENALTY * dupcount(k);
            if (c2 <= cost || rnd01() < exp((double)(cost - c2) / temp)) {
                cost = c2;
                if (cost < best_cost) { best_cost = cost; last = t; }
            } else {
                tmp = layers[l][i1]; layers[l][i1] = layers[l][i2]; layers[l][i2] = tmp;
                set_dart(k, l, i1, layers[l][i1], svol[l][i1]);
                set_dart(k, l, i2, layers[l][i2], svol[l][i2]);
            }
        } else {
            /* voltage change */
            int l = rndint(d), i = rndint(k);
            int old = svol[l][i];
            int nw = rndint(G);
            if (nw == old) continue;
            svol[l][i] = nw;
            set_dart(k, l, i, layers[l][i], nw);
            c2 = unreached(k) + PENALTY * dupcount(k);
            if (c2 <= cost || rnd01() < exp((double)(cost - c2) / temp)) {
                cost = c2;
                if (cost < best_cost) { best_cost = cost; last = t; }
            } else {
                svol[l][i] = old;
                set_dart(k, l, i, layers[l][i], old);
            }
        }
    }
    return cost == 0;
}

static void build_cand(Graph *g, int k) {
    int G = GSZ, AN = k * G;
    g->n = 2 * AN;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= AN; }
    for (int u = 0; u < AN; u++)
        for (int l = 0; l < d; l++) add_edge(g, u, nbr[l][u]);
}

static void bicayley_search(Graph *best, double until) {
    static Graph cand;
    long mb = moore_bound();
    while (now() < until) {
        if (best->n + 2 > mb) return;
        int k = 1 + rndint(MAXK);
        int need = best->n + 2;
        int target = (need + 2 * k - 1) / (2 * k) + rndint(3);
        if (!sample_group(target)) continue;
        GSZ = CG.m * CG.k;
        long N = 2L * k * GSZ;
        if (N > MAXN || N < need || N > mb) continue;
        if (!anneal(k, until, 4000, 1200)) continue;
        build_cand(&cand, k);
        if (cand.n > best->n && is_valid(&cand)) copy_graph(best, &cand);
    }
}

/* ------------------------------------------------------------------ grow by two */

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
    while (now() < until && best->n + 2 <= moore_bound()) {
        double left = until - now();
        double slice = left < 4.0 ? left : (left / 4 > 4.0 ? left / 4 : 4.0);
        if (grow_once(best, &work, now() + slice)) copy_graph(best, &work);
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
        printf("1 0\n");
        return 0;
    }

    static Graph best;
    read_start(&best);
    int had_start = best.n > 0;
    if (best.n == 0) complete_bipartite(&best);

    if (D >= 2 && best.n < moore_bound()) {
        double split = had_start ? 0.45 : 0.75;
        bicayley_search(&best, t0 + (t_end - t0) * split);
        if (best.n > 0) grow_search(&best, t_end);
    }
    if (best.n == 0) complete_bipartite(&best);
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


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d, capped at q = 7 for speed."""
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _valid(g, d, D):
    return g is not None and lib.is_valid(g[0], g[1], d, D)


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if D <= 1 or d < 1:
        return (2, [(0, 1)]) if (D == 1 and d >= 1) else (1, [])

    moore = lib.moore_bound(d, D)

    # Candidate starts; K_{d,d} is always valid for D >= 2.
    cands = [lib.haar_graph(d, range(d))]
    if D >= 3:
        cands.append(_best_pg(d))
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        cands.append(lib.araujo_lopez_graph(d - 2))
    if D == 4:
        cands.append(_best_gq(d))

    best = None
    for g in cands:
        if _valid(g, d, D) and (best is None or g[0] > best[0]):
            best = g
    if best is None:
        best = lib.haar_graph(d, range(d))

    # Already a Moore graph: nothing can beat it.
    if best[0] >= moore:
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.5
    if budget < 2.0:
        return best

    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=best, timeout=budget + 8.0)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
