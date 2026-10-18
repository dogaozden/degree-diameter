"""Combined program: bi-Cayley voltage-lift search over semidirect groups, run by a C annealer
(mode "lift") that replaces the Python search loop, then greedy edge saturation of every
candidate, then a C grow-by-two engine that inserts vertices into the best graph found.
Saturation only adds edges between opposite-side vertices with spare degree, so distances can
only shrink and validity is preserved.

Every returned graph is checked with lib.is_valid, and K_{d,d} (or a known construction) is the fallback.
"""
import itertools
import math
import random
import time

import lib


C_SOURCE = r'''
/* Grow-by-two search core, plus a bi-Cayley lift annealer.
 * Usage:  prog d D seed time_limit < start_graph      (grow mode)
 *         prog lift d D seed time_limit k m k2 r      (lift mode, stdin ignored)
 * grow stdin:  "n m" + m edge lines (valid bipartite start), or "0 0".
 * stdout:      "n m" + edges of the best valid graph found (never worse than the input).
 *
 * Lift mode anneals voltage assignments over the semidirect product Z_m x| Z_k2 (r^k2 = 1 mod m)
 * with k base blocks per side. Element (a,b) is coded a*k2+b, and (a,b)(c,d) = (a + r^b c, b+d).
 * The lift is left-invariant under the group, so it is valid iff every vertex is within D of
 * every block representative, which is what the bitmask reach computes.
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

/* ------------------------------------------------------------------------
 * Lift mode: simulated annealing over voltage assignments of a bi-Cayley lift.
 * Vertices: A_{i,g} = i*G + g (i < k), B_{p,h} = (k+p)*G + h, with G = m*k2.
 * Layer l pairs A_i with B_{lay[l][i]} through voltage S[l][i]: A_{i,g} ~ B_{p, g*s}.
 * ------------------------------------------------------------------------ */
#define LMAXN 16384
#define LMAXK 4
#define LMAXL 32
#define LPEN 1000L

static int L_d, L_D, L_k, L_m, L_k2, L_G, L_N;
static unsigned char L_full;
static int L_pw[256];
static int L_lay[LMAXL][LMAXK];
static int L_S[LMAXL][LMAXK];
static int L_nbr[LMAXL][LMAXN];
static unsigned char L_rc[LMAXN], L_cur[LMAXN];
static unsigned char L_bufA[LMAXN], L_bufB[LMAXN];

static int L_gcd(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

/* Semidirect product: (a,b)(c,e) = (a + r^b c, b + e). */
static int L_mul(int x, int y) {
    int a = x / L_k2, b = x % L_k2;
    int c = y / L_k2, e = y % L_k2;
    return ((a + L_pw[b] * c) % L_m) * L_k2 + (b + e) % L_k2;
}

/* Inverse of (a,b) is (-r^(-b) a, -b). */
static int L_inv(int x) {
    int a = x / L_k2, b = x % L_k2;
    int nb = (L_k2 - b) % L_k2;
    long t = ((long)L_m - L_pw[nb]) % L_m;
    int na = (int)(t * a % L_m);
    return na * L_k2 + nb;
}

/* Write layer l's neighbours for A block i and B block p with voltage s. */
static void L_set(int l, int i, int p, int s) {
    int G = L_G, k = L_k;
    int si = L_inv(s);
    int *A = L_nbr[l];
    for (int g = 0; g < G; g++) {
        A[i * G + g] = (k + p) * G + L_mul(g, s);
        A[(k + p) * G + g] = i * G + L_mul(g, si);
    }
}

/* Fill L_rc with per-vertex bitmasks (bit b: block representative b within distance D);
 * return the number of (vertex, representative) pairs still missing. */
static long L_eval(void) {
    int N = L_N, k = L_k, d_ = L_d;
    unsigned char *cur = L_bufA, *nxt = L_bufB;
    memset(cur, 0, (size_t)N);
    for (int b = 0; b < 2 * k; b++) cur[b * L_G] = (unsigned char)(1u << b);
    for (int t = 0; t < L_D; t++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            unsigned char x = cur[v];
            for (int l = 0; l < d_; l++) x |= cur[L_nbr[l][v]];
            nxt[v] = x;
            changed |= (x != cur[v]);
        }
        unsigned char *tmp = cur;
        cur = nxt;
        nxt = tmp;
        if (!changed) break;
    }
    long miss = 0;
    for (int v = 0; v < N; v++) {
        L_rc[v] = cur[v];
        miss += __builtin_popcount((unsigned)(L_full & ~cur[v]));
    }
    return miss;
}

/* Number of duplicated darts (same base pair and voltage), which would be duplicate edges. */
static long L_dup(void) {
    int keys[LMAXL * LMAXK];
    int c = 0;
    for (int l = 0; l < L_d; l++)
        for (int i = 0; i < L_k; i++)
            keys[c++] = (i * L_k + L_lay[l][i]) * L_G + L_S[l][i];
    long dup = 0;
    for (int a = 0; a < c; a++)
        for (int b = 0; b < a; b++)
            if (keys[a] == keys[b]) dup++;
    return dup;
}

static int L_anneal(double tbudget, long patience) {
    int k = L_k, d_ = L_d, G = L_G, N = L_N;
    double t0 = now();
    double deadline = t0 + tbudget;
    for (int l = 0; l < d_; l++) {
        for (int i = 0; i < k; i++) L_lay[l][i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rndint(i + 1), tmp = L_lay[l][i];
            L_lay[l][i] = L_lay[l][j];
            L_lay[l][j] = tmp;
        }
        for (int i = 0; i < k; i++) {
            L_S[l][i] = rndint(G);
            L_set(l, i, L_lay[l][i], L_S[l][i]);
        }
    }
    long cost = L_eval() + LPEN * L_dup();
    memcpy(L_cur, L_rc, (size_t)N);
    double c0 = cost > 1 ? (double)cost : 1.0;
    long best = cost, last = 0;

    for (long t = 0; cost > 0; t++) {
        double tn = now();
        if (tn > deadline || t - last > patience) break;
        double frac = (tn - t0) / tbudget;
        if (frac > 1.0) frac = 1.0;
        double temp = 0.02 * c0 * (1.0 - frac);
        if (temp < 0.3) temp = 0.3;

        if (k >= 2 && rnd01() < 0.25) {
            int l = rndint(d_);
            int i1 = rndint(k), i2 = rndint(k - 1);
            if (i2 >= i1) i2++;
            int tmp = L_lay[l][i1];
            L_lay[l][i1] = L_lay[l][i2];
            L_lay[l][i2] = tmp;
            L_set(l, i1, L_lay[l][i1], L_S[l][i1]);
            L_set(l, i2, L_lay[l][i2], L_S[l][i2]);
            long c2 = L_eval() + LPEN * L_dup();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                memcpy(L_cur, L_rc, (size_t)N);
                if (cost < best) { best = cost; last = t; }
            } else {
                tmp = L_lay[l][i1];
                L_lay[l][i1] = L_lay[l][i2];
                L_lay[l][i2] = tmp;
                L_set(l, i1, L_lay[l][i1], L_S[l][i1]);
                L_set(l, i2, L_lay[l][i2], L_S[l][i2]);
            }
            continue;
        }

        /* Voltage move; with probability 0.4 aim at a vertex that is still missing pairs. */
        int u = -1;
        if (rnd01() < 0.4) {
            for (int tr = 0; tr < 30; tr++) {
                int v = rndint(N);
                if (L_cur[v] != L_full) { u = v; break; }
            }
        }
        int l, i;
        if (u >= 0) {
            int block = u / G;
            l = rndint(d_);
            i = -1;
            if (block < k) {
                i = block;
            } else {
                for (int j = 0; j < k; j++)
                    if (L_lay[l][j] == block - k) { i = j; break; }
            }
            if (i < 0) continue;
        } else {
            l = rndint(d_);
            i = rndint(k);
        }
        int old = L_S[l][i];
        int nw = rndint(G);
        if (nw == old) continue;
        L_S[l][i] = nw;
        L_set(l, i, L_lay[l][i], nw);
        long c2 = L_eval() + LPEN * L_dup();
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
            memcpy(L_cur, L_rc, (size_t)N);
            if (cost < best) { best = cost; last = t; }
        } else {
            L_S[l][i] = old;
            L_set(l, i, L_lay[l][i], old);
        }
    }
    return cost == 0;
}

static void L_print(void) {
    int k = L_k, G = L_G, d_ = L_d;
    long M = (long)k * G * d_;
    printf("%d %ld\n", L_N, M);
    for (int u = 0; u < k * G; u++)
        for (int l = 0; l < d_; l++)
            printf("%d %d\n", u, L_nbr[l][u]);
}

static int lift_main(int argc, char **argv) {
    if (argc < 10) { printf("0 0\n"); return 0; }
    L_d = atoi(argv[2]);
    L_D = atoi(argv[3]);
    long seed = atol(argv[4]);
    double limit = atof(argv[5]);
    L_k = atoi(argv[6]);
    L_m = atoi(argv[7]);
    L_k2 = atoi(argv[8]);
    int r = atoi(argv[9]);
    if (L_d < 1 || L_d > LMAXL || L_D < 1 || L_k < 1 || L_k > LMAXK || L_m < 2 ||
        L_k2 < 1 || L_k2 > 256 || r < 1 || r >= L_m || L_gcd(r, L_m) != 1 || limit <= 0) {
        printf("0 0\n");
        return 0;
    }
    L_G = L_m * L_k2;
    if (2L * L_k * L_G > LMAXN) { printf("0 0\n"); return 0; }
    L_N = 2 * L_k * L_G;
    L_full = (unsigned char)((1u << (2 * L_k)) - 1);
    L_pw[0] = 1 % L_m;
    for (int t = 1; t < L_k2; t++) L_pw[t] = (int)((long)L_pw[t - 1] * r % L_m);
    if ((long)L_pw[L_k2 - 1] * r % L_m != 1 % L_m) { printf("0 0\n"); return 0; }

    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (L_anneal(limit * 0.9, 3000)) L_print();
    else printf("0 0\n");
    return 0;
}

int main(int argc, char **argv) {
    if (argc >= 2 && strcmp(argv[1], "lift") == 0) return lift_main(argc, argv);
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
# Bi-Cayley lift parameters over semidirect products Z_m x| Z_k2.
# The annealing itself runs in C (lift mode of C_SOURCE).
# ----------------------------------------------------------------------------

_KS = (1, 2, 3, 4)
_MAX_N = 16000  # must stay within LMAXN in the C lift annealer


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


def _c_lift(d, D, seed, budget, k, m, k2, r):
    """Run the C lift annealer for one group/base-size choice; return (n, edges) or None."""
    try:
        text = lib.run_c(C_SOURCE, ["lift", d, D, seed, round(budget, 2), k, m, k2, r],
                         timeout=budget + 10)
        n, edges = lib.parse_graph_text(text)
    except Exception:
        return None
    return (n, edges) if n > 0 else None


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

    # Phase 1: bi-Cayley lift search (C annealer) with a bandit over base sizes k.
    # The order goal is ratcheted: a success jumps the goal above the new graph, while
    # failures ease it back toward the current best. Large graphs make the C grow phase
    # more expensive per step, so the lift share shrinks once best_n is large.
    lift_frac = 0.6 if best_n > 3000 else 0.75
    lift_deadline = t0 + lift_frac * total
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}
    goal = float(best_n) * 1.05
    seed_base = rng.randrange(1 << 30)
    trial_no = 0

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while True:
        remaining = lift_deadline - time.monotonic()
        if remaining < 0.5:
            break
        k = pick_k()
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
        if 2 * k * G > _MAX_N:
            goal = max(float(best_n) * 1.02, goal * 0.99)
            continue
        trials[k] += 1
        trial_no += 1
        budget = min(remaining, 8.0)
        res = _c_lift(d, D, seed_base + trial_no, budget, k, m, k2, r)
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
            text = lib.run_c(C_SOURCE, [d, D, seed, round(remaining, 2)],
                             stdin_graph=best, timeout=remaining + 10)
            out = lib.parse_graph_text(text)
            consider_saturated(out[0], out[1])
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
