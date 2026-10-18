"""Bi-Cayley lift search in C over semidirect groups Z_m x| Z_k2, followed by a C grow-by-two
phase that inserts vertices into the best graph found.

The lift search is exact. A lift with base size k and group G is G-invariant under left
multiplication, so diameter D holds iff every one of the 2k block representatives reaches all
2kG vertices within D steps. Each annealing evaluation is therefore 2k breadth-first searches on
a precomputed neighbour table, with a penalty for parallel edges. Every returned graph is checked
with lib.is_valid. K_{d,d} (or a known construction) is the fallback.
"""
import itertools
import time

import lib


C_SOURCE = r'''
/* Usage:
 *   prog d D seed time_limit lift floorN     -> prints best bi-Cayley lift with > floorN vertices
 *   prog d D seed time_limit < start_graph   -> grow-by-two from the start graph
 * Output: "n m" followed by m edge lines, or "0 0" when nothing was found.
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
#define LMAX MAXD
#define KMAX 12
#define NKS 9
#define PEN 1000

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
 * Bi-Cayley lift search over Z_m x| Z_k2.
 * Vertices: A_{i,g} = i*G + g (i < k), B_{j,h} = (k+j)*G + h, G = m*k2.
 * Layer l: A block i joins B block LP[l][i] with voltage LV[l][i]:
 *          A_{i,g} ~ B_{LP[l][i], g * LV[l][i]}.
 * Each layer is a perfect matching, so the graph is d-regular.
 * ------------------------------------------------------------------------ */
static int gM = 1, gK2 = 1, gR = 1, gG = 1;
static int gPW[64];
static int LK = 1;
static int LP[LMAX][KMAX];
static int LV[LMAX][KMAX];
static int nbr[MAXN][MAXD];
static int vis[MAXN];
static int bq[MAXN];
static int vstamp = 0;
static Graph gl;

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static int pw_mod(int b, int e, int m) {
    long r = 1 % m, x = b % m;
    while (e > 0) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return (int)r;
}

static void set_group(int m, int k2, int r) {
    gM = m; gK2 = k2; gR = r; gG = m * k2;
    long p = 1 % m;
    for (int b = 0; b < k2; b++) {
        gPW[b] = (int)p;
        p = p * r % m;
    }
}

/* (a,b)*(c,e) = (a + r^b c, b + e) */
static inline int gmul(int x, int y) {
    int a = x / gK2, b = x % gK2, c = y / gK2, e = y % gK2;
    long t = ((long)a + (long)gPW[b] * c) % gM;
    return (int)(t * gK2 + (b + e) % gK2);
}

/* inverse of (a,b) is (-r^{-b} a, -b) */
static inline int ginv(int x) {
    int a = x / gK2, b = x % gK2;
    int nb = (gK2 - b) % gK2;
    long t = ((long)gPW[nb] * a) % gM;
    return (int)(((gM - t) % gM) * gK2 + nb);
}

static int sample_group(int target) {
    static const int K2S[20] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36};
    for (int tries = 0; tries < 200; tries++) {
        int k2 = K2S[rndint(20)];
        int m = (target + k2 - 1) / k2;
        if (m < 2) m = 2;
        if ((long)m * k2 > MAXN) continue;
        if (k2 == 1) {
            set_group(m, 1, 1);
            return 1;
        }
        for (int t = 0; t < 100; t++) {
            int c = 1 + rndint(m - 1);
            if (gcd_i(c, m) == 1 && pw_mod(c, k2, m) == 1 % m) {
                set_group(m, k2, c);
                return 1;
            }
        }
    }
    return 0;
}

static void fill_layer(int l) {
    int k = LK, G = gG;
    for (int i = 0; i < k; i++) {
        int j = LP[l][i], v = LV[l][i], iv = ginv(v);
        for (int g = 0; g < G; g++) {
            nbr[i * G + g][l] = (k + j) * G + gmul(g, v);
            nbr[(k + j) * G + g][l] = i * G + gmul(g, iv);
        }
    }
}

static void init_random(void) {
    int k = LK, G = gG;
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < k; i++) LP[l][i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = LP[l][i];
            LP[l][i] = LP[l][j];
            LP[l][j] = t;
        }
        for (int i = 0; i < k; i++) LV[l][i] = rndint(G);
        fill_layer(l);
    }
}

/* Parallel edges: same A block, same target B block, same voltage in two layers. */
static long lift_dups(void) {
    long c = 0;
    for (int i = 0; i < LK; i++)
        for (int l = 0; l < d; l++)
            for (int l2 = l + 1; l2 < d; l2++)
                if (LP[l][i] == LP[l2][i] && LV[l][i] == LV[l2][i]) c++;
    return c;
}

/* Sum over the 2k block representatives of vertices not reached within D steps. */
static long lift_cost(void) {
    int k = LK, G = gG, N = 2 * k * G;
    long unreached = 0;
    for (int b = 0; b < 2 * k; b++) {
        int src = b * G;
        vstamp++;
        int head = 0, tail = 0;
        bq[tail++] = src;
        vis[src] = vstamp;
        for (int depth = 0; depth < D && head < tail; depth++) {
            int end = tail;
            while (head < end) {
                int v = bq[head++];
                for (int l = 0; l < d; l++) {
                    int u = nbr[v][l];
                    if (vis[u] != vstamp) {
                        vis[u] = vstamp;
                        bq[tail++] = u;
                    }
                }
            }
        }
        unreached += N - tail;
    }
    return unreached;
}

static long full_cost(void) {
    return lift_cost() + (long)PEN * lift_dups();
}

static void build_gl(void) {
    int A = LK * gG, N = 2 * A;
    gl.n = N;
    for (int v = 0; v < N; v++) {
        gl.deg[v] = 0;
        gl.side[v] = (unsigned char)(v < A ? 0 : 1);
    }
    for (int v = 0; v < A; v++)
        for (int l = 0; l < d; l++) {
            int u = nbr[v][l];
            gl.adj[v][gl.deg[v]++] = u;
            gl.adj[u][gl.deg[u]++] = v;
        }
}

/* Simulated annealing over the current LK; returns 1 when cost reaches 0. */
static int anneal(double deadline, long patience) {
    int k = LK;
    long cost = full_cost();
    double c0 = (double)(cost > 0 ? cost : 1);
    long best = cost, last = 0;
    for (long t = 0;; t++) {
        if (cost == 0) return 1;
        if ((t & 3) == 0 && now() > deadline) return 0;
        if (t - last > patience) return 0;
        double temp = 0.3 + 0.02 * c0 / (1.0 + t / 1000.0);
        int l = rndint(d);
        long nc;
        int acc = 0;
        if (k >= 2 && rnd01() < 0.3) {
            int i1 = rndint(k), i2 = rndint(k - 1);
            if (i2 >= i1) i2++;
            int tmp = LP[l][i1];
            LP[l][i1] = LP[l][i2];
            LP[l][i2] = tmp;
            fill_layer(l);
            nc = full_cost();
            if (nc <= cost || rnd01() < exp(-(double)(nc - cost) / temp)) {
                acc = 1;
            } else {
                tmp = LP[l][i1];
                LP[l][i1] = LP[l][i2];
                LP[l][i2] = tmp;
                fill_layer(l);
            }
        } else {
            int i = rndint(k);
            int old = LV[l][i];
            int nv = rndint(gG);
            if (nv == old) continue;
            LV[l][i] = nv;
            fill_layer(l);
            nc = full_cost();
            if (nc <= cost || rnd01() < exp(-(double)(nc - cost) / temp)) {
                acc = 1;
            } else {
                LV[l][i] = old;
                fill_layer(l);
            }
        }
        if (acc) {
            cost = nc;
            if (cost < best) {
                best = cost;
                last = t;
            }
        }
    }
}

static int bestFound = 0, bestN = 0;
static int bK, bM, bK2, bR;
static int bLP[LMAX][KMAX], bLV[LMAX][KMAX];

static void save_best(int k, int N) {
    bestFound = 1;
    bestN = N;
    bK = k;
    bM = gM;
    bK2 = gK2;
    bR = gR;
    for (int l = 0; l < d; l++)
        for (int i = 0; i < k; i++) {
            bLP[l][i] = LP[l][i];
            bLV[l][i] = LV[l][i];
        }
}

static void emit_best(void) {
    LK = bK;
    set_group(bM, bK2, bR);
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < bK; i++) {
            LP[l][i] = bLP[l][i];
            LV[l][i] = bLV[l][i];
        }
        fill_layer(l);
    }
    int A = bK * gG;
    printf("%d %d\n", 2 * A, A * d);
    for (int v = 0; v < A; v++)
        for (int l = 0; l < d; l++)
            printf("%d %d\n", v, nbr[v][l]);
}

static int pick_k(const int *tr, const int *wn) {
    if (rnd01() < 0.2) return rndint(NKS);
    int bi = 0;
    double bv = -1.0;
    for (int i = 0; i < NKS; i++) {
        double v = (wn[i] + 1.0) / (tr[i] + 2.0) + 0.02 * rnd01();
        if (v > bv) { bv = v; bi = i; }
    }
    return bi;
}

static void lift_driver(double until, int floorN) {
    static const int KS[NKS] = {1, 2, 3, 4, 5, 6, 8, 10, 12};
    int trials[NKS], wins[NKS];
    for (int i = 0; i < NKS; i++) { trials[i] = 0; wins[i] = 0; }
    bestN = floorN;
    double goal = floorN * 1.05 + 4.0;
    while (now() < until && bestN < MAXN) {
        double left = until - now();
        if (left < 0.5) break;
        int ki = pick_k(trials, wins);
        int k = KS[ki];
        int target = (int)(goal / (2.0 * k)) + rndint(3);
        if (target < 2) target = 2;
        if (!sample_group(target)) {
            goal = bestN * 1.02 + 2.0;
            continue;
        }
        int N = 2 * k * gG;
        if (N > MAXN || N <= bestN) {
            goal = bestN * 1.02 + 2.0;
            continue;
        }
        LK = k;
        trials[ki]++;
        double slice = left / 4.0;
        if (slice < 3.0) slice = left;
        if (slice > 15.0) slice = 15.0;
        init_random();
        int ok = anneal(now() + slice, 5000);
        if (ok) {
            build_gl();
            if (is_valid(&gl)) {
                wins[ki]++;
                save_best(k, N);
                goal = bestN * 1.04 + 2.0;
                continue;
            }
        }
        double lo = bestN * 1.02 + 2.0;
        double dec = goal * 0.99;
        goal = dec > lo ? dec : lo;
    }
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [lift floorN] < start_graph\n", argv[0]);
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

    if (argc >= 6 && strcmp(argv[5], "lift") == 0) {
        int floorN = argc >= 7 ? atoi(argv[6]) : 0;
        lift_driver(t_end, floorN);
        if (!bestFound) printf("0 0\n");
        else emit_best();
        return 0;
    }

    read_start(&gbest);
    if (gbest.n == 0) { printf("0 0\n"); return 0; }
    grow_search(t_end);
    if (!is_valid(&gbest)) { printf("0 0\n"); return 0; }
    print_graph(&gbest);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Exact small constructions.
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
# Saturation: add every legal missing edge between deficient vertices of opposite sides.
# Adding edges never breaks diameter or bipartiteness; results are re-checked.
# ----------------------------------------------------------------------------

def _saturate(n, edges, d, D):
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

    # Exact constructions (calibration cases return immediately).
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

    # Phase 1: exact bi-Cayley lift search in C (bandit over base sizes, ratcheted order goal).
    if d >= 3 and D >= 3:
        left = final - time.monotonic() - 3.0
        if left > 4.0:
            budget = round(0.75 * left, 2)
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, budget, "lift", best_n],
                                 stdin_graph=None, timeout=budget + 15)
                n, e = lib.parse_graph_text(text)
                consider_saturated(n, e)
            except Exception:
                pass

    # Phase 2: C grow-by-two from the best graph, using the remaining time.
    remaining = final - time.monotonic() - 2.0
    if remaining > 2.0 and best_n > 2 * d:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(remaining, 2)],
                             stdin_graph=best, timeout=remaining + 10)
            n, e = lib.parse_graph_text(text)
            consider_saturated(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
