"""Combined search: exact small constructions, then a C engine that runs bi-Cayley lift
annealing over Z_m x| Z_k groups (bandit over base size k), then grow-by-two from the best graph.
Python builds the start graph and validates everything before returning."""
import time

import lib

C_SOURCE = r'''
/* Combined bipartite degree-diameter engine.
 *
 * Usage:  prog d D seed time_limit   < start_graph
 * stdin:  "n m" then m lines "u v" (valid start), or "0 0".
 * stdout: "n m" then m lines "u v": the largest valid graph found.
 *
 * Phase 1 (bi-Cayley lifts): vertices A_{i,g} = i*G+g and B_{j,g} = (K+j)*G+g, for base
 * blocks i,j < K and group elements g of Z_GM x| Z_GK (order G). Each of the d layers is a
 * permutation LAY[l] pairing A-block i with B-block LAY[l][i] via voltage VOL[l][i]:
 * A_{i,g} ~ B_{j, g*s}. The graph is d-regular and bipartite. Left multiplication is an
 * automorphism, so diameter is checked from the 2K block representatives with bitmasks.
 * Simulated annealing minimises unreached (representative, vertex) pairs, with restarts.
 *
 * Phase 2 (grow by two): insert one new vertex per side into the best graph using spare
 * edge slots, then anneal degree-preserving swaps until the diameter is <= D.
 *
 * Every returned graph is checked by is_valid().
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 8192
#define MAXD 16
#define MAXW (MAXN / 64)
#define MAXK 6
#define PEN 1000

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;

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
        memcpy(dst->adj[v], src->adj[v], sizeof(int) * (size_t)src->deg[v]);
    }
}

/* ------------------------------------------------------------------ distance check */

static uint64_t BPA[MAXN * MAXW], BPB[MAXN * MAXW];
static int badv[MAXN]; /* vertices farther than D from v, set by bad_pairs() */

/* Number of unordered pairs at distance > D (0 means diameter <= D and connected). */
static long bad_pairs(const Graph *g) {
    int n = g->n, W = (n + 63) / 64;
    uint64_t *cur = BPA, *nxt = BPB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            const uint64_t *src = cur + (size_t)v * W;
            memcpy(dst, src, sizeof(uint64_t) * (size_t)W);
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

/* Full validity: simple, bipartite (side labels), degree <= d, diameter <= D. */
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
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN || m < 0) return;
    g->n = n;
    for (int v = 0; v < n; v++) { g->deg[v] = 0; g->side[v] = 255; }
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= n || v >= n ||
            u == v || g->deg[u] >= MAXD || g->deg[v] >= MAXD) {
            g->n = 0;
            return;
        }
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
                if (g->side[u] == 255) {
                    g->side[u] = (unsigned char)(1 - g->side[v]);
                    queue[tail++] = u;
                } else if (g->side[u] == g->side[v]) {
                    g->n = 0;
                    return;
                }
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
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = (unsigned char)(v >= d); }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

/* ------------------------------------------------------------------ groups */

/* Group Z_GM x| Z_GK, element a*GK+b, (a,b)(c,e) = (a + r^b c mod GM, b+e mod GK). */
static int K, G, GM, GK, GR;
static int RP[MAXN]; /* RP[b] = GR^b mod GM */

static int gmul(int x, int y) {
    int a = x / GK, b = x % GK, c = y / GK, e = y % GK;
    long t = ((long)a + (long)RP[b] * c) % GM;
    return (int)(t * GK + (b + e) % GK);
}

/* Uniformly random (m, k, r) with m*k = N, gcd(r, m) = 1 and r^k = 1 mod m. */
static void random_group(int N) {
    long count = 0;
    int bm = 1, bk = N, br = 1;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        int rmax = m > 1 ? m : 2;
        for (int r = 1; r < rmax; r++) {
            if (m > 1 && gcd_int(r, m) != 1) continue;
            if (powmod(r, k, m) != (1 % m)) continue;
            count++;
            if (rndint((int)count) == 0) { bm = m; bk = k; br = r; }
        }
    }
    G = N;
    GM = bm;
    GK = bk;
    GR = br;
    RP[0] = 1 % GM;
    for (int b = 1; b < GK; b++) RP[b] = (int)((long)RP[b - 1] * GR % GM);
}

/* ------------------------------------------------------------------ bi-Cayley lifts */

static int LAY[MAXD][MAXK];
static int VOL[MAXD][MAXK];
static int NB[MAXD][MAXN];
static uint64_t ACC[MAXN], CND[MAXN], SCR[MAXN];

/* Write layer l's neighbours from its darts (both directions). */
static void set_layer(int l) {
    for (int i = 0; i < K; i++) {
        int j = LAY[l][i], s = VOL[l][i];
        for (int g = 0; g < G; g++) {
            int a = i * G + g;
            int b = (K + j) * G + gmul(g, s);
            NB[l][a] = b;
            NB[l][b] = a;
        }
    }
}

/* Number of duplicate darts: same A-block, same B-block, same voltage in two layers. */
static long dupcount(void) {
    long c = 0;
    for (int i = 0; i < K; i++)
        for (int l = 0; l < d; l++)
            for (int l2 = l + 1; l2 < d; l2++)
                if (LAY[l][i] == LAY[l2][i] && VOL[l][i] == VOL[l2][i]) c++;
    return c;
}

/* Cost = unreached (representative, vertex) pairs + penalty per duplicate dart.
 * The reach masks are written into res. Cost 0 means the lift is valid. */
static long evaluate(uint64_t *res) {
    int N = 2 * K * G;
    uint64_t *cur = res, *nxt = SCR;
    memset(cur, 0, sizeof(uint64_t) * (size_t)N);
    for (int b = 0; b < 2 * K; b++) cur[(size_t)b * G] = 1ULL << b;
    for (int t = 0; t < D; t++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint64_t x = cur[v];
            for (int l = 0; l < d; l++) x |= cur[NB[l][v]];
            nxt[v] = x;
            changed |= (x != cur[v]);
        }
        uint64_t *tmp = cur;
        cur = nxt;
        nxt = tmp;
        if (!changed) break;
    }
    if (cur != res) memcpy(res, cur, sizeof(uint64_t) * (size_t)N);
    long unreached = 0;
    for (int v = 0; v < N; v++) unreached += 2 * K - __builtin_popcountll(res[v]);
    return unreached + (long)PEN * dupcount();
}

static int accept(long c2, long c1, double temp) {
    if (c2 <= c1) return 1;
    return rnd01() < exp(-(double)(c2 - c1) / temp);
}

static void lift_to_graph(Graph *g) {
    int half = K * G;
    g->n = 2 * half;
    for (int v = 0; v < g->n; v++) {
        g->deg[v] = 0;
        g->side[v] = (unsigned char)(v >= half);
    }
    for (int a = 0; a < half; a++)
        for (int l = 0; l < d; l++) add_edge(g, a, NB[l][a]);
}

/* Simulated annealing from a random start. Returns 1 when a valid lift is found. */
static int anneal(int iters, int patience, double until) {
    int N = 2 * K * G;
    uint64_t full = (1ULL << (2 * K)) - 1;
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < K; i++) LAY[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int s = LAY[l][i];
            LAY[l][i] = LAY[l][j];
            LAY[l][j] = s;
        }
        for (int i = 0; i < K; i++) VOL[l][i] = rndint(G);
        set_layer(l);
    }
    long cost = evaluate(ACC);
    double c0 = cost > 1 ? (double)cost : 1.0;
    long best = cost;
    int last = 0;
    for (int t = 0; t < iters && cost > 0; t++) {
        if ((t & 31) == 0 && now() > until) break;
        if (t - last > patience) break;
        double temp = 0.01 * c0 * (1.0 - (double)t / iters);
        if (temp < 0.5) temp = 0.5;

        if (K >= 2 && rnd01() < 0.25) {
            /* Layer swap: exchange the B-targets of two A-blocks in one layer. */
            int l = rndint(d), i1 = rndint(K), i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            int s = LAY[l][i1];
            LAY[l][i1] = LAY[l][i2];
            LAY[l][i2] = s;
            set_layer(l);
            long c2 = evaluate(CND);
            if (accept(c2, cost, temp)) {
                cost = c2;
                memcpy(ACC, CND, sizeof(uint64_t) * (size_t)N);
                if (cost < best) { best = cost; last = t; }
            } else {
                s = LAY[l][i1];
                LAY[l][i1] = LAY[l][i2];
                LAY[l][i2] = s;
                set_layer(l);
            }
            continue;
        }

        /* Voltage move: defect-targeted with probability 0.4, otherwise uniform. */
        int l = -1, i = -1;
        if (rnd01() < 0.4) {
            int u = -1;
            for (int tries = 0; tries < 50; tries++) {
                int v = rndint(N);
                if (ACC[v] != full) { u = v; break; }
            }
            if (u >= 0) {
                int block = u / G;
                l = rndint(d);
                if (block < K) {
                    i = block;
                } else {
                    for (int q = 0; q < K; q++)
                        if (LAY[l][q] == block - K) { i = q; break; }
                }
            }
        }
        if (i < 0) {
            l = rndint(d);
            i = rndint(K);
        }
        int old = VOL[l][i];
        int nw = rndint(G);
        if (nw == old) continue;
        VOL[l][i] = nw;
        set_layer(l);
        long c2 = evaluate(CND);
        if (accept(c2, cost, temp)) {
            cost = c2;
            memcpy(ACC, CND, sizeof(uint64_t) * (size_t)N);
            if (cost < best) { best = cost; last = t; }
        } else {
            VOL[l][i] = old;
            set_layer(l);
        }
    }
    return cost == 0;
}

/* Bandit over base sizes K; each trial aims at a group order just above the current best. */
static void cayley_search(Graph *best, double until) {
    static int trials[MAXK + 1], wins[MAXK + 1];
    static Graph cand;
    long moore = moore_bound();
    long lim = moore < MAXN ? moore : MAXN;
    while (now() < until) {
        if (best->n + 2 > lim) return;
        int k = 1;
        if (rnd01() < 0.2) {
            k = 1 + rndint(MAXK);
        } else {
            double bs = -1.0;
            for (int c = 1; c <= MAXK; c++) {
                double sc = (wins[c] + 1.0) / (trials[c] + 2.0) + 0.02 * rnd01();
                if (sc > bs) { bs = sc; k = c; }
            }
        }
        int base = best->n / (2 * k);
        int grp = base + 1 + rndint(base / 8 + 2);
        if (2L * k * grp > lim) continue;
        random_group(grp);
        K = k;
        trials[k]++;
        if (anneal(6000, 1500, until)) {
            wins[k]++;
            lift_to_graph(&cand);
            if (cand.n > best->n && is_valid(&cand)) copy_graph(best, &cand);
        }
    }
}

/* ------------------------------------------------------------------ grow by two */

/* Insert one vertex per side into a copy of best (degree d each), then anneal swaps. */
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
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best;
    if (d < 1 || d > MAXD || D < 1) {
        printf("1 0\n");
        return 0;
    }
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (!is_valid(&best)) complete_bipartite(&best);

    if (D >= 3 && best.n < moore_bound()) {
        cayley_search(&best, t0 + limit * 0.85);
        grow_search(&best, t0 + limit * 0.93);
    }
    if (!is_valid(&best)) complete_bipartite(&best);
    if (!is_valid(&best)) {
        printf("1 0\n");
        return 0;
    }
    print_graph(&best);
    return 0;
}
'''


def _exact(d, D):
    """Optimal graphs for tiny parameters, or None."""
    if d <= 0 or D <= 0:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]
    if D == 2:
        return lib.haar_graph(d, range(d))   # K_{d,d}: optimal for diameter 2
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    ex = _exact(d, D)
    if ex is not None and lib.is_valid(ex[0], ex[1], d, D):
        return ex

    best = lib.haar_graph(d, range(d))   # K_{d,d}: valid for D >= 2
    if not lib.is_valid(best[0], best[1], d, D):
        return (1, [])

    def consider(g):
        nonlocal best
        if g is not None and g[0] > best[0] and lib.is_valid(g[0], g[1], d, D):
            best = g

    if D >= 3:
        if lib.is_prime_power(d - 1):
            consider(lib.projective_plane_incidence(d - 1))   # Moore graph for D = 3
            if D == 3:
                return best
        elif d - 2 >= 3 and lib.is_prime_power(d - 2):
            consider(lib.araujo_lopez_graph(d - 2))           # record start for D = 3

    if d > 16 or D < 3 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.8 * time_limit - 2.0 - (time.monotonic() - t0)
    if budget < 1.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=best, timeout=budget + 8.0)
        consider(lib.parse_graph_text(text))
    except (RuntimeError, ValueError, IndexError):
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
