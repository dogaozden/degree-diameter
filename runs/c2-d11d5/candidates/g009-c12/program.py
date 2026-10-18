"""Combined program: Python goal-ratchet over semidirect groups, a C bi-Cayley voltage annealer
(lift mode) that runs each group trial, and a C grow-by-two engine (grow mode) for small graphs.

Every returned graph is checked with lib.is_valid, and K_{d,d} (or a known construction) is the fallback.
"""
import itertools
import math
import random
import time

import lib


C_SOURCE = r'''
/* Two modes in one binary.
 *
 * Grow mode (default):
 *   prog d D seed time_limit < start_graph
 *   stdin:  "n m" + m edge lines (valid bipartite start), or "0 0".
 *   stdout: "n m" + edges of the best valid graph found (never worse than the input).
 *   Each step inserts one vertex on each side, using the spare degree freed by d-1 deleted
 *   edges, then anneals degree-preserving edge swaps until every pair is within distance D.
 *
 * Lift mode:
 *   prog lift d D seed time_limit k m k2 r iters patience
 *   Searches a bi-Cayley lift over G = Z_m x| Z_k2 (element a*k2+b, product (a,b)(c,d) =
 *   (a + r^b c, b + d)) with k base vertices per side and d layers. Layer l pairs A_i with
 *   B_{layers[l][i]} through voltage s: A_{i,g} ~ B_{p, g*s}. Simulated annealing on the
 *   number of unreached (block representative, vertex) pairs plus a duplicate-edge penalty.
 *   stdout: "n m" + edges on success, or "0 0".
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

/* ------------------------- lift mode ------------------------- */

#define LMAXN 40000
#define LMAXD 32
#define PEN 1000

static int lk, lG, lm, lk2, lr;
static int pw[64];
static int nb[LMAXD][LMAXN];
static int layers[LMAXD][4];
static int sv[LMAXD][4];
static uint8_t reachS[LMAXN], reachT[LMAXN];

/* Product in G = Z_lm x| Z_lk2 with element a*lk2 + b. */
static int gmul(int x, int y) {
    int a = x / lk2, b = x % lk2;
    int c = y / lk2, e = y % lk2;
    long long t = (long long)a + (long long)pw[b] * c;
    return (int)((t % lm) * lk2 + (b + e) % lk2);
}

/* Write layer l's darts for base A-vertex i and base B-vertex p with voltage s. */
static void set_dart(int l, int i, int p, int s) {
    for (int g = 0; g < lG; g++) {
        int ua = i * lG + g;
        int vb = (lk + p) * lG + gmul(g, s);
        nb[l][ua] = vb;
        nb[l][vb] = ua;
    }
}

static void swap_layer(int l, int i1, int i2) {
    int tmp = layers[l][i1];
    layers[l][i1] = layers[l][i2];
    layers[l][i2] = tmp;
    set_dart(l, i1, layers[l][i1], sv[l][i1]);
    set_dart(l, i2, layers[l][i2], sv[l][i2]);
}

/* For each vertex, bitmask of block representatives that reach it within D. Returns unreached count. */
static int lift_reach(uint8_t *out) {
    int N = 2 * lk * lG;
    static uint8_t tmp[LMAXN];
    memset(out, 0, (size_t)N);
    for (int b = 0; b < 2 * lk; b++) out[b * lG] = (uint8_t)(1u << b);
    for (int r = 0; r < D; r++) {
        memcpy(tmp, out, (size_t)N);
        for (int l = 0; l < d; l++) {
            const int *nl = nb[l];
            for (int v = 0; v < N; v++) tmp[v] |= out[nl[v]];
        }
        int changed = memcmp(tmp, out, (size_t)N) != 0;
        memcpy(out, tmp, (size_t)N);
        if (!changed) break;
    }
    int full_bits = 2 * lk, unreached = 0;
    for (int v = 0; v < N; v++) unreached += full_bits - __builtin_popcount(out[v]);
    return unreached;
}

/* Number of repeated (A-block, B-block, voltage) triples; each is a multi-edge. */
static int lift_dups(void) {
    int c = 0;
    for (int l = 0; l < d; l++)
        for (int i = 0; i < lk; i++)
            for (int l2 = 0; l2 < l; l2++)
                if (layers[l2][i] == layers[l][i] && sv[l2][i] == sv[l][i]) c++;
    return c;
}

static int lift_main(int argc, char **argv) {
    if (argc < 12) { printf("0 0\n"); return 0; }
    d = atoi(argv[2]);
    D = atoi(argv[3]);
    long seed = atol(argv[4]);
    double limit = atof(argv[5]);
    lk = atoi(argv[6]);
    lm = atoi(argv[7]);
    lk2 = atoi(argv[8]);
    lr = atoi(argv[9]);
    long iters = atol(argv[10]);
    long patience = atol(argv[11]);
    if (d < 1 || d > LMAXD || D < 1 || lk < 1 || lk > 4 || lm < 2 ||
        lk2 < 1 || lk2 > 64 || lr < 0 || lr >= lm || iters < 1) {
        printf("0 0\n");
        return 0;
    }
    lG = lm * lk2;
    if (2L * lk * lG > LMAXN) { printf("0 0\n"); return 0; }
    pw[0] = 1 % lm;
    for (int t = 1; t < lk2; t++) pw[t] = (int)((long long)pw[t - 1] * lr % lm);
    if ((long long)pw[lk2 - 1] * lr % lm != 1 % lm) { printf("0 0\n"); return 0; }

    double t0 = now();
    double deadline = t0 + limit;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    int N = 2 * lk * lG;
    int full = (1 << (2 * lk)) - 1;
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < lk; i++) layers[l][i] = i;
        for (int i = lk - 1; i > 0; i--) {
            int j = rndint(i + 1), tmp = layers[l][i];
            layers[l][i] = layers[l][j];
            layers[l][j] = tmp;
        }
        for (int i = 0; i < lk; i++) {
            sv[l][i] = rndint(lG);
            set_dart(l, i, layers[l][i], sv[l][i]);
        }
    }

    int cost = lift_reach(reachS) + PEN * lift_dups();
    double c0 = cost > 1 ? (double)cost : 1.0;
    int best_cost = cost;
    long last = 0;

    for (long t = 0; t < iters; t++) {
        if (cost == 0 || now() > deadline) break;
        if (t - last > patience) break;
        double temp = 0.01 * c0 * (1.0 - (double)t / (double)iters);
        if (temp < 0.5) temp = 0.5;

        if (lk >= 2 && rnd01() < 0.25) {
            int l = rndint(d);
            int i1 = rndint(lk);
            int i2 = rndint(lk - 1);
            if (i2 >= i1) i2++;
            swap_layer(l, i1, i2);
            int c2 = lift_reach(reachT) + PEN * lift_dups();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                memcpy(reachS, reachT, (size_t)N);
                if (cost < best_cost) { best_cost = cost; last = t; }
            } else {
                swap_layer(l, i1, i2);
            }
            continue;
        }

        int u = -1;
        if (rnd01() < 0.4) {
            for (int tr = 0; tr < 50; tr++) {
                int v = rndint(N);
                if (reachS[v] != full) { u = v; break; }
            }
        }
        int l = rndint(d);
        int i;
        if (u >= 0) {
            int block = u / lG;
            if (block < lk) {
                i = block;
            } else {
                i = -1;
                for (int j = 0; j < lk; j++)
                    if (layers[l][j] == block - lk) { i = j; break; }
                if (i < 0) continue;
            }
        } else {
            i = rndint(lk);
        }

        int old = sv[l][i];
        int nw = rndint(lG);
        if (nw == old) continue;
        sv[l][i] = nw;
        set_dart(l, i, layers[l][i], nw);
        int c2 = lift_reach(reachT) + PEN * lift_dups();
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
            memcpy(reachS, reachT, (size_t)N);
            if (cost < best_cost) { best_cost = cost; last = t; }
        } else {
            sv[l][i] = old;
            set_dart(l, i, layers[l][i], old);
        }
    }

    if (cost != 0) { printf("0 0\n"); return 0; }
    long M = (long)lk * lG * d;
    printf("%d %ld\n", N, M);
    for (int u = 0; u < lk * lG; u++)
        for (int l = 0; l < d; l++)
            printf("%d %d\n", u, nb[l][u]);
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
# Bi-Cayley lift search: group sampling in Python, annealing in C (lift mode).
# ----------------------------------------------------------------------------

_KS = (1, 2, 3, 4)
# Above this order the C grow-by-two step cannot repair enough pairs in its time slice,
# so the time is better spent on more lift searches.
_GROW_MAX_N = 1500
_LIFT_ITERS = 20000
_LIFT_PATIENCE = 3000
_LIFT_MAXN = 40000   # must match LMAXN in the C source
_TRIAL_CAP = 8.0     # seconds per C lift trial


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


def _lift_trial(d, D, seed, k, m, k2, r, seconds):
    """Run one C lift annealing trial. Returns (n, edges) or None."""
    text = lib.run_c(C_SOURCE, ["lift", d, D, seed, round(seconds, 2), k, m, k2, r,
                                _LIFT_ITERS, _LIFT_PATIENCE],
                     timeout=seconds + 10)
    n, edges = lib.parse_graph_text(text)
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
            consider(*lib.araujo_lopez_graph(d - 2))
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

    # Phase 1: bi-Cayley lift search. Python samples the group and manages a bandit over
    # base sizes k and an order goal that ratchets up after successes. Each trial's
    # annealing runs in C, which evaluates many more states per second than numpy.
    use_grow = best_n <= _GROW_MAX_N
    lift_deadline = t0 + (0.75 if use_grow else 1.0) * total
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}
    goal = float(best_n) * 1.05

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while True:
        left = lift_deadline - time.monotonic()
        if left < 0.5:
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
        if 2 * k * G > _LIFT_MAXN:
            goal = max(float(best_n) * 1.02, goal * 0.97)
            continue
        trials[k] += 1
        try:
            res = _lift_trial(d, D, rng.randrange(1 << 30), k, m, k2, r,
                              min(_TRIAL_CAP, left))
        except Exception:
            res = None
        if res is not None:
            wins[k] += 1
            consider(res[0], res[1])
            goal = max(goal, res[0] * 1.04)
        else:
            goal = max(float(best_n) * 1.02, goal * 0.99)

    # Phase 2: C grow-by-two from the best graph, using the remaining time (small graphs only).
    remaining = final - time.monotonic() - 2.0
    if use_grow and remaining > 2.0 and best_n > 2 * d:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(remaining, 2)],
                             stdin_graph=best, timeout=remaining + 10)
            out = lib.parse_graph_text(text)
            consider(out[0], out[1])
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
