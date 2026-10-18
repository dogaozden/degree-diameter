"""Ruin-free voltage search with exhaustive coordinate descent.

Python builds exact or known starting graphs (projective planes, Araujo-Lopez,
W(q) for D=4) and falls back to K_{d,d}. The C engine is a new construction family:

Bi-block lifts over a group G = Z_m x| Z_k of order exactly T. The graph has 2*KB*T
vertices. Each of the d layers is a bijection pi_l from A-blocks to B-blocks plus a
voltage s_{l,i} per A-block, so A_{i,g} ~ B_{pi_l(i), g*s_{l,i}}. Every vertex then has
degree exactly d, and the graph is bipartite. Left multiplication by G is an
automorphism, so the diameter condition reduces to checking the block representatives.

Search: coordinate descent over (layer, block) pairs. Each coordinate's voltage is chosen
exhaustively (or from a random sample of 300 when G is large) to minimise the number of
unreached (representative, vertex) pairs. Duplicate edges are forbidden during the choice.
When stuck, the search restores the best state and applies a kick (swap two targets in a
layer, or randomise one voltage). The engine tries target orders just above the current best
and keeps every verified improvement. Each output is checked with bitset diameter and degree
tests before it replaces the best graph.
"""
import itertools
import time

import lib

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 4096
#define MAXD 32
#define MAXK 4
#define MAXR 64
#define MAXW (MAXN / 64)
#define CANDMAX 300
#define BIGC (1L << 60)

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static double t_end;
static Graph best;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int gcd_i(int a, int b) {
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

/* ------------------------------------------------------------ graph basics */

static void add_edge(Graph *g, int u, int v) {
    g->adj[u][g->deg[u]++] = v;
    g->adj[v][g->deg[v]++] = u;
}

static void complete_bipartite(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) {
        g->deg[v] = 0;
        g->side[v] = (unsigned char)(v >= d);
    }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
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

/* ------------------------------------------------------------ groups */

static int GM, GK, GRR, GG;
static int rpw[MAXR];

static int gmul(int x, int y) {
    int a = x / GK, b = x % GK, c = y / GK, e = y % GK;
    long t = (a + (long)rpw[b] * c) % GM;
    return (int)(t * GK + (b + e) % GK);
}

static void set_group(int m, int k, int r) {
    GM = m; GK = k; GRR = r; GG = m * k;
    rpw[0] = 1 % m;
    for (int b = 1; b < k; b++) rpw[b] = (int)((long)rpw[b - 1] * r % m);
}

static const int KLIST[] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36};

/* Choose Z_m x|_r Z_k with m*k == G exactly. Returns 0 if G has no usable divisor. */
static int pick_group(int G) {
    int cand[32], nc = 0;
    int nk = (int)(sizeof(KLIST) / sizeof(KLIST[0]));
    for (int t = 0; t < nk; t++)
        if (G % KLIST[t] == 0 && G / KLIST[t] >= 2) cand[nc++] = KLIST[t];
    if (nc == 0) return 0;
    int k = cand[rndint(nc)];
    int m = G / k;
    int r = 1;
    if (k == 2 && rnd01() < 0.3) {
        r = m - 1;
    } else if (k > 2 && m > 2) {
        for (int t = 0; t < 80; t++) {
            int c = 2 + rndint(m - 2);
            if (gcd_i(c, m) == 1 && powmod(c, k, m) == 1 % m) { r = c; break; }
        }
    }
    set_group(m, k, r);
    return 1;
}

/* ------------------------------------------------------------ bi-block lift state */

static int KB;                       /* A-blocks (and B-blocks) */
static int NN;                       /* 2*KB*GG */
static int perm[MAXD][MAXK];         /* layer l: A-block i -> B-block perm[l][i] */
static int volt[MAXD][MAXK];        /* voltage of (l, i) */
static int nbr[MAXD][MAXN];
static int spm[MAXD][MAXK], svo[MAXD][MAXK];
static uint16_t RR0[MAXN], RR1[MAXN];

/* A_{i,g} ~ B_{j,g*s} for the layer, stored in both directions. */
static void build_layer(int l) {
    for (int i = 0; i < KB; i++) {
        int j = perm[l][i], s = volt[l][i];
        for (int g = 0; g < GG; g++) {
            int a = i * GG + g;
            int b = (KB + j) * GG + gmul(g, s);
            nbr[l][a] = b;
            nbr[l][b] = a;
        }
    }
}

static void build_all(void) {
    for (int l = 0; l < d; l++) build_layer(l);
}

/* Sum over vertices of (2KB - number of block representatives within distance D). */
static long cost_full(void) {
    uint16_t *cur = RR0, *nxt = RR1;
    int N = NN;
    for (int v = 0; v < N; v++) cur[v] = 0;
    for (int b = 0; b < 2 * KB; b++) cur[b * GG] = (uint16_t)(1u << b);
    for (int r = 0; r < D; r++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint16_t x = cur[v];
            for (int l = 0; l < d; l++) x |= cur[nbr[l][v]];
            nxt[v] = x;
            if (x != cur[v]) changed = 1;
        }
        uint16_t *t = cur;
        cur = nxt;
        nxt = t;
        if (!changed) break;
    }
    long s = 0;
    int full = 2 * KB;
    for (int v = 0; v < N; v++) s += full - __builtin_popcount(cur[v]);
    return s;
}

/* True if voltage s for (l, i) would duplicate an edge set of another layer. */
static int dup_with(int l, int i, int s) {
    int j = perm[l][i];
    for (int l2 = 0; l2 < d; l2++)
        if (l2 != l && perm[l2][i] == j && volt[l2][i] == s) return 1;
    return 0;
}

/* Exhaustive (or sampled) choice of the voltage of (l, i). Returns the resulting cost. */
static long optimize_coord(int l, int i) {
    int old = volt[l][i];
    int bests = old;
    long bestc = BIGC;
    int ties = 0;
    int full = (GG <= CANDMAX);
    int nc = full ? GG : CANDMAX;
    for (int t = 0; t < nc; t++) {
        int s = full ? t : rndint(GG);
        if (dup_with(l, i, s)) continue;
        volt[l][i] = s;
        build_layer(l);
        long c = cost_full();
        if (c < bestc) {
            bestc = c;
            bests = s;
            ties = 1;
        } else if (c == bestc) {
            ties++;
            if (rndint(ties) == 0) bests = s;
        }
        if (c == 0) break;
    }
    if (bestc >= BIGC) {
        volt[l][i] = old;
        build_layer(l);
        return cost_full();
    }
    volt[l][i] = bests;
    build_layer(l);
    return bestc;
}

static long randomize_state(void) {
    for (int l = 0; l < d; l++) {
        int p[MAXK];
        for (int i = 0; i < KB; i++) p[i] = i;
        for (int i = KB - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = p[i]; p[i] = p[j]; p[j] = t;
        }
        for (int i = 0; i < KB; i++) { perm[l][i] = p[i]; volt[l][i] = -1; }
    }
    for (int l = 0; l < d; l++)
        for (int i = 0; i < KB; i++) {
            int s = rndint(GG);
            for (int t = 0; t < 200 && dup_with(l, i, s); t++) s = rndint(GG);
            volt[l][i] = s;
        }
    build_all();
    return cost_full();
}

static void save_state(void) {
    memcpy(spm, perm, sizeof perm);
    memcpy(svo, volt, sizeof volt);
}

static long load_state(void) {
    memcpy(perm, spm, sizeof perm);
    memcpy(volt, svo, sizeof volt);
    build_all();
    return cost_full();
}

/* Kick: swap two targets in a layer, or randomise one voltage. */
static long perturb(long cost) {
    int kicks = 1 + rndint(2);
    for (int k = 0; k < kicks; k++) {
        int l = rndint(d), i = rndint(KB);
        if (KB >= 2 && rnd01() < 0.5) {
            int i2 = rndint(KB - 1);
            if (i2 >= i) i2++;
            int t = perm[l][i]; perm[l][i] = perm[l][i2]; perm[l][i2] = t;
            cost = optimize_coord(l, i2);
            cost = optimize_coord(l, i);
        } else {
            int s = rndint(GG);
            if (!dup_with(l, i, s)) {
                volt[l][i] = s;
                build_layer(l);
            }
            cost = cost_full();
        }
    }
    return cost;
}

/* Coordinate descent with ILS-style kicks. Returns 1 when the diameter condition holds. */
static int search(double deadline) {
    long cost = randomize_state();
    long bestc = cost;
    save_state();
    int stagn = 0;
    int nco = d * KB;
    static int ord[MAXD * MAXK];
    while (cost > 0 && now() < deadline) {
        for (int t = 0; t < nco; t++) ord[t] = t;
        for (int t = nco - 1; t > 0; t--) {
            int j = rndint(t + 1);
            int x = ord[t]; ord[t] = ord[j]; ord[j] = x;
        }
        for (int t = 0; t < nco && cost > 0; t++) {
            int l = ord[t] / KB, i = ord[t] % KB;
            cost = optimize_coord(l, i);
        }
        if (cost == 0) break;
        if (cost < bestc) {
            bestc = cost;
            save_state();
            stagn = 0;
        } else if (++stagn >= 3) {
            cost = load_state();
            cost = perturb(cost);
            stagn = 0;
        }
    }
    return cost == 0;
}

static void build_graph(Graph *g) {
    int A = KB * GG, N = 2 * A;
    g->n = N;
    for (int v = 0; v < N; v++) {
        g->deg[v] = 0;
        g->side[v] = (unsigned char)(v >= A);
    }
    for (int l = 0; l < d; l++)
        for (int u = 0; u < A; u++) add_edge(g, u, nbr[l][u]);
}

static int pick_kb(void) {
    double x = rnd01();
    return x < 0.5 ? 1 : (x < 0.8 ? 2 : 3);
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
    t_end = t0 + limit * 0.92 - 0.3;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXD) { printf("1 0\n"); return 0; }
    if (D < 2) { printf("2 1\n0 1\n"); return 0; }

    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (!is_valid(&best)) complete_bipartite(&best);

    long moore = moore_bound();
    static Graph gbuf;
    while (now() < t_end) {
        if (best.n >= moore) break;
        double rem = t_end - now();
        if (rem < 0.3) break;
        int kb = pick_kb();
        int base = best.n / (2 * kb);
        int spread = base / 30 + 1;
        int Gt = base + 1 + rndint(spread);
        int ok = 0;
        for (int t = 0; t < 40 && !ok; t++) {
            if (pick_group(Gt)) ok = 1;
            else Gt++;
        }
        if (!ok) continue;
        int N = 2 * kb * GG;
        if (N > MAXN || N <= best.n || N > moore) continue;
        KB = kb;
        NN = N;
        double slice = 3.0 + 6.0 * rnd01();
        double dl = now() + slice;
        if (dl > t_end) dl = t_end;
        if (search(dl)) {
            build_graph(&gbuf);
            if (gbuf.n > best.n && is_valid(&gbuf)) best = gbuf;
        }
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
    """W(q) for the largest prime power q with q + 1 <= d (kept small for speed)."""
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d} has diameter 2, so it is valid for every D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(cand):
        nonlocal best
        if cand is None:
            return
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        try:
            consider(_best_pg(d))
        except Exception:
            pass
        # Exact Moore graph: nothing can beat it.
        if D == 3 and lib.is_prime_power(d - 1) and best[0] > 2 * d:
            return best
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass

    if D == 4:
        try:
            consider(_best_gq(d))
        except Exception:
            pass

    budget = 0.8 * time_limit - (time.monotonic() - t0) - 3.0
    if budget > 1.0 and best[0] < lib.moore_bound(d, D):
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             stdin_graph=best, timeout=budget + 8.0)
            consider(lib.parse_graph_text(text))
        except Exception:
            pass  # keep the valid Python graph

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
