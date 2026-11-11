"""Combined program: Python picks the best known start graph, C runs bi-Cayley lift
annealing (from g000-i00's approach, in C) and then grow-by-two annealing (from g000-seed)."""
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
 * Phase 1 (bi-Cayley lifts): vertices A_{i,g} = i*G+g, B_{j,h} = (k+j)*G+h, group
 *   G = Z_m x| Z_k2 (order G). Layer l maps A-block i to B-block Lay[l][i] with voltage
 *   Sv[l][i]: A_{i,g} ~ B_{Lay, g*s}. Each layer is a permutation, so the graph is
 *   d-regular and bipartite. Simulated annealing on voltages and layer permutations,
 *   cost = (block, vertex) pairs not reached within D + penalty for duplicate darts.
 *   Left multiplication is an automorphism, so checking all vertices against the
 *   2k block identities is enough for diameter <= D.
 * Phase 2 (grow by two): add one vertex per side using spare degree of d-1 removed
 *   edges, then anneal degree-preserving edge swaps until diameter <= D.
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
#define PEN 1000

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static double t_end;

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
            memcpy(dst, src, sizeof(uint64_t) * W);
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

/* Full validity: simple, bipartite (by side labels), degree <= d, diameter <= D. */
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

/* Z_m x|_r Z_k: element (a, b) is the int a*k + b; (a,b)(c,e) = (a + r^b c mod m, b + e mod k). */
typedef struct {
    int m, k, r;
    int rp[MAXN]; /* rp[b] = r^b mod m */
} Grp;

static Grp grp;

static int gmul(int x, int y) {
    int a = x / grp.k, b = x % grp.k, c = y / grp.k, e = y % grp.k;
    return (int)(((long)a + (long)grp.rp[b] * c) % grp.m) * grp.k + (b + e) % grp.k;
}

/* Uniform random (m, k, r) with m*k = G, gcd(r, m) = 1, r^k = 1 mod m. Fills grp. */
static int random_group(int G) {
    long count = 0;
    int bm = 1, bk = G, br = 0;
    for (int m = 1; m <= G; m++) {
        if (G % m) continue;
        int k = G / m;
        if (m == 1) {
            count++;
            if (rndint((int)count) == 0) { bm = 1; bk = k; br = 0; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            count++;
            if (rndint((int)count) == 0) { bm = m; bk = k; br = r; }
        }
    }
    if (!count) return 0;
    grp.m = bm;
    grp.k = bk;
    grp.r = br;
    grp.rp[0] = 1 % bm;
    for (int b = 1; b < bk; b++) grp.rp[b] = (int)((long)grp.rp[b - 1] * br % bm);
    return 1;
}

/* ------------------------------------------------------------------ bi-Cayley lifts */

static int K, GG;
static int Lay[MAXD][MAXK], Sv[MAXD][MAXK];
static int nbr[MAXD][MAXN];
static uint32_t rc[MAXN], rt[MAXN], rtmp[MAXN];
static long lk_wins[MAXK + 1], lk_trials[MAXK + 1];

/* Fill nbr from Lay and Sv. Each layer is a permutation, so every vertex gets one neighbour per layer. */
static void build_nbr(void) {
    int k = K, G = GG;
    for (int l = 0; l < d; l++)
        for (int i = 0; i < k; i++) {
            int j = Lay[l][i], s = Sv[l][i];
            for (int g = 0; g < G; g++) {
                int h = gmul(g, s);
                int u = i * G + g, w = (k + j) * G + h;
                nbr[l][u] = w;
                nbr[l][w] = u;
            }
        }
}

/* Cost = unreached (block-identity, vertex) pairs + PEN * duplicate darts. Result in rt. */
static long lift_cost(void) {
    int k = K, G = GG, N = 2 * k * G;
    for (int v = 0; v < N; v++) rt[v] = 0;
    for (int b = 0; b < 2 * k; b++) rt[b * G] = 1u << b;
    for (int r = 0; r < D; r++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint32_t x = rt[v];
            for (int l = 0; l < d; l++) x |= rt[nbr[l][v]];
            rtmp[v] = x;
            if (x != rt[v]) changed = 1;
        }
        memcpy(rt, rtmp, sizeof(uint32_t) * N);
        if (!changed) break;
    }
    long unreached = 0;
    for (int v = 0; v < N; v++) unreached += 2 * k - __builtin_popcount(rt[v]);
    long dup = 0;
    for (int i = 0; i < k; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (Lay[l1][i] == Lay[l2][i] && Sv[l1][i] == Sv[l2][i]) dup++;
    return unreached + (long)PEN * dup;
}

static void graph_from_lift(Graph *g) {
    int k = K, G = GG, N = 2 * k * G;
    g->n = N;
    for (int v = 0; v < N; v++) { g->deg[v] = 0; g->side[v] = v >= k * G; }
    for (int u = 0; u < k * G; u++)
        for (int l = 0; l < d; l++) add_edge(g, u, nbr[l][u]);
}

static int pick_k(void) {
    if (rnd01() < 0.2) return 1 + rndint(MAXK);
    int bk = 1;
    double bs = -1.0;
    for (int k = 1; k <= MAXK; k++) {
        double s = (lk_wins[k] + 1.0) / (lk_trials[k] + 2.0) + 0.02 * rnd01();
        if (s > bs) { bs = s; bk = k; }
    }
    return bk;
}

/* Simulated annealing on the lift with the current K, GG. Returns 1 if cost reached 0. */
static int lift_anneal(long iters, long patience, double until) {
    int k = K, G = GG, N = 2 * k * G;
    uint32_t full = (1u << (2 * k)) - 1;
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < k; i++) Lay[l][i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rndint(i + 1), s = Lay[l][i];
            Lay[l][i] = Lay[l][j];
            Lay[l][j] = s;
        }
        for (int i = 0; i < k; i++) Sv[l][i] = rndint(G);
    }
    build_nbr();
    long cost = lift_cost();
    memcpy(rc, rt, sizeof(uint32_t) * N);
    long c0 = cost > 0 ? cost : 1, best_c = cost, last = 0;

    for (long t = 0; t < iters && cost > 0; t++) {
        if ((t & 31) == 0 && now() > until) break;
        if (t - last > patience) break;
        double temp = 0.05 * (double)c0 * (1.0 - (double)t / (double)iters) + 0.5;

        if (k >= 2 && rnd01() < 0.2) {
            /* layer-swap move: exchange B-targets of two A-blocks in one layer */
            int l = rndint(d), i1 = rndint(k), i2 = rndint(k);
            if (i1 == i2) continue;
            int tmp = Lay[l][i1];
            Lay[l][i1] = Lay[l][i2];
            Lay[l][i2] = tmp;
            build_nbr();
            long c2 = lift_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                memcpy(rc, rt, sizeof(uint32_t) * N);
                if (cost < best_c) { best_c = cost; last = t; }
            } else {
                tmp = Lay[l][i1];
                Lay[l][i1] = Lay[l][i2];
                Lay[l][i2] = tmp;
                build_nbr();
            }
            continue;
        }

        /* voltage move, defect-targeted half of the time */
        int l = rndint(d), i = rndint(k);
        if (rnd01() < 0.5) {
            int v0 = rndint(N), v = -1;
            for (int q = 0; q < N; q++) {
                int w = (v0 + q) % N;
                if (rc[w] != full) { v = w; break; }
            }
            if (v >= 0) {
                int c = v / G;
                if (c < k) {
                    i = c;
                } else {
                    int j = c - k;
                    for (int ii = 0; ii < k; ii++)
                        if (Lay[l][ii] == j) { i = ii; break; }
                }
            }
        }
        int old = Sv[l][i];
        int nw = rndint(G);
        if (nw == old) continue;
        Sv[l][i] = nw;
        build_nbr();
        long c2 = lift_cost();
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
            memcpy(rc, rt, sizeof(uint32_t) * N);
            if (cost < best_c) { best_c = cost; last = t; }
        } else {
            Sv[l][i] = old;
            build_nbr();
        }
    }
    return cost == 0;
}

static void lift_search(Graph *best, double until) {
    static Graph cand;
    long moore = moore_bound();
    int fails = 0;
    while (now() < until) {
        int k = pick_k();
        long need = best->n + 2;
        long G = (need + 2L * k - 1) / (2L * k);
        G += rndint((int)(G / 20 + 2));
        if (G < 1 || 2L * k * G > moore || 2L * k * G > MAXN) {
            if (++fails > 5000) return;
            continue;
        }
        if (!random_group((int)G)) continue;
        K = k;
        GG = (int)G;
        lk_trials[k]++;
        double cap = now() + 4.0;
        if (cap > until) cap = until;
        if (lift_anneal(8000, 2000, cap)) {
            graph_from_lift(&cand);
            if (cand.n > best->n && is_valid(&cand)) {
                copy_graph(best, &cand);
                lk_wins[k]++;
            }
        }
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
    t_end = t0 + limit * 0.9;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXD || D < 1) { printf("1 0\n"); return 0; }
    if (D == 1) { printf("2 1\n0 1\n"); return 0; }

    static Graph best;
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);

    if (best.n < moore_bound()) {
        double tn = now();
        double frac = best.n > 2 * d ? 0.55 : 0.7;
        lift_search(&best, tn + (t_end - tn) * frac);
        grow_search(&best, t_end);
    }
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


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
    """W(q) for the largest small prime power q with q + 1 <= d."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}: diameter 2, always valid for D >= 2
    if D == 2:
        return best

    def consider(cand):
        nonlocal best
        if cand is not None and cand[0] > best[0] and lib.is_valid(cand[0], cand[1], d, D):
            best = cand

    # Exact or known record constructions.
    if D == 3:
        if d - 1 >= 2 and lib.is_prime_power(d - 1):
            consider(lib.projective_plane_incidence(d - 1))  # Moore graph: optimal
            return best
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            consider(lib.araujo_lopez_graph(d - 2))          # record start graph
    if D == 4:
        consider(_best_gq(d))
        if d - 1 <= 9 and d - 1 >= 2 and lib.is_prime_power(d - 1):
            return best

    # C search: lifts, then grow by two, starting from the best valid graph.
    budget = 0.8 * time_limit - 1.5 - (time.monotonic() - t0)
    if budget < 1.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=best, timeout=budget + 8)
        consider(lib.parse_graph_text(text))
    except Exception:
        pass
    return best
