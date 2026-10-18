"""Bi-Cayley annealing engine in C with exact orbit-reach checks, then grow-by-two.

New in this version: the bi-Cayley lift search (layers of block permutations plus
semidirect-product voltages) runs entirely in C. Reachability is tracked as one
bitmask per vertex over the 2k representative vertices. Left multiplication by the
group is an automorphism, so checking distance from each block representative to
every vertex is exact for the diameter. The search anneals over layer swaps and
voltages, biased toward vertices that are not yet fully reached, and keeps the best
valid graph. Python only supplies exact small constructions and glue.
"""
import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact and small constructions.
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


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# C engine: bi-Cayley annealing (new), then grow-by-two annealing.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
/* Bipartite degree-diameter search core.
 * Usage:  prog d D seed time_limit < start_graph
 * stdin:  "n m" + m edge lines (valid start), or "0 0".
 * stdout: "n m" + edge lines, the largest valid graph found.
 *
 * Phase 1: bi-Cayley annealing over Z_m x| Z_k2 with k blocks per side.
 *   A_{i,g} ~ B_{layer_l(i), g*s_{l,i}} for each layer l in 0..d-1.
 *   Left multiplication is an automorphism, so distance from block representatives
 *   to all vertices decides the diameter exactly. Reach masks are kept per vertex.
 * Phase 2: grow by two vertices with bipartite switch annealing.
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
#define MAXK 6
#define BPEN 100
#define PATIENCE 3000L
#define MAXITER 30000L

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

typedef struct {
    int m, k, r;
    int rp[MAXN];
} Grp;

static int d, D;
static double t_end;
static Graph best;

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

static void complete_bipartite(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= d; }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

/* Z_m x|_r Z_k: element (a,b) = a*k+b, (a,b)(c,e) = (a + r^b c mod m, b+e mod k). */
static int gmul(const Grp *G, int x, int y) {
    int a = x / G->k, b = x % G->k, c = y / G->k, e = y % G->k;
    return (int)((a + (long)G->rp[b] * c) % G->m) * G->k + (b + e) % G->k;
}

static int random_group(int N, Grp *G) {
    long count = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        int rmax = m > 1 ? m : 2;
        for (int r = 1; r < rmax; r++) {
            if (m > 1 && gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            count++;
            if (rndint((int)(count < 2000000000L ? count : 2000000000L)) == 0) {
                G->m = m; G->k = k; G->r = r;
            }
        }
    }
    if (!count) return 0;
    G->rp[0] = 1 % G->m;
    for (int b = 1; b < G->k; b++) G->rp[b] = (int)((long)G->rp[b - 1] * G->r % G->m);
    return 1;
}

/* ---------------- bi-Cayley annealing state ---------------- */

static int bk, bG, bN;
static Grp bgrp;
static int blayer[MAXD][MAXK];      /* A block i joins B block blayer[l][i] in layer l */
static int bvolt[MAXD][MAXK];       /* voltage of that dart */
static int bnbr[MAXD][MAXN];        /* neighbour of vertex v in layer l */
static int binv[MAXN];
static uint32_t maskA[MAXN], maskB[MAXN];
static uint32_t *bcur = NULL;

/* Write layer l's neighbours for A block i and the B block it hits. */
static void bset_dart(int l, int i) {
    int j = blayer[l][i], s = bvolt[l][i], si = binv[s];
    int *nb = bnbr[l];
    for (int g = 0; g < bG; g++) {
        nb[i * bG + g] = (bk + j) * bG + gmul(&bgrp, g, s);
        nb[(bk + j) * bG + g] = i * bG + gmul(&bgrp, g, si);
    }
}

static void bgroup_inverses(void) {
    for (int s = 0; s < bG; s++)
        for (int t = 0; t < bG; t++)
            if (gmul(&bgrp, s, t) == 0) { binv[s] = t; break; }
}

/* Unreached (representative, vertex) pairs; leaves the final masks in bcur. */
static long bc_cost(void) {
    int N = bN;
    uint32_t *cur = maskA, *nxt = maskB;
    for (int v = 0; v < N; v++) cur[v] = 0;
    for (int b = 0; b < 2 * bk; b++) cur[b * bG] = 1u << b;
    for (int t = 0; t < D; t++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint32_t r = cur[v];
            for (int l = 0; l < d; l++) r |= cur[bnbr[l][v]];
            nxt[v] = r;
            changed |= (r != cur[v]);
        }
        uint32_t *tmp = cur; cur = nxt; nxt = tmp;
        if (!changed) break;
    }
    bcur = cur;
    long unre = 0;
    int full_bits = 2 * bk;
    for (int v = 0; v < N; v++) unre += full_bits - __builtin_popcount(cur[v]);
    return unre;
}

/* Number of darts that repeat an (A block, B block, voltage) triple. */
static long bdup(void) {
    long c = 0;
    for (int i = 0; i < bk; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (blayer[l1][i] == blayer[l2][i] && bvolt[l1][i] == bvolt[l2][i]) c++;
    return c;
}

/* Pick a dart that touches a vertex still missing some representative. */
static int bad_pick(int *pl, int *pi) {
    uint32_t full = (1u << (2 * bk)) - 1u;
    for (int tries = 0; tries < 20; tries++) {
        int v = rndint(bN);
        if (bcur[v] == full) continue;
        int b = v / bG;
        int l = rndint(d);
        if (b < bk) { *pl = l; *pi = b; return 1; }
        int j = b - bk;
        for (int i = 0; i < bk; i++)
            if (blayer[l][i] == j) { *pl = l; *pi = i; return 1; }
    }
    return 0;
}

/* One annealing run for block count k and group order G. Returns 1 if a valid lift was found. */
static int bc_run(int k, int G, long max_iters, double until) {
    bk = k; bG = G; bN = 2 * k * G;
    if (!random_group(G, &bgrp)) return 0;
    bgroup_inverses();
    for (int l = 0; l < d; l++) {
        int perm[MAXK];
        for (int i = 0; i < k; i++) perm[i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int s = perm[i]; perm[i] = perm[j]; perm[j] = s;
        }
        for (int i = 0; i < k; i++) {
            blayer[l][i] = perm[i];
            bvolt[l][i] = rndint(G);
            bset_dart(l, i);
        }
    }
    long cost = bc_cost() + BPEN * bdup();
    long best_cost = cost, last = 0;
    for (long t = 0; t < max_iters && cost > 0; t++) {
        if (t - last > PATIENCE) break;
        if ((t & 31) == 0 && now() > until) break;
        double T = 0.05 + 3.0 * (1.0 - (double)t / (double)max_iters);
        if (k >= 2 && rnd01() < 0.25) {
            int l = rndint(d);
            int i1 = rndint(k), i2 = rndint(k - 1);
            if (i2 >= i1) i2++;
            int s1 = blayer[l][i1]; blayer[l][i1] = blayer[l][i2]; blayer[l][i2] = s1;
            bset_dart(l, i1); bset_dart(l, i2);
            long c2 = bc_cost() + BPEN * bdup();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                s1 = blayer[l][i1]; blayer[l][i1] = blayer[l][i2]; blayer[l][i2] = s1;
                bset_dart(l, i1); bset_dart(l, i2);
            }
        } else {
            int l, i;
            if (!(rnd01() < 0.5 && bad_pick(&l, &i))) { l = rndint(d); i = rndint(k); }
            int old = bvolt[l][i];
            int nw = rndint(G);
            if (nw == old) continue;
            bvolt[l][i] = nw;
            bset_dart(l, i);
            long c2 = bc_cost() + BPEN * bdup();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                bvolt[l][i] = old;
                bset_dart(l, i);
            }
        }
        if (cost < best_cost) { best_cost = cost; last = t; }
    }
    return cost == 0;
}

static void bc_to_graph(Graph *g) {
    int A = bk * bG;
    g->n = bN;
    for (int v = 0; v < bN; v++) { g->deg[v] = 0; g->side[v] = v >= A; }
    for (int u = 0; u < A; u++)
        for (int l = 0; l < d; l++) add_edge(g, u, bnbr[l][u]);
}

/* Repeatedly try bi-Cayley lifts with orders just above the current best. */
static void bicayley_phase(double until) {
    long trials[MAXK + 1], wins[MAXK + 1];
    for (int c = 0; c <= MAXK; c++) { trials[c] = 0; wins[c] = 0; }
    static Graph cand;
    while (now() < until) {
        if (best.n + 2 > moore_bound()) return;
        int k;
        if (rnd01() < 0.2) {
            k = 1 + rndint(MAXK);
        } else {
            double bs = -1.0;
            k = 1;
            for (int c = 1; c <= MAXK; c++) {
                double sc = (wins[c] + 1.0) / (trials[c] + 2.0) + 0.05 * rnd01();
                if (sc > bs) { bs = sc; k = c; }
            }
        }
        int minG = best.n / (2 * k) + 1;
        int G = minG + rndint(3);
        if (2L * k * G > MAXN || 2L * k * G > moore_bound()) continue;
        trials[k]++;
        if (!bc_run(k, G, MAXITER, until)) continue;
        bc_to_graph(&cand);
        if (cand.n > best.n && is_valid(&cand)) {
            copy_graph(&best, &cand);
            wins[k]++;
        }
    }
}

/* ---------------- grow-by-two annealing ---------------- */

static int grow_once(const Graph *src, Graph *work, double until) {
    int n = src->n;
    if (n + 2 > moore_bound() || n + 2 > MAXN) return 0;
    copy_graph(work, src);
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

static void grow_search(Graph *cur, double until) {
    static Graph work;
    while (now() < until && cur->n + 2 <= moore_bound()) {
        double left = until - now();
        double slice = left < 4.0 ? left : (left / 4 > 4.0 ? left / 4 : 4.0);
        if (grow_once(cur, &work, now() + slice)) copy_graph(cur, &work);
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
    t_end = t0 + limit * 0.92;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXD || D < 1) { printf("1 0\n"); return 0; }
    if (D == 1) { printf("2 1\n0 1\n"); return 0; }

    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (!is_valid(&best)) complete_bipartite(&best);

    double split = t0 + (t_end - t0) * 0.7;
    bicayley_phase(split);
    grow_search(&best, t_end);

    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    usable = max(1.0, 0.85 * time_limit - 3.0)
    end = t0 + usable

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        """Adopt (n, e) if it is a larger valid graph."""
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact constructions.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            ar = lib.araujo_lopez_graph(d - 2)
            consider(ar[0], ar[1])
        except (ValueError, RuntimeError):
            pass
    if D == 4 and time.monotonic() < end:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # C engine: bi-Cayley annealing, then grow-by-two, starting from the best so far.
    if D >= 2:
        c_budget = end - time.monotonic() - 0.5
        if c_budget > 1.0:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(c_budget, 2)],
                                 stdin_graph=best, timeout=c_budget + 8)
                n, e = lib.parse_graph_text(text)
                consider(n, e)
            except (RuntimeError, ValueError):
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
