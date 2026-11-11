"""Combined program: known constructions as start graphs, a C engine that runs bi-Cayley
(voltage-lift) annealing over semidirect products Z_m x| Z_k, then grows the best graph by two.

build() always returns a valid graph: every C result is re-checked with lib.is_valid, and
any failure falls back to the best graph already held in Python.
"""
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
 * Phase 1 (bi-Cayley annealing): a d-regular bipartite graph on 2kG vertices, where G is a
 *   semidirect product Z_m x|_r Z_k2 (order G) and k is the number of base vertices per side.
 *   Layer l is a permutation sigma_l of the k A-blocks onto the k B-blocks, with a voltage
 *   S[l][i]: A(i,x) ~ B(sigma_l(i), x*S[l][i]). Left multiplication is an automorphism, so
 *   diameter <= D holds iff every block representative reaches all vertices within D steps.
 *   Reach is a bitmask over the 2k representatives, which keeps each evaluation cheap.
 * Phase 2 (grow by two): add one vertex per side using the spare degree of d-1 deleted edges,
 *   then anneal degree-preserving 2-switches until the diameter is <= D.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 10000
#define MAXD 32
#define MAXW ((MAXN + 63) / 64)
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

/* Number of unordered pairs at distance > D. Bitset reachability per vertex. */
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

/* K_{d,d}: valid for D >= 2. */
static void complete_bipartite(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= d; }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

/* Single vertex: valid for every D. */
static void single_vertex(Graph *g) {
    g->n = 1;
    g->deg[0] = 0;
    g->side[0] = 0;
}

/* ------------------------------------------------------------------ groups */

/* Z_m x|_r Z_k: element (a, b) is the int a*k + b, (a,b)(c,e) = (a + r^b c mod m, b + e mod k). */
typedef struct {
    int m, k, r;
    int rp[64]; /* rp[b] = r^b mod m */
} Grp;

static int gmul(const Grp *G, int x, int y) {
    int k = G->k;
    int a = x / k, b = x % k, c = y / k, e = y % k;
    long t = ((long)a + (long)G->rp[b] * c) % G->m;
    return (int)(t * k + (b + e) % k);
}

/* Random group of order >= target with a valid r. Returns 1 on success. */
static int sample_group(int target, Grp *G) {
    static const int K2[] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36};
    for (int tries = 0; tries < 200; tries++) {
        int k2 = K2[rndint(20)];
        int m = (target + k2 - 1) / k2;
        if (m < 3) continue;
        int r = -1;
        if (k2 == 1) {
            r = 1;
        } else if (k2 == 2 && rndint(10) < 3) {
            r = m - 1;
            if (gcd(r, m) != 1 || powmod(r, 2, m) != 1 % m) r = -1;
        } else {
            for (int t = 0; t < 60; t++) {
                int c = 2 + rndint(m - 2);
                if (gcd(c, m) == 1 && powmod(c, k2, m) == 1 % m) { r = c; break; }
            }
        }
        if (r < 0) continue;
        G->m = m;
        G->k = k2;
        G->r = r;
        G->rp[0] = 1 % m;
        for (int b = 1; b < k2; b++) G->rp[b] = (int)((long)G->rp[b - 1] * r % m);
        return 1;
    }
    return 0;
}

/* ------------------------------------------------------------------ bi-Cayley search */

typedef struct {
    int k, G, N;
    Grp grp;
    int layers[MAXD][MAXK];      /* layers[l][i] = B-block paired with A-block i in layer l */
    int S[MAXD][MAXK];           /* voltage of that dart */
    int nbr[MAXD][MAXN];         /* nbr[l][v]: layer-l partner of vertex v (an involution) */
} BC;

static uint64_t bufA[MAXN], bufB[MAXN];

static void bc_set_dart(BC *st, int l, int i) {
    int k = st->k, G = st->G, j = st->layers[l][i], s = st->S[l][i];
    int bbase = (k + j) * G;
    for (int x = 0; x < G; x++) {
        int y = gmul(&st->grp, x, s);
        int a = i * G + x, b = bbase + y;
        st->nbr[l][a] = b;
        st->nbr[l][b] = a;
    }
}

/* Reach bitmask per vertex: bit b set iff representative of block b is within D steps. */
static void bc_reach(const BC *st, uint64_t *out) {
    int N = st->N, k = st->k, G = st->G;
    uint64_t *cur = bufA, *nxt = bufB;
    for (int v = 0; v < N; v++) cur[v] = 0;
    for (int b = 0; b < 2 * k; b++) cur[(size_t)b * G] = 1ULL << b;
    for (int r = 0; r < D; r++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint64_t x = cur[v];
            for (int l = 0; l < d; l++) x |= cur[st->nbr[l][v]];
            nxt[v] = x;
            if (x != cur[v]) changed = 1;
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
        if (!changed) break;
    }
    memcpy(out, cur, sizeof(uint64_t) * (size_t)N);
}

/* Unreached (vertex, representative) pairs plus a penalty for duplicate darts. */
static long bc_cost(const BC *st, const uint64_t *reach) {
    int k = st->k;
    uint64_t full = (1ULL << (2 * k)) - 1;
    long c = 0;
    for (int v = 0; v < st->N; v++) c += __builtin_popcountll(full & ~reach[v]);
    long dup = 0;
    for (int i = 0; i < k; i++)
        for (int l = 0; l < d; l++)
            for (int l2 = l + 1; l2 < d; l2++)
                if (st->layers[l][i] == st->layers[l2][i] && st->S[l][i] == st->S[l2][i]) dup++;
    return c + (long)PEN * dup;
}

static void bc_init(BC *st) {
    int k = st->k;
    for (int l = 0; l < d; l++) {
        int p[MAXK];
        for (int i = 0; i < k; i++) p[i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rndint(i + 1), t = p[i];
            p[i] = p[j];
            p[j] = t;
        }
        for (int i = 0; i < k; i++) {
            st->layers[l][i] = p[i];
            st->S[l][i] = rndint(st->G);
        }
    }
    for (int l = 0; l < d; l++)
        for (int i = 0; i < k; i++) bc_set_dart(st, l, i);
}

/* Simulated annealing on layers and voltages. Returns 1 when cost reaches 0. */
static int bc_search(BC *st, double until, long iters, long patience) {
    static uint64_t reach[MAXN], nreach[MAXN];
    int k = st->k, N = st->N, G = st->G;
    uint64_t full = (1ULL << (2 * k)) - 1;
    bc_init(st);
    bc_reach(st, reach);
    long cost = bc_cost(st, reach);
    double c0 = cost > 0 ? (double)cost : 1.0;
    long best = cost, last = 0;
    for (long t = 0; t < iters; t++) {
        if (cost == 0) return 1;
        if ((t & 15) == 0 && now() > until) return 0;
        if (t - last > patience) return 0;
        double temp = 0.01 * c0 * (1.0 - (double)t / (double)iters);
        if (temp < 0.5) temp = 0.5;

        if (k >= 2 && rnd01() < 0.25) {
            /* Layer-swap move: exchange the B-targets of two A-blocks in one layer. */
            int l = rndint(d);
            int i1 = rndint(k), i2 = rndint(k - 1);
            if (i2 >= i1) i2++;
            int tmp = st->layers[l][i1];
            st->layers[l][i1] = st->layers[l][i2];
            st->layers[l][i2] = tmp;
            bc_set_dart(st, l, i1);
            bc_set_dart(st, l, i2);
            bc_reach(st, nreach);
            long nc = bc_cost(st, nreach);
            if (nc <= cost || rnd01() < exp(-(double)(nc - cost) / temp)) {
                cost = nc;
                memcpy(reach, nreach, sizeof(uint64_t) * (size_t)N);
                if (cost < best) { best = cost; last = t; }
            } else {
                tmp = st->layers[l][i1];
                st->layers[l][i1] = st->layers[l][i2];
                st->layers[l][i2] = tmp;
                bc_set_dart(st, l, i1);
                bc_set_dart(st, l, i2);
            }
            continue;
        }

        /* Voltage move: defect-targeted with probability 0.4, otherwise uniform. */
        int l = -1, i = -1;
        if (rnd01() < 0.4) {
            int v = -1;
            for (int tr = 0; tr < 30; tr++) {
                int u = rndint(N);
                if (reach[u] != full) { v = u; break; }
            }
            if (v >= 0) {
                int blk = v / G;
                l = rndint(d);
                if (blk < k) {
                    i = blk;
                } else {
                    int j = blk - k;
                    i = 0;
                    for (int ii = 0; ii < k; ii++)
                        if (st->layers[l][ii] == j) { i = ii; break; }
                }
            }
        }
        if (l < 0) {
            l = rndint(d);
            i = rndint(k);
        }
        int old = st->S[l][i];
        int nw = rndint(G);
        if (nw == old) continue;
        st->S[l][i] = nw;
        bc_set_dart(st, l, i);
        bc_reach(st, nreach);
        long nc = bc_cost(st, nreach);
        if (nc <= cost || rnd01() < exp(-(double)(nc - cost) / temp)) {
            cost = nc;
            memcpy(reach, nreach, sizeof(uint64_t) * (size_t)N);
            if (cost < best) { best = cost; last = t; }
        } else {
            st->S[l][i] = old;
            bc_set_dart(st, l, i);
        }
    }
    return cost == 0;
}

static void bc_to_graph(const BC *st, Graph *g) {
    int N = st->N, A = st->k * st->G;
    g->n = N;
    for (int v = 0; v < N; v++) {
        g->deg[v] = 0;
        g->side[v] = v >= A;
    }
    for (int l = 0; l < d; l++)
        for (int a = 0; a < A; a++) add_edge(g, a, st->nbr[l][a]);
}

/* Bandit over base sizes k; each trial is a fresh random bi-Cayley graph above best->n. */
static void bc_phase(Graph *best, double until) {
    static BC st;
    static Graph cand;
    static int trials[MAXK + 1], wins[MAXK + 1];
    long moore = moore_bound();
    int fails = 0;
    while (now() < until && fails < 3000) {
        int k;
        if (rnd01() < 0.2) {
            k = 1 + rndint(MAXK);
        } else {
            double bv = -1.0;
            k = 1;
            for (int kk = 1; kk <= MAXK; kk++) {
                double v = (wins[kk] + 1.0) / (trials[kk] + 2.0) + 0.02 * rnd01();
                if (v > bv) { bv = v; k = kk; }
            }
        }
        int gt = best->n / (2 * k) + 1 + rndint(best->n / (8 * k) + 2);
        if (gt < d + 1) gt = d + 1;
        if (!sample_group(gt, &st.grp)) { fails++; continue; }
        st.k = k;
        st.G = st.grp.m * st.grp.k;
        st.N = 2 * k * st.G;
        if (st.N <= best->n || st.N > moore || st.N > MAXN) { fails++; continue; }
        fails = 0;
        trials[k]++;
        if (bc_search(&st, until, 15000, 2500)) {
            bc_to_graph(&st, &cand);
            if (cand.n > best->n && is_valid(&cand)) {
                copy_graph(best, &cand);
                wins[k]++;
            }
        }
    }
}

/* ------------------------------------------------------------------ grow by two */

/* Insert one new vertex per side into a copy of best (degree d each), then anneal 2-switches. */
static int grow_once(const Graph *best, Graph *work, double until) {
    int n = best->n;
    if (n + 2 > moore_bound() || n + 2 > MAXN) return 0;
    copy_graph(work, best);
    int x = n, y = n + 1;
    work->n = n + 2;
    work->deg[x] = 0;
    work->deg[y] = 0;
    work->side[x] = 0;
    work->side[y] = 1;
    add_edge(work, x, y);
    static int used[MAXN];
    static int stamp = 0;
    stamp++;
    used[x] = stamp;
    used[y] = stamp;
    for (int k = 0, tries = 0; k < d - 1 && tries < 100000; tries++) {
        int a = rndint(n);
        if (work->side[a] != 0 || used[a] == stamp || work->deg[a] == 0) continue;
        int b = work->adj[a][rndint(work->deg[a])];
        if (used[b] == stamp) continue;
        del_edge(work, a, b);
        add_edge(work, x, b);
        add_edge(work, y, a);
        used[a] = stamp;
        used[b] = stamp;
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
    if (limit > 3.0) t_end = t0 + limit - 1.0;
    else t_end = t0 + limit * 0.8;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best;
    if (d < 1 || D < 1 || d > MAXD || 2 * d > MAXN) {
        printf("0 0\n");
        return 0;
    }
    read_start(&best);
    if (best.n == 0) {
        if (D >= 2) complete_bipartite(&best);
        else single_vertex(&best);
    }
    if (D >= 2 && best.n < moore_bound()) {
        double tn = now();
        double span = t_end - tn;
        if (span > 0.5) {
            bc_phase(&best, tn + 0.8 * span);
            grow_search(&best, t_end);
        }
    }
    if (!is_valid(&best)) {
        if (D >= 2) complete_bipartite(&best);
        else single_vertex(&best);
    }
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
    edges = [(p, P + j) for j, L in enumerate(lines) for p in L]
    return 2 * P, edges


def _known_starts(d, D):
    """Constructions Python can build directly; each is re-validated before use."""
    out = []
    if D >= 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                out.append(lib.projective_plane_incidence(q))   # diameter 3
                break
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        out.append(lib.araujo_lopez_graph(d - 2))               # diameter 3 record family
    if D >= 4:
        for q in range(min(d - 1, 9), 1, -1):
            if lib.is_prime_power(q):
                out.append(_gq_w(q))                            # diameter 4
                break
    return out


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))   # K_{d,d}: diameter 2, always valid for D >= 2
    for cand in _known_starts(d, D):
        try:
            if cand[0] > best[0] and lib.is_valid(cand[0], cand[1], d, D):
                best = cand
        except Exception:
            pass

    if best[0] >= lib.moore_bound(d, D):
        return best   # nothing beats a Moore graph

    budget = 0.85 * time_limit - 3.0 - (time.monotonic() - t0)
    if budget < 1.0:
        return best

    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=best, timeout=budget + 10)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass   # keep the valid Python fallback
    return best
