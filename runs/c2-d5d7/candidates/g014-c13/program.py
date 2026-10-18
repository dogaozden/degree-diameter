"""Frobenius-group sweep for bi-Cayley lifts, plus ruin-free pair growth, for the d=5, D=7 target.

New in this version: a faithful Frobenius-group sampler (frob_group). For a prime m and k | m-1,
the group Z_m x| Z_k with r of exact order k mod m acts faithfully. It is non-abelian, and it
exists only for sparse orders N = m*k. The parent sampled groups uniformly over all admissible
semidirect products, which mostly picks abelian or non-faithful ones and rarely hits the
sparse orders above the record half-order. The new phase 1 sweeps every order N above the
current half-order in ascending order and tries a faithful Frobenius group at each N that has
one. For d=5 this reaches N = 41*40 = 1640 (order 3280 graph), above the record 3110. Phase 2
keeps the random semidirect sampling. Phase 3 grows the best graph one vertex pair at a time.

Every candidate is verified in C with bitset diameter checks and again in Python with lib.is_valid.
The hexagon incidence graph H(4) (order 2730, valid for D=7) is the algebraic fallback.
"""
import itertools
import time

import numpy as np

import lib

C_SOURCE = r'''
/* Bi-Cayley lift search with faithful Frobenius groups, then pair growth.
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v", or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
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
#define MAXH 2048
#define BC_STEPS 6000
#define BC_ATTEMPTS 8
#define SWEEP_ATTEMPTS 3
#define INIT_TRIALS 6

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static double t_end;

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

static int is_prime(int x) {
    if (x < 2) return 0;
    for (int f = 2; f * f <= x; f++)
        if (x % f == 0) return 0;
    return 1;
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

/* Number of unordered pairs at distance > D, by bitset BFS; fills badv. */
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

/* ---------------- groups: Z_m x|_r Z_k, element a*k + b ---------------- */
typedef struct {
    int m, k, r;
    int rp[MAXN];
} Grp;

static int gmul(const Grp *G, int x, int y) {
    int a = x / G->k, b = x % G->k, c = y / G->k, e = y % G->k;
    return (int)((a + (long)G->rp[b] * c) % G->m) * G->k + (b + e) % G->k;
}

static int MTAB[MAXH * MAXH];
static int INVT[MAXH];
static int NN;

/* Fill the multiplication table of G (order N), its inverses, and set NN. */
static void fill_group(int N, Grp *G) {
    G->rp[0] = 1 % G->m;
    for (int b = 1; b < G->k; b++) G->rp[b] = (int)((long)G->rp[b - 1] * G->r % G->m);
    NN = N;
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            MTAB[(size_t)x * N + y] = gmul(G, x, y);
    for (int x = 0; x < N; x++) {
        INVT[x] = 0;
        for (int y = 0; y < N; y++)
            if (MTAB[(size_t)x * N + y] == 0) { INVT[x] = y; break; }
    }
}

/* Uniformly random admissible semidirect product of order N (reservoir sampling). */
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
    return count > 0;
}

/* NEW HELPER: faithful Frobenius-type group Z_m x| Z_k with m prime, k | m-1, k >= 2,
 * and r of EXACT order k mod m. Returns the number of such (m, r) choices; with pick set,
 * one choice is sampled uniformly into G. Such groups act faithfully, so they are the
 * most non-abelian choices of order N = m*k. */
static int frob_group(int N, Grp *G, int pick) {
    long cnt = 0;
    for (int m = 3; m <= N; m++) {
        if (N % m || !is_prime(m)) continue;
        int k = N / m;
        if (k < 2 || (m - 1) % k) continue;
        for (int r = 2; r < m; r++) {
            if (powmod(r, k, m) != 1) continue;
            int ord = 0;
            long x = 1;
            for (int t = 1; t <= k; t++) {
                x = x * r % m;
                if (x == 1) { ord = t; break; }
            }
            if (ord != k) continue;
            cnt++;
            if (pick && rndint((int)(cnt < 2000000000L ? cnt : 2000000000L)) == 0) {
                G->m = m; G->k = k; G->r = r;
            }
        }
    }
    return cnt > 0;
}

/* ---------------- bi-Cayley lift search ----------------
 * Vertices: a_x = x (side 0), b_x = N + x (side 1), x in G.
 * Edges: a_x -- b_{x * g_t} for t = 0..d-1, with g_0 = e (index 0) and distinct g_t.
 * Left multiplication is transitive on each side, so BFS from a_e and b_e suffices. */

static int dist_bc[2 * MAXH], seen_bc[2 * MAXH], q_bc[2 * MAXH];
static int stamp_bc = 0;
static Graph bc_cand;

static int used_upto(const int *gv, int cnt, int v) {
    for (int i = 0; i < cnt; i++)
        if (gv[i] == v) return 1;
    return 0;
}

/* Number of (source, vertex) pairs at distance > D, sources a_e and b_e. */
static long eval_bad(const int *gv) {
    int N = NN, V = 2 * N;
    int gi[MAXD];
    for (int t = 0; t < d; t++) gi[t] = INVT[gv[t]];
    long total = 0;
    for (int s = 0; s < 2; s++) {
        int src = s ? N : 0;
        int head = 0, tail = 0;
        stamp_bc++;
        seen_bc[src] = stamp_bc;
        dist_bc[src] = 0;
        q_bc[tail++] = src;
        while (head < tail) {
            int v = q_bc[head++];
            int dv = dist_bc[v];
            if (dv >= D) continue;
            if (v < N) {
                const int *row = MTAB + (size_t)v * N;
                for (int t = 0; t < d; t++) {
                    int u = N + row[gv[t]];
                    if (seen_bc[u] != stamp_bc) {
                        seen_bc[u] = stamp_bc;
                        dist_bc[u] = dv + 1;
                        q_bc[tail++] = u;
                    }
                }
            } else {
                const int *row = MTAB + (size_t)(v - N) * N;
                for (int t = 0; t < d; t++) {
                    int u = row[gi[t]];
                    if (seen_bc[u] != stamp_bc) {
                        seen_bc[u] = stamp_bc;
                        dist_bc[u] = dv + 1;
                        q_bc[tail++] = u;
                    }
                }
            }
        }
        total += V - tail;
    }
    return total;
}

/* Annealed voltage hill-climb; gv[0] = 0 (identity) is kept fixed. */
static long climb(int *gv, long steps, double until) {
    long bad = eval_bad(gv);
    double T = 2.0;
    for (long s = 0; s < steps && bad > 0; s++) {
        if ((s & 127) == 0 && now() > until) break;
        int t = 1 + rndint(d - 1);
        int old = gv[t], nv;
        do { nv = rndint(NN); } while (used_upto(gv, d, nv));
        gv[t] = nv;
        long nb = eval_bad(gv);
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) bad = nb;
        else gv[t] = old;
        T *= 0.9997;
        if (T < 0.2) T = 0.2;
    }
    return bad;
}

static void build_bc(Graph *g, int N, const int *gv) {
    g->n = 2 * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= N; }
    for (int x = 0; x < N; x++)
        for (int t = 0; t < d; t++)
            add_edge(g, x, N + MTAB[(size_t)x * N + gv[t]]);
}

/* Random voltages on the currently filled group; improves best on success. */
static int try_order(Graph *best, int N, int attempts, long steps, double until) {
    int gv[MAXD];
    for (int att = 0; att < attempts && now() < until; att++) {
        gv[0] = 0;
        for (int t = 1; t < d; t++) {
            do { gv[t] = rndint(N); } while (used_upto(gv, t, gv[t]));
        }
        if (climb(gv, steps, until) != 0) continue;
        build_bc(&bc_cand, N, gv);
        if (bc_cand.n > best->n && is_valid(&bc_cand)) {
            copy_graph(best, &bc_cand);
            return 1;
        }
    }
    return 0;
}

static int bc_nmax(void) {
    long m = moore_bound() / 2;
    if (m > MAXH) m = MAXH;
    if (m > MAXN / 2) m = MAXN / 2;
    return (int)m;
}

/* Phase 1 (new): ascending sweep over orders N > best/2 that admit a faithful Frobenius group. */
static void frob_sweep(Graph *best, double until) {
    static Grp G;
    int Nmax = bc_nmax();
    for (int N = best->n / 2 + 1; N <= Nmax && now() < until; N++) {
        if (N < d + 1) continue;
        if (!frob_group(N, &G, 1)) continue;
        fill_group(N, &G);
        try_order(best, N, SWEEP_ATTEMPTS, BC_STEPS, until);
    }
}

/* Phase 2: random orders just above the half-order, mixing Frobenius and random semidirect groups. */
static void random_bicayley(Graph *best, double until) {
    static Grp G;
    int Nmax = bc_nmax();
    while (now() < until) {
        int lo = best->n / 2 + 1;
        if (lo < d + 1) lo = d + 1;
        if (lo > Nmax) return;
        int span = Nmax - lo + 1;
        if (span > 60) span = 60;
        double u = rnd01();
        int N = lo + (int)(u * u * span);
        if (N > Nmax) N = Nmax;
        int ok = 0;
        if (rnd01() < 0.5) ok = frob_group(N, &G, 1);
        if (!ok) ok = random_group(N, &G);
        if (!ok) continue;
        fill_group(N, &G);
        try_order(best, N, BC_ATTEMPTS, BC_STEPS, until);
    }
}

/* ---------------- pair growth ---------------- */

/* Random wiring of one new vertex pair x (side 0), y (side 1) onto best. */
static void wire_random(const Graph *best, Graph *work) {
    static int used[MAXN];
    static int stamp = 0;
    int n = best->n;
    copy_graph(work, best);
    int x = n, y = n + 1;
    work->n = n + 2;
    work->deg[x] = work->deg[y] = 0;
    work->side[x] = 0;
    work->side[y] = 1;
    add_edge(work, x, y);
    stamp++;
    used[x] = used[y] = stamp;
    int k = 0;
    for (int tries = 0; k < d - 1 && tries < 200000; tries++) {
        int a = rndint(n);
        if (work->side[a] != 0 || used[a] == stamp || work->deg[a] == 0) continue;
        int b = work->adj[a][rndint(work->deg[a])];
        if (b >= n || used[b] == stamp) continue;
        del_edge(work, a, b);
        add_edge(work, x, b);
        add_edge(work, y, a);
        used[a] = used[b] = stamp;
        k++;
    }
}

static int grow_once(const Graph *best, Graph *work, double until) {
    int n = best->n;
    if (n + 2 > moore_bound() || n + 2 > MAXN) return 0;
    static Graph trial;
    long bestbad = -1;
    for (int t = 0; t < INIT_TRIALS; t++) {
        wire_random(best, &trial);
        long b = bad_pairs(&trial);
        if (bestbad < 0 || b < bestbad) {
            bestbad = b;
            copy_graph(work, &trial);
        }
        if (bestbad == 0 || now() > until) break;
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
    t_end = t0 + limit * 0.95;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best;
    if (d < 1 || D < 1 || d > MAXD) { complete_bipartite(&best); print_graph(&best); return 0; }
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (!is_valid(&best)) complete_bipartite(&best);

    double L = t_end - t0;
    if (d >= 3 && D >= 2 && best.n < moore_bound()) {
        frob_sweep(&best, t0 + L * 0.45);
        random_bicayley(&best, t0 + L * 0.65);
        if (best.n < moore_bound()) grow_search(&best, t_end);
    }
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


def _hexagon_incidence(q):
    """Incidence graph of the split Cayley hexagon H(q), q = 2 or 4.

    Order 2(q^6-1)/(q-1), degree q+1, bipartite, diameter 6, so it is valid for D = 6 and D = 7.
    Points: points of the quadric X0X4 + X1X5 + X2X6 = X3^2. Lines: quadric lines whose Grassmann
    coordinates satisfy p12=p34, p54=p32, p20=p35, p65=p30, p01=p36, p46=p31.
    Characteristic 2, so signs are irrelevant. The caller validates the result with lib.is_valid.
    """
    F = lib.GF(q)
    MT, AT = F.mul_table, F.add_table
    pts = []
    for v in itertools.product(range(q), repeat=7):
        if any(v) and next(c for c in v if c) == 1:
            s = AT[AT[MT[v[0], v[4]], MT[v[1], v[5]]], AT[MT[v[2], v[6]], MT[v[3], v[3]]]]
            if s == 0:
                pts.append(tuple(int(c) for c in v))
    N = len(pts)
    index = {v: i for i, v in enumerate(pts)}
    P = np.array(pts, dtype=np.int64)
    lines = set()
    for i in range(N - 1):
        x = P[i]
        Y = P[i + 1:]

        def pp(a, b):
            """Grassmann coordinate p_ab = x_a y_b - x_b y_a, for all y in Y."""
            return AT[MT[x[a], Y[:, b]], MT[x[b], Y[:, a]]]

        # Collinearity on the quadric: polar form B(x, y) = 0 (char 2 has no 2*x3*y3 term).
        s = np.zeros(len(Y), dtype=np.int64)
        for a, b in ((0, 4), (1, 5), (2, 6)):
            s = AT[s, AT[MT[x[a], Y[:, b]], MT[Y[:, a], x[b]]]]
        ok = (s == 0)
        ok &= pp(1, 2) == pp(3, 4)
        ok &= pp(5, 4) == pp(3, 2)
        ok &= pp(2, 0) == pp(3, 5)
        ok &= pp(6, 5) == pp(3, 0)
        ok &= pp(0, 1) == pp(3, 6)
        ok &= pp(4, 6) == pp(3, 1)
        for jj in np.nonzero(ok)[0]:
            y = Y[jj]
            # Points of the line: x, and t*x + y for t in GF(q).
            vecs = [tuple(int(c) for c in x)]
            for t in range(q):
                vecs.append(tuple(int(AT[MT[t, x[k]], y[k]]) for k in range(7)))
            idx = []
            for v in vecs:
                c = next(e for e in v if e)
                inv = F.inv(c)
                idx.append(index[tuple(F.mul(inv, e) for e in v)])
            lines.add(tuple(sorted(idx)))
    lines = sorted(lines)
    edges = [(pt, N + k) for k, L in enumerate(lines) for pt in L]
    return 2 * N, edges


def known_starts(d, D):
    """Algebraic candidates (may be empty); build() keeps only those that pass lib.is_valid."""
    out = []
    if D >= 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        out.append(lib.projective_plane_incidence(d - 1))
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        out.append(lib.araujo_lopez_graph(d - 2))
    if D >= 6 and d - 1 in (2, 4):
        try:
            out.append(_hexagon_incidence(d - 1))
        except Exception:
            pass
    return out


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D
        return L, [(i, (i + 1) % L) for i in range(L)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}: always valid for D >= 2
    for cand in known_starts(d, D):
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 31 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.9 * time_limit - (time.monotonic() - t0) - 1.0
    if budget <= 0.2:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, budget],
                         stdin_graph=best, timeout=budget + 6)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
