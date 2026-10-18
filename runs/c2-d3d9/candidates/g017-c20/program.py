"""Starter program: Python builds the best known start graph, the C engine searches from it.

Most improvements belong in C_SOURCE (it runs 10-100x faster than Python).
build() keeps the best valid graph it has, so a broken idea in C can only cost time.
"""
import time

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search core, lift-based version.
 *
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v": a known-valid starting graph, or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * Search:
 *   1. Voltage lifts over metacyclic groups Z_m x|_r Z_k of order N with a random
 *      base multigraph on p+p vertices (p = 1..6). Each base vertex has degree d.
 *      The lift has 2pN vertices. Left multiplication by G is an automorphism that
 *      is transitive on each fibre, so the diameter is decided by BFS from the 2p
 *      fibre representatives only. The cost is the number of (representative, vertex)
 *      pairs at distance > D. It is zero exactly when the lift has diameter <= D.
 *      Simulated annealing on the voltages drives the cost to zero.
 *   2. Grow by two: insert one vertex per side and anneal edge swaps until valid.
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
#define MAXP 6
#define MAXG 1024

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN]; /* 0 = part A, 1 = part B */
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

/* Number of unordered pairs at distance > D (0 means diameter <= D and connected). */
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

/* Full validity check: simple, bipartite (by side labels), degree <= d, diameter <= D. */
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

/* K_{d,d}: always valid for D >= 2. */
static void complete_bipartite(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= d; }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

/* ------------------------------------------------------------------ groups */

/* Group Z_m x|_r Z_k of order N = m*k: element (a,b) is a*k+b,
 * (a,b)(c,e) = (a + r^b c mod m, b + e mod k). Tables are kept in MUL / INV. */
static int MUL[MAXG * MAXG];
static int INV[MAXG];
static int G_N;

static void set_group(int m, int k, int r) {
    int N = m * k;
    int rp[MAXG];
    for (int b = 0; b < k; b++) rp[b] = (int)powmod(r, b, m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            MUL[x * N + y] = (int)(((long)a + (long)rp[b] * c) % m) * k + (b + e) % k;
        }
    }
    for (int x = 0; x < N; x++) {
        INV[x] = 0;
        for (int y = 0; y < N; y++)
            if (MUL[x * N + y] == 0) { INV[x] = y; break; }
    }
    G_N = N;
}

/* Uniformly random (m, k, r) with m*k = N, gcd(r,m)=1, r^k = 1 mod m. Returns 0 if none. */
static int pick_group(int N, int *om, int *ok, int *orr) {
    long count = 0;
    int bm = 1, bk = N, br = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        if (m == 1) {
            count++;
            if (rndint((int)count) == 0) { bm = 1; bk = k; br = 0; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1 || powmod(r, k, m) != 1 % m) continue;
            count++;
            if (rndint((int)count) == 0) { bm = m; bk = k; br = r; }
        }
    }
    if (!count) return 0;
    *om = bm;
    *ok = bk;
    *orr = br;
    return 1;
}

/* ------------------------------------------------------------------ voltage lifts */

typedef struct { int i, j, g; } Dart; /* base A-vertex i -> base B-vertex j, voltage g */

static int P_, N_, ND_;
static Dart DT[MAXP * MAXD];
static int NB[MAXN][MAXD];
static int NBC[MAXN];
static int QU[MAXN], DIST[MAXN];

/* Random d-regular base multigraph on p+p vertices: sum of d random permutation matrices.
 * Retried for connectivity a bounded number of times. M[i][j] = darts i -> j. */
static void make_base(int p, int M[MAXP][MAXP]) {
    for (int attempt = 0; ; attempt++) {
        memset(M, 0, sizeof(int) * MAXP * MAXP);
        for (int t = 0; t < d; t++) {
            int perm[MAXP];
            for (int i = 0; i < p; i++) perm[i] = i;
            for (int i = p - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int s = perm[i]; perm[i] = perm[j]; perm[j] = s;
            }
            for (int i = 0; i < p; i++) M[i][perm[i]]++;
        }
        int seen[2 * MAXP] = {0}, stack[2 * MAXP], top = 0, nseen = 1;
        seen[0] = 1;
        stack[top++] = 0;
        while (top) {
            int v = stack[--top];
            for (int u = 0; u < 2 * p; u++) {
                if (seen[u]) continue;
                int linked = v < p ? (u >= p && M[v][u - p]) : (u < p && M[u][v - p]);
                if (linked) { seen[u] = 1; nseen++; stack[top++] = u; }
            }
        }
        if (nseen == 2 * p || attempt > 200) return;
    }
}

/* A voltage not equal to any of the first nd darts with the same base pair (skipping index skip). */
static int fresh_g(int nd, int skip, int i, int j) {
    for (int tries = 0;; tries++) {
        int g = rndint(N_), clash = 0;
        for (int t = 0; t < nd; t++)
            if (t != skip && DT[t].i == i && DT[t].j == j && DT[t].g == g) { clash = 1; break; }
        if (!clash || tries > 100000) return g;
    }
}

/* Random base with voltages for the current P_, N_, group. */
static void fill_darts(int p) {
    int M[MAXP][MAXP];
    make_base(p, M);
    ND_ = 0;
    for (int i = 0; i < p; i++)
        for (int j = 0; j < p; j++)
            for (int c = 0; c < M[i][j]; c++) {
                DT[ND_].i = i;
                DT[ND_].j = j;
                DT[ND_].g = fresh_g(ND_, -1, i, j);
                ND_++;
            }
}

/* Neighbour lists of the lift. A fibre vertex i*N+x (A side) joins j-fibre vertex
 * p*N + j*N + x*g for each dart (i,j,g). A vertex p*N+j*N+y (B side) joins i*N + y*g^{-1}. */
static void build_nb(void) {
    int p = P_, N = N_;
    for (int i = 0; i < p; i++)
        for (int x = 0; x < N; x++) {
            int v = i * N + x, c = 0;
            for (int t = 0; t < ND_; t++)
                if (DT[t].i == i) NB[v][c++] = p * N + DT[t].j * N + MUL[x * N + DT[t].g];
            NBC[v] = c;
        }
    for (int j = 0; j < p; j++)
        for (int y = 0; y < N; y++) {
            int v = p * N + j * N + y, c = 0;
            for (int t = 0; t < ND_; t++)
                if (DT[t].j == j) NB[v][c++] = DT[t].i * N + MUL[y * N + INV[DT[t].g]];
            NBC[v] = c;
        }
}

/* Number of (fibre representative, vertex) pairs at distance > D. Zero iff the lift is valid. */
static long lift_cost(void) {
    build_nb();
    int V = 2 * P_ * N_;
    long far = 0;
    for (int s = 0; s < 2 * P_; s++) {
        int src = s < P_ ? s * N_ : P_ * N_ + (s - P_) * N_;
        for (int v = 0; v < V; v++) DIST[v] = -1;
        int head = 0, tail = 0;
        DIST[src] = 0;
        QU[tail++] = src;
        while (head < tail) {
            int v = QU[head++];
            if (DIST[v] >= D) continue;
            for (int k = 0; k < NBC[v]; k++) {
                int u = NB[v][k];
                if (DIST[u] < 0) { DIST[u] = DIST[v] + 1; QU[tail++] = u; }
            }
        }
        far += V - tail;
    }
    return far;
}

/* Simulated annealing over the voltages. Returns 0 if the cost reached zero. */
static long anneal(long steps, double T0) {
    long cur = lift_cost();
    double T = T0;
    for (long s = 0; s < steps && cur > 0; s++) {
        if ((s & 127) == 0 && now() > t_end) break;
        int t = rndint(ND_);
        int old = DT[t].g;
        DT[t].g = fresh_g(ND_, t, DT[t].i, DT[t].j);
        long c = lift_cost();
        if (c <= cur || rnd01() < exp(-(double)(c - cur) / T)) cur = c;
        else DT[t].g = old;
        T *= 0.9999;
        if (T < 0.2) T = 0.2;
    }
    return cur;
}

static void graph_from_lift(Graph *g) {
    int p = P_, N = N_;
    g->n = 2 * p * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= p * N; }
    build_nb();
    for (int v = 0; v < p * N; v++)
        for (int k = 0; k < NBC[v]; k++) add_edge(g, v, NB[v][k]);
}

static void lift_search(Graph *best, double until) {
    static Graph cand;
    long moore = moore_bound();
    if (d < 2) return;
    int fails = 0;
    while (now() < until) {
        if ((long)best->n + 2 > moore) return;
        int p = 1 + rndint(MAXP);
        long bump = best->n < 300 ? best->n / 6 : 2;
        long target = best->n + 2 + (rndint(2) ? bump : 0);
        long Nl = (target + 2 * p - 1) / (2 * p);
        int N = (int)Nl + (rndint(3) == 0 ? 1 : 0);
        if (N < d + 1) N = d + 1;
        if (2L * p * N > moore || 2L * p * N > MAXN || N > MAXG) {
            if (++fails > 100000) return;
            continue;
        }
        fails = 0;
        int m, k, r;
        if (!pick_group(N, &m, &k, &r)) continue;
        set_group(m, k, r);
        P_ = p;
        N_ = N;
        fill_darts(p);
        long c = anneal(30000, 2.0);
        if (c == 0) {
            graph_from_lift(&cand);
            if (cand.n > best->n && is_valid(&cand)) copy_graph(best, &cand);
        }
    }
}

/* ------------------------------------------------------------------ grow by two */

/* Insert one new vertex per side into a copy of best (degree d each), then anneal edge swaps.
 * Returns 1 if the work graph ends valid with best->n + 2 vertices. */
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

    static Graph best;
    if (d < 1 || D < 1 || d > MAXD) { complete_bipartite(&best); print_graph(&best); return 0; }
    read_start(&best);

    if (D >= 2 && best.n < moore_bound()) {
        lift_search(&best, t0 + (t_end - t0) * 0.85);
        if (best.n > 0) grow_search(&best, t_end);
    }
    if (best.n == 0) complete_bipartite(&best);
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


def known_start(d, D):
    """Best graph Python can build directly for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)           # record graphs of order 2(q^2+q+5)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    start = known_start(d, D)
    best = start if start is not None else lib.haar_graph(d, range(d))   # K_{d,d}: always valid
    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if best[0] >= lib.moore_bound(d, D):
        budget = min(budget, 0.5)   # nothing beats a Moore graph; just exercise the C engine
    if budget > 0.2:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, budget], stdin_graph=best, timeout=budget + 5)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except (RuntimeError, ValueError):
            pass   # keep the valid fallback
    return best
