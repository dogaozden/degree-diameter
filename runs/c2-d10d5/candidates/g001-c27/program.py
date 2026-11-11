"""Starter program v2: Python builds the best known start graph, the C engine searches from it.

New in C: a fast exact diameter test for bi-Cayley voltage lifts over semidirect products.
The group acts on the lift by left multiplication, so the eccentricity of A(i,x) equals that
of A(i,0), and that of B(j,y) equals that of B(j,0). The diameter check therefore needs only
2P depth-limited BFS runs over the lift instead of full bitset closure. Voltages are
hill-climbed to minimise unreached pairs, and the order grows adaptively past the best graph.
"""
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
#define MAXW (MAXN / 64)
#define MAXP 4
#define MAXG 2048

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static double t_end;

/* ------------------------------------------------------------ utilities */

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

/* ------------------------------------------------------------ graph basics */

static void add_edge(Graph *g, int u, int v) {
    g->adj[u][g->deg[u]++] = v;
    g->adj[v][g->deg[v]++] = u;
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
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN || m < 0) return;
    g->n = n;
    for (int v = 0; v < n; v++) { g->deg[v] = 0; g->side[v] = 255; }
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= n || v >= n ||
            u == v || g->deg[u] >= MAXD || g->deg[v] >= MAXD) { g->n = 0; return; }
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

/* ------------------------------------------------------------ groups */

/* Z_m x|_r Z_k: element (a,b) = a*k+b; (a,b)(c,e) = (a + r^b c mod m, b+e mod k). */
typedef struct { int m, k, r; int rp[MAXG]; } Grp;
static Grp G;
static int NN, P;
static unsigned short MT[MAXG * MAXG]; /* multiplication table */
static int GI[MAXG];                   /* inverses */

static int gmul_f(int x, int y) {
    int k = G.k, m = G.m;
    int a = x / k, b = x % k, c = y / k, e = y % k;
    return (int)((a + (long)G.rp[b] * c) % m) * k + (b + e) % k;
}

/* Inverse of (a,b) is (-r^{-b} a, -b) = (-r^{nb} a, nb), nb = (k - b) mod k. */
static int ginv_f(int x) {
    int k = G.k, m = G.m;
    int a = x / k, b = x % k;
    int nb = (k - b) % k;
    int c = (int)((m - ((long)G.rp[nb] * a) % m) % m);
    return c * k + nb;
}

static void build_group_tables(int N) {
    for (int x = 0; x < N; x++) {
        for (int y = 0; y < N; y++) MT[x * N + y] = (unsigned short)gmul_f(x, y);
        GI[x] = ginv_f(x);
    }
}

/* Uniform random (m, k, r) with m*k = N, gcd(r,m) = 1, r^k = 1 mod m. */
static int random_group(int N) {
    long count = 0;
    int bm = 1, bk = N, br = 1;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        int rmax = m > 1 ? m : 2;
        for (int r = 1; r < rmax; r++) {
            if (m > 1 && gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            count++;
            if (rndint((int)count) == 0) { bm = m; bk = k; br = r; }
        }
    }
    if (!count) return 0;
    G.m = bm; G.k = bk; G.r = br;
    G.rp[0] = 1 % bm;
    for (int b = 1; b < bk; b++) G.rp[b] = (int)((long)G.rp[b - 1] * br % bm);
    return 1;
}

/* ------------------------------------------------------------ base graph and darts */

typedef struct { int i, j, g, gi; } Dart; /* A-vertex i -> B-vertex j with voltage g */
static Dart dt[MAXP * MAXD];
static int nd;
static int fromi[MAXP][MAXD], intoj[MAXP][MAXD];
static int nbr[MAXN][MAXD];

/* Random d-regular bipartite base multigraph on P+P vertices (sum of d permutations),
 * connected. M[i][j] = number of darts from A_i to B_j. */
static void make_base(int p, int M[MAXP][MAXP]) {
    for (;;) {
        memset(M, 0, sizeof(int) * MAXP * MAXP);
        for (int t = 0; t < d; t++) {
            int perm[MAXP];
            for (int i = 0; i < p; i++) perm[i] = i;
            for (int i = p - 1; i > 0; i--) {
                int j = rndint(i + 1), s = perm[i];
                perm[i] = perm[j];
                perm[j] = s;
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
        if (nseen == 2 * p) return;
    }
}

/* Voltage not used by another dart (index < cnt, not skip) between the same base pair. */
static int fresh_voltage(int skip, int cnt, int i, int j) {
    for (;;) {
        int g = rndint(NN), clash = 0;
        for (int t = 0; t < cnt; t++)
            if (t != skip && dt[t].i == i && dt[t].j == j && dt[t].g == g) { clash = 1; break; }
        if (!clash) return g;
    }
}

static void make_darts(void) {
    int M[MAXP][MAXP];
    make_base(P, M);
    nd = 0;
    for (int i = 0; i < P; i++)
        for (int j = 0; j < P; j++)
            for (int c = 0; c < M[i][j]; c++) {
                dt[nd].i = i;
                dt[nd].j = j;
                dt[nd].g = fresh_voltage(-1, nd, i, j);
                dt[nd].gi = GI[dt[nd].g];
                nd++;
            }
    int ci[MAXP] = {0}, cj[MAXP] = {0};
    for (int t = 0; t < nd; t++) {
        fromi[dt[t].i][ci[dt[t].i]++] = t;
        intoj[dt[t].j][cj[dt[t].j]++] = t;
    }
}

/* Neighbour table of the lift. A(i,x) = i*N+x, B(j,y) = P*N + j*N + y. */
static void build_nbr(void) {
    int N = NN, p = P;
    for (int i = 0; i < p; i++)
        for (int x = 0; x < N; x++) {
            int *row = nbr[i * N + x];
            for (int k = 0; k < d; k++) {
                const Dart *q = &dt[fromi[i][k]];
                row[k] = p * N + q->j * N + MT[x * N + q->g];
            }
        }
    for (int j = 0; j < p; j++)
        for (int y = 0; y < N; y++) {
            int *row = nbr[p * N + j * N + y];
            for (int k = 0; k < d; k++) {
                const Dart *q = &dt[intoj[j][k]];
                row[k] = q->i * N + MT[y * N + q->gi];
            }
        }
}

/* ------------------------------------------------------------ orbit-based diameter test */

static int vis[MAXN], vst = 0, qb[MAXN];

/* Number of vertices within distance D of src. */
static int reach_count(int src) {
    vst++;
    int head = 0, tail = 0;
    vis[src] = vst;
    qb[tail++] = src;
    for (int depth = 0; depth < D && head < tail; depth++) {
        int end = tail;
        while (head < end) {
            const int *row = nbr[qb[head++]];
            for (int k = 0; k < d; k++) {
                int u = row[k];
                if (vis[u] != vst) { vis[u] = vst; qb[tail++] = u; }
            }
        }
    }
    return tail;
}

/* Total number of (source, vertex) pairs missed within distance D, over the 2P sources.
 * Zero exactly when diameter <= D. */
static long lift_cost(void) {
    build_nbr();
    long V = 2L * P * NN, cost = 0;
    for (int i = 0; i < P; i++) cost += V - reach_count(i * NN);
    for (int j = 0; j < P; j++) cost += V - reach_count(P * NN + j * NN);
    return cost;
}

static void lift_to_graph(Graph *g) {
    int N = NN, p = P;
    g->n = 2 * p * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= p * N; }
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, dt[t].i * N + x, p * N + dt[t].j * N + MT[x * N + dt[t].g]);
}

/* One hill-climb over the voltages of a random base and random group of order N. */
static int attempt(int p, int N, double until, Graph *out) {
    if (N > MAXG || N < d) return 0;
    if (!random_group(N)) return 0;
    P = p;
    NN = N;
    build_group_tables(N);
    make_darts();
    long cur = lift_cost();
    long it = 0;
    while (cur > 0) {
        if ((++it & 7) == 0 && now() > until) return 0;
        int t = rndint(nd);
        int old = dt[t].g, oldgi = dt[t].gi;
        int g = fresh_voltage(t, nd, dt[t].i, dt[t].j);
        dt[t].g = g;
        dt[t].gi = GI[g];
        long nc = lift_cost();
        if (nc <= cur || rnd01() < 0.02) cur = nc;
        else { dt[t].g = old; dt[t].gi = oldgi; }
    }
    lift_to_graph(out);
    return 1;
}

/* Adaptive growth: aim for best->n + step vertices, using a random p and random group. */
static void search(Graph *best, double until) {
    static Graph cand;
    long cap = MAXN;
    long mb = moore_bound();
    if (mb < cap) cap = mb;
    long step = 2;
    int fails = 0;
    while (now() < until) {
        long T = (long)best->n + step;
        if (T > cap) {
            if ((long)best->n + 2 > cap) break;
            step = 2;
            T = (long)best->n + 2;
        }
        int r = rndint(10);
        int p = r < 5 ? 1 : (r < 8 ? 2 : 3);
        long N = (T + 2L * p - 1) / (2L * p);
        if (N < d) N = d;
        if (2L * p * N > cap) {
            p = 1;
            N = (T + 1) / 2;
            if (N < d) N = d;
            if (2L * N > cap) { step = 2; continue; }
        }
        double slice = until - now();
        double att = slice * 0.2;
        if (att < 0.5) att = 0.5;
        if (att > 6.0) att = 6.0;
        if (att > slice) att = slice;
        if (attempt(p, (int)N, now() + att, &cand) && cand.n > best->n && is_valid(&cand)) {
            copy_graph(best, &cand);
            step *= 2;
            if (step > best->n / 8 + 2) step = best->n / 8 + 2;
            fails = 0;
        } else if (++fails >= 2) {
            fails = 0;
            step /= 2;
            if (step < 2) step = 2;
        }
    }
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
    t_end = t0 + limit * 0.92;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best;
    if (d < 1 || d > MAXD) {
        best.n = 1;
        best.deg[0] = 0;
        best.side[0] = 0;
        print_graph(&best);
        return 0;
    }
    if (D < 2) {
        memset(&best, 0, sizeof(best));
        if (D == 1) {
            best.n = 2;
            best.side[1] = 1;
            add_edge(&best, 0, 1);
        } else {
            best.n = 1;
        }
    } else {
        read_start(&best);
        if (best.n == 0) complete_bipartite(&best);
        if (!is_valid(&best)) complete_bipartite(&best);
        if (d >= 2 && best.n < moore_bound()) search(&best, t_end);
    }
    if (!is_valid(&best) && D >= 2) complete_bipartite(&best);
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


def fallback(d, D):
    """A graph that is always valid for these parameters."""
    if D == 0 or d == 0:
        return (1, [])
    if D == 1:
        return (2, [(0, 1)])
    return lib.haar_graph(d, range(d))   # K_{d,d}


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    start = known_start(d, D)
    if start is None or not lib.is_valid(*start, d, D):
        start = fallback(d, D)
    best = start
    if not lib.is_valid(*best, d, D):
        best = (1, [])

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if best[0] >= lib.moore_bound(d, D):
        budget = min(budget, 0.5)   # nothing beats a Moore graph
    if budget > 0.5:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             stdin_graph=best, timeout=budget + 5)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(*out, d, D):
                best = out
        except (RuntimeError, ValueError):
            pass   # keep the valid fallback
    return best
