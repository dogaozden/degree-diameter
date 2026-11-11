"""Orbit-lift annealing search for bipartite degree-diameter graphs.

Bold change in this version: the C engine no longer grows the graph one pair of vertices
at a time. It builds Z_N-lifts of random d-regular base multigraphs over metacyclic groups
Z_m x|_r Z_k with 2p base vertices (p per side). Left multiplication is an automorphism
transitive on each side's fibre, so the diameter test needs only 2p BFS runs, one from
each base representative. Simulated annealing then moves base endpoints and voltages to
drive the number of unreached (representative, vertex) pairs to zero. Any accepted lift
is re-checked in full before it is kept. A valid fallback (Python-known graph or K_{s,s})
is always returned.
"""
import time

import lib

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXV 2048
#define MAXDEG 16
#define MAXP 6
#define MAXND (MAXDEG * MAXP)
#define MAXG 1100
#define CONF_PEN 64

typedef struct {
    int n;
    int deg[MAXV];
    int adj[MAXV][MAXDEG];
    unsigned char side[MAXV];
} Graph;

typedef struct { int ai, bj, g; } Dart;

static int d, D;
static double t_end;
static Graph best;

/* ------------------------------------------------------------ utilities */

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

/* Full check: simple, bipartite by side labels, degree <= d, every BFS reaches all within D. */
static int is_valid(const Graph *g) {
    int n = g->n;
    if (n <= 0 || n > MAXV) return 0;
    for (int v = 0; v < n; v++) {
        if (g->deg[v] > d) return 0;
        for (int i = 0; i < g->deg[v]; i++) {
            int u = g->adj[v][i];
            if (u < 0 || u >= n || u == v || g->side[u] == g->side[v]) return 0;
            for (int j = 0; j < i; j++)
                if (g->adj[v][j] == u) return 0;
        }
    }
    static int dist[MAXV], q[MAXV];
    for (int s = 0; s < n; s++) {
        for (int v = 0; v < n; v++) dist[v] = -1;
        int h = 0, t = 0;
        dist[s] = 0;
        q[t++] = s;
        while (h < t) {
            int v = q[h++];
            if (dist[v] >= D) continue;
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[v][i];
                if (dist[u] < 0) { dist[u] = dist[v] + 1; q[t++] = u; }
            }
        }
        if (t != n) return 0;
    }
    return 1;
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

static void fallback(Graph *g) {
    memset(g, 0, sizeof(*g));
    if (D == 1 || d == 1) {
        g->n = 2;
        g->side[0] = 0;
        g->side[1] = 1;
        add_edge(g, 0, 1);
        return;
    }
    int s = d < MAXDEG ? d : MAXDEG;
    g->n = 2 * s;
    for (int v = 0; v < g->n; v++) g->side[v] = v >= s;
    for (int a = 0; a < s; a++)
        for (int b = 0; b < s; b++) add_edge(g, a, s + b);
}

static void read_start(void) {
    static Graph g;
    int n, m;
    best.n = 0;
    if (scanf("%d %d", &n, &m) != 2) return;
    if (n <= 0 || n > MAXV || m < 0) return;
    memset(&g, 0, sizeof(g));
    g.n = n;
    for (int v = 0; v < n; v++) g.side[v] = 255;
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v ||
            g.deg[u] >= MAXDEG || g.deg[v] >= MAXDEG) return;
        add_edge(&g, u, v);
    }
    static int q[MAXV];
    for (int s = 0; s < n; s++) {
        if (g.side[s] != 255) continue;
        int h = 0, t = 0;
        g.side[s] = 0;
        q[t++] = s;
        while (h < t) {
            int v = q[h++];
            for (int i = 0; i < g.deg[v]; i++) {
                int u = g.adj[v][i];
                if (g.side[u] == 255) { g.side[u] = 1 - g.side[v]; q[t++] = u; }
                else if (g.side[u] == g.side[v]) return;
            }
        }
    }
    if (is_valid(&g)) best = g;
}

/* ------------------------------------------------------------ groups */

/* Z_m x|_r Z_k, element (a,b) = a*k+b, (a,b)(c,e) = (a + r^b c, b + e). */
static int gtab[MAXG * MAXG];
static int GN;

static void build_group(int m, int k, int r) {
    int N = m * k;
    static int rp[MAXG];
    GN = N;
    for (int b = 0; b < k; b++) rp[b] = (int)powmod(r, b, m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            gtab[x * N + y] = (int)(((a + (long)rp[b] * c) % m) * k + (b + e) % k);
        }
    }
}

/* Uniform random (m, k, r) with m*k = N, gcd(r,m) = 1, r^k = 1 mod m. */
static int random_group(int N, int *mo, int *ko, int *ro) {
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
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            count++;
            if (rndint((int)count) == 0) { bm = m; bk = k; br = r; }
        }
    }
    if (count == 0) return 0;
    *mo = bm;
    *ko = bk;
    *ro = br;
    return 1;
}

/* ------------------------------------------------------------ orbit lifts */

static Dart dart[MAXND], dbest[MAXND];
static int ND, NDbest;
static int P;
static int adjL[MAXV][MAXDEG];
static int degL[MAXV];

/* d random permutation layers: each A_i and each B_j gets exactly d darts. */
static void random_darts(void) {
    int p = P, N = GN, t = 0;
    for (int s = 0; s < d; s++) {
        int perm[MAXP];
        for (int i = 0; i < p; i++) perm[i] = i;
        for (int i = p - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int tmp = perm[i]; perm[i] = perm[j]; perm[j] = tmp;
        }
        for (int i = 0; i < p; i++) {
            dart[t].ai = i;
            dart[t].bj = perm[i];
            dart[t].g = rndint(N);
            t++;
        }
    }
    ND = t;
}

static void build_adj(void) {
    int p = P, N = GN, V = 2 * p * N;
    for (int v = 0; v < V; v++) degL[v] = 0;
    for (int t = 0; t < ND; t++) {
        int ai = dart[t].ai, bj = dart[t].bj, g = dart[t].g;
        for (int x = 0; x < N; x++) {
            int A = ai * N + x;
            int B = p * N + bj * N + gtab[x * N + g];
            adjL[A][degL[A]++] = B;
            adjL[B][degL[B]++] = A;
        }
    }
}

/* Number of vertices at distance > D from src in the current lift. */
static long bfs_unreached(int src, int V) {
    static int dist[MAXV], q[MAXV];
    for (int v = 0; v < V; v++) dist[v] = -1;
    int h = 0, t = 0;
    dist[src] = 0;
    q[t++] = src;
    while (h < t) {
        int v = q[h++];
        if (dist[v] >= D) continue;
        for (int i = 0; i < degL[v]; i++) {
            int u = adjL[v][i];
            if (dist[u] < 0) { dist[u] = dist[v] + 1; q[t++] = u; }
        }
    }
    return V - t;
}

/* Cost = unreached pairs from the 2p representatives + duplicate-dart penalty. Zero iff valid. */
static long eval_cost(void) {
    build_adj();
    int p = P, N = GN, V = 2 * p * N;
    long c = 0;
    for (int i = 0; i < p; i++) {
        c += bfs_unreached(i * N, V);
        c += bfs_unreached(p * N + i * N, V);
    }
    for (int a = 0; a < ND; a++)
        for (int b = a + 1; b < ND; b++)
            if (dart[a].ai == dart[b].ai && dart[a].bj == dart[b].bj && dart[a].g == dart[b].g)
                c += CONF_PEN;
    return c;
}

/* Simulated annealing over voltages and base endpoints. Leaves best state in dbest. */
static long anneal(long steps) {
    long cur = eval_cost();
    long bc = cur;
    memcpy(dbest, dart, sizeof(Dart) * ND);
    NDbest = ND;
    Dart save[MAXND];
    for (long s = 0; s < steps && bc > 0; s++) {
        if ((s & 127) == 0 && now() > t_end) break;
        double T = 2.0 * (1.0 - (double)s / (double)steps) + 0.05;
        memcpy(save, dart, sizeof(Dart) * ND);
        if (rnd01() < 0.5) {
            int t = rndint(ND);
            dart[t].g = rndint(GN);
        } else {
            int t1 = rndint(ND), t2 = rndint(ND);
            int tmp = dart[t1].bj;
            dart[t1].bj = dart[t2].bj;
            dart[t2].bj = tmp;
        }
        long nc = eval_cost();
        if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
            cur = nc;
            if (cur < bc) {
                bc = cur;
                memcpy(dbest, dart, sizeof(Dart) * ND);
                NDbest = ND;
            }
        } else {
            memcpy(dart, save, sizeof(Dart) * ND);
        }
    }
    return bc;
}

static void build_graph(Graph *g) {
    int p = P, N = GN;
    memset(g, 0, sizeof(*g));
    g->n = 2 * p * N;
    for (int v = 0; v < g->n; v++) g->side[v] = v >= p * N;
    for (int t = 0; t < ND; t++)
        for (int x = 0; x < N; x++) {
            int A = dart[t].ai * N + x;
            int B = p * N + dart[t].bj * N + gtab[x * N + dart[t].g];
            add_edge(g, A, B);
        }
}

static void lift_search(void) {
    static Graph cand;
    long moore = moore_bound();
    while (now() < t_end) {
        long target = best.n + 2;
        if (target > moore || target > MAXV) break;
        int p = 1 + rndint(MAXP);
        long N = (target + 2L * p - 1) / (2L * p) + rndint(3);
        if (N < 1 || N > 1024 || 2L * p * N > MAXV || 2L * p * N > moore) continue;
        int m, k, r;
        if (!random_group((int)N, &m, &k, &r)) continue;
        build_group(m, k, r);
        P = p;
        long V = 2L * p * N;
        long steps = 100000000L / (2L * p * V * d + 1);
        if (steps < 2000) steps = 2000;
        random_darts();
        long c = anneal(steps);
        if (c == 0) {
            memcpy(dart, dbest, sizeof(Dart) * NDbest);
            ND = NDbest;
            build_graph(&cand);
            if (cand.n > best.n && is_valid(&cand)) best = cand;
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
    t_end = t0 + limit * 0.9;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 1) {
        printf("1 0\n");
        return 0;
    }
    best.n = 0;
    read_start();
    if (d >= 2 && D >= 2 && d <= MAXDEG && best.n < moore_bound()) lift_search();
    if (best.n == 0 || !is_valid(&best)) fallback(&best);
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


def fallback_graph(d, D):
    """Always-valid graph: K_{s,s} with s = min(d, 16), or K_2 when D == 1 or d == 1."""
    if d < 1 or D < 1:
        return (1, [])
    if d == 1 or D == 1:
        return (2, [(0, 1)])
    s = min(d, 16)
    return (2 * s, [(a, s + b) for a in range(s) for b in range(s)])


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    fb = fallback_graph(d, D)
    start = known_start(d, D)
    if start is not None and not lib.is_valid(*start, d, D):
        start = None
    best = start if start is not None else fb
    if best[0] >= lib.moore_bound(d, D):
        return best   # already optimal; nothing to search for
    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.5
    if budget > 1.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             stdin_graph=start, timeout=budget + 5)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(*out, d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best
