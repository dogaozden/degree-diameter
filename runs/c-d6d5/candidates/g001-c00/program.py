"""Bi-Cayley (Haar-type) search for bipartite degree-diameter graphs.

Construction: pick a group G of order N (semidirect product Z_m x| Z_k) and a connection set
S of d distinct elements. The graph has vertices a_x and b_y (x, y in G), with a_x adjacent to
b_{xs} for s in S. It is bipartite and d-regular. Left multiplication is an automorphism, so the
diameter is at most D iff BFS from a_e and from b_e reaches every vertex within D steps.
The C engine hill-climbs S for the largest N it can reach. Each success is checked by a full
validator, and the start graph (or K_{d,d}) is kept as a fallback.
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

#define MAXN 4096
#define MAXD 32
#define MAXG 1024

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

/* ------------------------------------------------------------ group Z_m x| Z_k */

static int GM, GK, NG;
static int RP[MAXG];
static int MT[MAXG * MAXG];   /* MT[x*N + y] = x*y */
static int INV[MAXG];
static int S[MAXD], SI[MAXD]; /* connection set and its inverses */

/* element (a,b) is coded a*k+b; (a,b)(c,e) = (a + r^b c mod m, b+e mod k) */
static int gmul_raw(int x, int y) {
    int a = x / GK, b = x % GK, c = y / GK, e = y % GK;
    return (int)(((long)a + (long)RP[b] * c) % GM) * GK + (b + e) % GK;
}

static int setup_group(int N) {
    long count = 0;
    int bm = 0, bk = 0, br = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        int rmax = m > 1 ? m : 1;
        for (int r = 0; r < rmax; r++) {
            if (m > 1 && gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            count++;
            if (rndint((int)count) == 0) { bm = m; bk = k; br = r; }
        }
    }
    if (count == 0) return 0;
    GM = bm;
    GK = bk;
    NG = N;
    RP[0] = 1 % GM;
    for (int b = 1; b < GK; b++) RP[b] = (int)((long)RP[b - 1] * br % GM);
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            MT[x * N + y] = gmul_raw(x, y);
    for (int x = 0; x < N; x++) {
        int found = -1;
        for (int y = 0; y < N; y++)
            if (MT[x * N + y] == 0) { found = y; break; }
        if (found < 0) return 0;
        INV[x] = found;
    }
    return 1;
}

/* ------------------------------------------------------------ fast diameter test */

static int QB[2 * MAXG];
static int VIS[2 * MAXG];
static int vstamp = 0;

/* Number of vertices within distance D of src (src < NG is an A-node, else a B-node). */
static int reach(int src) {
    int N = NG;
    vstamp++;
    int head = 0, tail = 0;
    QB[tail++] = src;
    VIS[src] = vstamp;
    for (int depth = 0; depth < D && head < tail; depth++) {
        int end = tail;
        while (head < end) {
            int v = QB[head++];
            if (v < N) {
                const int *row = MT + v * N;
                for (int i = 0; i < d; i++) {
                    int u = N + row[S[i]];
                    if (VIS[u] != vstamp) { VIS[u] = vstamp; QB[tail++] = u; }
                }
            } else {
                const int *row = MT + (v - N) * N;
                for (int i = 0; i < d; i++) {
                    int u = row[SI[i]];
                    if (VIS[u] != vstamp) { VIS[u] = vstamp; QB[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Number of unreached (source, target) pairs from the two base vertices. 0 means valid. */
static long eval_bad(void) {
    long N2 = 2L * NG;
    return (N2 - reach(0)) + (N2 - reach(NG));
}

static int in_set(int x, int cnt) {
    for (int j = 0; j < cnt; j++)
        if (S[j] == x) return 1;
    return 0;
}

/* Simulated-annealing style search over S for the current group. Returns 1 on success. */
static int hill_climb(int steps) {
    int N = NG;
    for (int i = 0; i < d; i++) {
        int x;
        do { x = rndint(N); } while (in_set(x, i));
        S[i] = x;
        SI[i] = INV[x];
    }
    long cur = eval_bad();
    for (int s = 0; s < steps && cur > 0; s++) {
        if ((s & 255) == 0 && now() > t_end) return 0;
        int i = rndint(d);
        int old = S[i], oldI = SI[i];
        int x;
        do { x = rndint(N); } while (in_set(x, d));
        S[i] = x;
        SI[i] = INV[x];
        long nb = eval_bad();
        double T = 0.5 * (1.0 - (double)s / steps) + 0.02;
        if (nb <= cur || rnd01() < exp(-(double)(nb - cur) / T)) {
            cur = nb;
        } else {
            S[i] = old;
            SI[i] = oldI;
        }
    }
    return cur == 0;
}

/* ------------------------------------------------------------ graphs */

static void add_edge(Graph *g, int u, int v) {
    g->adj[u][g->deg[u]++] = v;
    g->adj[v][g->deg[v]++] = u;
}

static void haar_graph(Graph *g) {
    int N = NG;
    g->n = 2 * N;
    for (int v = 0; v < g->n; v++) {
        g->deg[v] = 0;
        g->side[v] = v >= N;
    }
    for (int x = 0; x < N; x++)
        for (int i = 0; i < d; i++)
            add_edge(g, x, N + MT[x * N + S[i]]);
}

static int vis_arr[MAXN];
static int vst = 0;
static int bq[MAXN];

/* Full validity: simple, bipartite via side labels, degree <= d, diameter <= D. */
static int full_valid(const Graph *g) {
    int n = g->n;
    if (n <= 0 || n > MAXN) return 0;
    for (int v = 0; v < n; v++) {
        if (g->deg[v] > d) return 0;
        for (int i = 0; i < g->deg[v]; i++) {
            int u = g->adj[v][i];
            if (u < 0 || u >= n || u == v || g->side[u] == g->side[v]) return 0;
            for (int j = 0; j < i; j++)
                if (g->adj[v][j] == u) return 0;
        }
    }
    for (int s = 0; s < n; s++) {
        vst++;
        int head = 0, tail = 0;
        bq[tail++] = s;
        vis_arr[s] = vst;
        for (int depth = 0; depth < D && head < tail; depth++) {
            int end = tail;
            while (head < end) {
                int v = bq[head++];
                for (int i = 0; i < g->deg[v]; i++) {
                    int u = g->adj[v][i];
                    if (vis_arr[u] != vst) { vis_arr[u] = vst; bq[tail++] = u; }
                }
            }
        }
        if (tail != n) return 0;
    }
    return 1;
}

static int read_start(Graph *g) {
    int n, m;
    if (scanf("%d %d", &n, &m) != 2) return 0;
    if (n <= 0 || n > MAXN || m < 0) return 0;
    g->n = n;
    for (int v = 0; v < n; v++) {
        g->deg[v] = 0;
        g->side[v] = 255;
    }
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return 0;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) return 0;
        if (g->deg[u] >= MAXD || g->deg[v] >= MAXD) return 0;
        add_edge(g, u, v);
    }
    static int q[MAXN];
    for (int s = 0; s < n; s++) {
        if (g->side[s] != 255) continue;
        int head = 0, tail = 0;
        g->side[s] = 0;
        q[tail++] = s;
        while (head < tail) {
            int v = q[head++];
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[v][i];
                if (g->side[u] == 255) {
                    g->side[u] = (unsigned char)(1 - g->side[v]);
                    q[tail++] = u;
                }
            }
        }
    }
    return full_valid(g);
}

static void complete_bip(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) {
        g->deg[v] = 0;
        g->side[v] = v >= d;
    }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++)
            add_edge(g, a, d + b);
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
    t_end = t0 + limit * 0.93 - 0.2;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best, cand;
    if (d < 1 || d > MAXD || D < 1) {
        printf("2 1\n0 1\n");
        return 0;
    }
    if (!read_start(&best)) complete_bip(&best);

    long moore = moore_bound();
    long half = moore / 2;
    int Nmax = MAXG;
    if (half < Nmax) Nmax = (int)half;
    int Nbest = best.n / 2;

    while (now() < t_end && Nbest < Nmax && Nmax >= d + 1) {
        int N = Nbest + 1 + rndint(1 + Nbest / 64);
        if (N > Nmax) N = Nmax;
        if (N <= d) N = d + 1;
        if (N > Nmax) break;
        if (!setup_group(N)) continue;
        if (hill_climb(6000)) {
            haar_graph(&cand);
            if (cand.n > best.n && full_valid(&cand)) {
                best = cand;
                Nbest = N;
            }
        }
    }
    if (!full_valid(&best)) complete_bip(&best);
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


def _complete(d):
    """K_{d,d}: valid for D >= 2."""
    return lib.haar_graph(d, range(d))


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if D < 2:
        return (2, [(0, 1)])
    start = known_start(d, D)
    best = start if start is not None else _complete(d)
    if best[0] >= lib.moore_bound(d, D):
        return best
    budget = 0.8 * time_limit - 2.0 - (time.monotonic() - t0)
    if budget < 1.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=start, timeout=budget + 8)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
