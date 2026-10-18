"""Bi-Cayley search: bipartite graphs A = B = G with a_g ~ b_{g s} for s in S, |S| = d.

Left multiplication by G is an automorphism group acting transitively on each side, so
diameter <= D needs only two BFS runs (from a_e and from b_e). Each candidate costs O(N d).
The C engine anneals the connection set S over semidirect products Z_m x| Z_k, growing the
group order N as long as a valid graph is found. Python builds a safe start graph and validates
everything it gets back.
"""
import time

import lib

C_SOURCE = r'''
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXV 4096                /* max group order N; the graph has 2N vertices */
#define MAXVV (2 * MAXV)
#define MAXD 16
#define MAXG 40000

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

/* ---------------------------------------------------------------- groups Z_m x|_r Z_k */

static int GM, GK, GR, N;
static int rp[MAXV]; /* rp[b] = r^b mod m */

typedef struct { int m, k, r; } GroupP;
static GroupP glist[MAXG];
static int ng;

static void set_group(int m, int k, int r) {
    GM = m; GK = k; GR = r; N = m * k;
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
}

/* element (a,b) is a*k+b; (a,b)(c,e) = (a + r^b c, b + e) */
static inline int gmul(int x, int y) {
    int a = x / GK, b = x % GK, c = y / GK, e = y % GK;
    int s = (int)(((long)a + (long)rp[b] * c) % GM);
    int t = (b + e) % GK;
    return s * GK + t;
}

/* inverse of (a,b) is (-a r^{-b}, -b) */
static inline int ginv(int x) {
    int a = x / GK, b = x % GK;
    int nb = (GK - b) % GK;
    int c = (int)((GM - ((long)a * rp[nb]) % GM) % GM);
    return c * GK + nb;
}

static void enum_groups(int n) {
    ng = 0;
    for (int m = 1; m <= n; m++) {
        if (n % m) continue;
        int k = n / m;
        if (m == 1) {
            if (ng < MAXG) { glist[ng].m = 1; glist[ng].k = k; glist[ng].r = 0; ng++; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            if (ng < MAXG) { glist[ng].m = m; glist[ng].k = k; glist[ng].r = r; ng++; }
        }
    }
}

/* ---------------------------------------------------------------- bi-Cayley graph */

static int S[MAXD], invS[MAXD];
/* vertices: A-vertex g is g, B-vertex h is N + h. adj[v][i] = i-th neighbour. */
static int adj[MAXVV][MAXD];

static void set_row(int i) {
    for (int g = 0; g < N; g++) {
        adj[g][i] = N + gmul(g, S[i]);
        adj[N + g][i] = gmul(g, invS[i]);
    }
}

static int vis[MAXVV], vstamp = 0, Q[MAXVV];

/* Number of vertices within distance D of src. */
static int reach_count(int src) {
    vstamp++;
    int head = 0, tail = 0, level_end;
    Q[tail++] = src;
    vis[src] = vstamp;
    level_end = tail;
    for (int lvl = 0; lvl < D; lvl++) {
        if (head == tail) break;
        while (head < level_end) {
            int v = Q[head++];
            for (int i = 0; i < d; i++) {
                int u = adj[v][i];
                if (vis[u] != vstamp) {
                    vis[u] = vstamp;
                    Q[tail++] = u;
                }
            }
        }
        level_end = tail;
    }
    return tail;
}

/* Zero iff the graph has diameter <= D (by transitivity of left multiplication). */
static long cost(void) {
    int nv = 2 * N;
    return (long)(nv - reach_count(0)) + (long)(nv - reach_count(N));
}

static int verify(void) {
    int nv = 2 * N;
    for (int v = 0; v < nv; v++)
        if (reach_count(v) != nv) return 0;
    return 1;
}

static int in_S(int t, int upto) {
    for (int j = 0; j < upto; j++)
        if (S[j] == t) return 1;
    return 0;
}

/* Simulated annealing over the connection set S for the current group. */
static int anneal(int steps, double until) {
    if (N <= d) return 0;
    for (int i = 0; i < d; i++) {
        int t;
        do { t = rndint(N); } while (in_S(t, i));
        S[i] = t;
        invS[i] = ginv(t);
    }
    for (int i = 0; i < d; i++) set_row(i);
    long cur = cost();
    for (int s = 0; s < steps; s++) {
        if (cur == 0) return 1;
        if ((s & 255) == 0 && now() > until) return 0;
        int i = rndint(d), t;
        do { t = rndint(N); } while (in_S(t, d));
        int old = S[i], oldinv = invS[i];
        S[i] = t;
        invS[i] = ginv(t);
        set_row(i);
        long nc = cost();
        double T = 1.0 - 0.8 * (double)s / (double)steps;
        if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
            cur = nc;
        } else {
            S[i] = old;
            invS[i] = oldinv;
            set_row(i);
        }
    }
    return cur == 0;
}

/* ---------------------------------------------------------------- best so far */

static int bestN, bestM, bestK, bestR;
static int bestS[MAXD];

static void print_best(void) {
    set_group(bestM, bestK, bestR);
    for (int i = 0; i < d; i++) S[i] = bestS[i];
    for (int i = 0; i < d; i++) invS[i] = ginv(S[i]);
    long m = (long)N * d;
    printf("%d %ld\n", 2 * N, m);
    for (int g = 0; g < N; g++)
        for (int i = 0; i < d; i++)
            printf("%d %d\n", g, N + gmul(g, S[i]));
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit\n", argv[0]);
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
    for (int i = 0; i < 20; i++) rnd();

    /* default: K_{d,d} = bi-Cayley over Z_d with S = Z_d */
    bestN = d; bestM = 1; bestK = d; bestR = 0;
    if (d < 1 || d > MAXD) {
        printf("0 0\n");
        return 0;
    }
    for (int i = 0; i < d; i++) bestS[i] = i;

    if (d >= 3 && D >= 2) {
        int lo = d, step = 8;
        while (lo < MAXV && now() < t_end) {
            int Nt = lo + step;
            if (Nt > MAXV) Nt = MAXV;
            enum_groups(Nt);
            double rem = t_end - now();
            double cap = now() + (rem * 0.25 > 0.3 ? rem * 0.25 : 0.3);
            int ok = 0;
            while (!ok && now() < cap && ng > 0) {
                GroupP g = glist[rndint(ng)];
                set_group(g.m, g.k, g.r);
                ok = anneal(6000, cap);
                if (ok && !verify()) ok = 0;
                if (ok) {
                    lo = Nt;
                    bestN = N; bestM = GM; bestK = GK; bestR = GR;
                    for (int i = 0; i < d; i++) bestS[i] = S[i];
                }
            }
            if (ok) {
                if (step < 1024) step *= 2;
            } else if (step > 1) {
                step /= 2;
            }
        }
    }
    print_best();
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


def _fallback(d, D):
    """A simple graph that is valid whenever D >= 2: even cycle for d = 2, else K_{d,d}."""
    if d == 2 and D >= 2:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]
    return lib.haar_graph(d, range(d))


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    best = known_start(d, D)
    if best is None:
        best = _fallback(d, D)
    if not lib.is_valid(*best, d, D):
        best = (2, [(0, 1)])          # K2: valid for any d >= 1, D >= 1

    if best[0] >= lib.moore_bound(d, D) or d < 3 or D < 2:
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 2.0
    if budget < 1.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=None, timeout=budget + 5)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(*out, d, D):
            best = out
    except (RuntimeError, ValueError):
        pass
    return best
