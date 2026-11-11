"""Voltage-lift simulated annealing over metacyclic groups, with a validity-checked fallback.

Python builds the best known start (projective plane or Araujo-Lopez graph when available,
otherwise K_{d,d}). The C engine ignores the start graph and searches its own bipartite
lifts: each candidate is a random group Z_m x|_r Z_k of order N, a random base multigraph
with P vertices per side, and random voltages. Simulated annealing (not greedy hill-climbing)
minimises the number of pairs at distance > D. Every accepted graph is checked in C, and
Python re-checks the output with lib.is_valid before returning the larger of the two graphs.
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

#define MAXV 1200
#define MAXW 19
#define MAXD 16
#define MAXP 4
#define MAXDART (MAXP * MAXD)
#define MAXE 12000

static int d, D;
static double t_end;
static long MOORE;

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

/* ---------------------------------------------------------- group Z_m x|_r Z_k */

static int G_m = 1, G_k = 1, G_r = 0;
static int G_rp[MAXV];

static void set_group(int m, int k, int r) {
    G_m = m;
    G_k = k;
    G_r = r;
    for (int b = 0; b < k; b++) G_rp[b] = (int)powmod(r, b, m);
}

/* (a,b)(c,e) = (a + r^b c, b + e), element coded as a*k + b. */
static int gmul(int x, int y) {
    int a = x / G_k, b = x % G_k, c = y / G_k, e = y % G_k;
    return (int)(((long)a + (long)G_rp[b] * c) % G_m) * G_k + (b + e) % G_k;
}

/* Uniform random (m, k, r) with m*k = N, gcd(r,m)=1, r^k = 1 mod m. */
static int random_group(int N) {
    long cnt = 0;
    int bm = -1, bk = -1, br = -1;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        if (m == 1) {
            cnt++;
            if (rndint((int)cnt) == 0) { bm = 1; bk = k; br = 0; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            cnt++;
            if (rndint((int)cnt) == 0) { bm = m; bk = k; br = r; }
        }
    }
    if (cnt == 0) return 0;
    set_group(bm, bk, br);
    return 1;
}

/* ---------------------------------------------------------- graph state */

static int nv;
static int deg[MAXV];
static int adj[MAXV][MAXD];
static uint64_t bufA[MAXV * MAXW], bufB[MAXV * MAXW];

static void add_nb(int a, int b) {
    adj[a][deg[a]++] = b;
    adj[b][deg[b]++] = a;
}

/* Number of unordered pairs at distance > D. */
static long bad_pairs(void) {
    int W = (nv + 63) / 64;
    uint64_t *cur = bufA, *nxt = bufB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)nv * W);
    for (int v = 0; v < nv; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < nv; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            const uint64_t *src = cur + (size_t)v * W;
            memcpy(dst, src, sizeof(uint64_t) * W);
            for (int i = 0; i < deg[v]; i++) {
                const uint64_t *s = cur + (size_t)adj[v][i] * W;
                for (int w = 0; w < W; w++) dst[w] |= s[w];
            }
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
    }
    long total = 0;
    for (int v = 0; v < nv; v++) {
        int c = 0;
        const uint64_t *s = cur + (size_t)v * W;
        for (int w = 0; w < W; w++) c += __builtin_popcountll(s[w]);
        total += nv - c;
    }
    return total / 2;
}

static int check_simple(void) {
    for (int v = 0; v < nv; v++)
        for (int i = 0; i < deg[v]; i++) {
            if (adj[v][i] == v) return 0;
            for (int j = 0; j < i; j++)
                if (adj[v][j] == adj[v][i]) return 0;
        }
    return 1;
}

/* ---------------------------------------------------------- voltage lifts */

typedef struct { int i, j, g; } Dart;
static Dart dt[MAXDART];
static int nd, P, NN;

/* Base: d random perfect matchings between P A-vertices and P B-vertices (so every
 * vertex on each side has exactly d darts). */
static void make_base_darts(void) {
    nd = 0;
    for (int t = 0; t < d; t++) {
        int perm[MAXP];
        for (int i = 0; i < P; i++) perm[i] = i;
        for (int i = P - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int s = perm[i];
            perm[i] = perm[j];
            perm[j] = s;
        }
        for (int i = 0; i < P; i++) {
            dt[nd].i = i;
            dt[nd].j = perm[i];
            dt[nd].g = -1;
            nd++;
        }
    }
}

/* A voltage not used by another dart between the same base pair. */
static int fresh_g(int t) {
    for (int tries = 0; tries < 10000; tries++) {
        int g = rndint(NN), clash = 0;
        for (int u = 0; u < nd; u++)
            if (u != t && dt[u].g >= 0 && dt[u].i == dt[t].i && dt[u].j == dt[t].j && dt[u].g == g) {
                clash = 1;
                break;
            }
        if (!clash) return g;
    }
    return -1;
}

static void build_lift(void) {
    nv = 2 * P * NN;
    for (int v = 0; v < nv; v++) deg[v] = 0;
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < NN; x++)
            add_nb(dt[t].i * NN + x, P * NN + dt[t].j * NN + gmul(x, dt[t].g));
}

/* Simulated annealing over voltages. Returns 0 when bad = 0 (graph left built),
 * the remaining bad count on timeout, or -1 if no initial voltages exist. */
static long sa_search(double until) {
    for (int t = 0; t < nd; t++) dt[t].g = -1;
    for (int t = 0; t < nd; t++) {
        int g = fresh_g(t);
        if (g < 0) return -1;
        dt[t].g = g;
    }
    build_lift();
    long bad = bad_pairs();
    for (long s = 0; bad > 0; s++) {
        if ((s & 7) == 0 && now() > until) return bad;
        int t = rndint(nd);
        int old = dt[t].g;
        int ng = fresh_g(t);
        if (ng < 0) continue;
        dt[t].g = ng;
        build_lift();
        long nb = bad_pairs();
        double T = 0.2 + 1.0 * (1.0 - (double)(s % 5000) / 5000.0);
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) {
            bad = nb;
        } else {
            dt[t].g = old;
            build_lift();
        }
    }
    return 0;
}

/* ---------------------------------------------------------- best graph */

static int bestn = 0, ne = 0;
static int eu[MAXE], ev[MAXE];

static void init_best(void) {
    bestn = 2 * d;
    ne = 0;
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) {
            eu[ne] = a;
            ev[ne] = d + b;
            ne++;
        }
}

static void store_best(void) {
    bestn = nv;
    ne = 0;
    for (int u = 0; u < nv; u++)
        for (int i = 0; i < deg[u]; i++)
            if (u < adj[u][i] && ne < MAXE) {
                eu[ne] = u;
                ev[ne] = adj[u][i];
                ne++;
            }
}

/* ---------------------------------------------------------- main */

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
    t_end = t0 + limit * 0.85;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXD || D < 1) {
        printf("0 0\n");
        return 0;
    }
    if (D < 2) {
        printf("2 1\n0 1\n");
        return 0;
    }

    MOORE = moore_bound();
    init_best();

    long fails = 0;
    while (now() < t_end) {
        int p = 1 + rndint(MAXP);
        long target = (long)bestn + 2;
        if (target > MOORE) break;
        long N = (target + 2L * p - 1) / (2L * p) + rndint(3);
        if (N <= d) N = d + 1;
        if (2L * p * N > MOORE || 2L * p * N > MAXV || N > MAXV) {
            if (++fails > 5000) break;
            continue;
        }
        if (!random_group((int)N)) continue;
        P = p;
        NN = (int)N;
        make_base_darts();
        double slice = t_end - now();
        if (slice > 3.0) slice = 3.0;
        long b = sa_search(now() + slice);
        if (b == 0 && check_simple() && bad_pairs() == 0 && nv > bestn && nv <= MAXV) {
            store_best();
        }
    }

    printf("%d %d\n", bestn, ne);
    for (int e = 0; e < ne; e++) printf("%d %d\n", eu[e], ev[e]);
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
    if start is not None:
        best = start
    else:
        best = lib.haar_graph(d, range(d))   # K_{d,d}: always valid for D >= 2
    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if start is not None and best[0] >= lib.moore_bound(d, D):
        budget = min(budget, 0.5)   # nothing beats a Moore graph
    if budget > 0.5:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, budget], stdin_graph=None, timeout=budget + 5)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except (RuntimeError, ValueError):
            pass   # keep the valid fallback
    return best
