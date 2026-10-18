"""Cayley-first search for beating the bipartite degree-diameter records.

Python builds the best known construction and keeps it as a fallback. The C engine
tries bipartite Cayley graphs over metacyclic groups of order N, sweeping N downward
from the Moore limit. Each candidate uses connection set S = {e, s_1, ..., s_{d-1}}.
Left multiplication is transitive on each side, so two BFS runs check the diameter.
"""
import time

import lib

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define CAY_MAX 1000
#define MAXD 8
#define MAXGR 4096
#define PAIR_TRIES 600
#define GROUPS_PER_N 20

static int d, D;
static double t_end;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

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

/* ---------------------------------------------------------------- groups */

typedef struct { int m, k, r; } Grp;

/* Multiplication table of Z_m x|_r Z_k, element a*k+b, (a,b)(c,e) = (a + r^b c, b + e). */
static int MT[CAY_MAX * CAY_MAX];
static int INV[CAY_MAX];
static int rp[CAY_MAX];
static int N_;

static void build_group(Grp g) {
    int m = g.m, k = g.k, r = g.r;
    int N = m * k;
    N_ = N;
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            MT[x * N + y] = (int)((a + (long)rp[b] * c) % m) * k + (b + e) % k;
        }
    }
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (MT[x * N + y] == 0) { INV[x] = y; break; }
}

static Grp gl[MAXGR];

/* Enumerate all metacyclic groups of order N into gl; returns the count. */
static int enum_groups(int N) {
    int G = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        if (m == 1) {
            if (G < MAXGR) { gl[G].m = 1; gl[G].k = k; gl[G].r = 0; G++; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1 || powmod(r, k, m) != 1 % m) continue;
            if (G < MAXGR) { gl[G].m = m; gl[G].k = k; gl[G].r = r; G++; }
        }
    }
    return G;
}

/* ---------------------------------------------------------------- Cayley check */

static int Sv[MAXD], Si[MAXD];
static int dist[2 * CAY_MAX], qu[2 * CAY_MAX];
static int found = 0;
static Grp bg;
static int bS[MAXD];

/* Bipartite Cayley graph: A_x -- B_{x s} for s in S. Valid iff BFS from A_e and from B_e
 * reaches every vertex within D steps (left multiplication is a transitive automorphism). */
static int check_cay(void) {
    int N = N_, V = 2 * N;
    for (int src = 0; src < 2; src++) {
        int s0 = src ? N : 0;
        for (int v = 0; v < V; v++) dist[v] = -1;
        int h = 0, t = 0;
        dist[s0] = 0;
        qu[t++] = s0;
        while (h < t) {
            int v = qu[h++];
            if (dist[v] >= D) continue;
            if (v < N) {
                const int *row = MT + v * N;
                for (int i = 0; i < d; i++) {
                    int u = N + row[Sv[i]];
                    if (dist[u] < 0) { dist[u] = dist[v] + 1; qu[t++] = u; }
                }
            } else {
                int y = v - N;
                for (int i = 0; i < d; i++) {
                    int u = MT[y * N + Si[i]];
                    if (dist[u] < 0) { dist[u] = dist[v] + 1; qu[t++] = u; }
                }
            }
        }
        if (t != V) return 0;
    }
    return 1;
}

/* Random connection sets for one group. Returns 1 and records the set on success. */
static int search_group(Grp g, int tries, double until) {
    build_group(g);
    int N = N_;
    if (N < d || N < 2) return 0;
    for (int t = 0; t < tries; t++) {
        if ((t & 63) == 0 && now() > until) return 0;
        Sv[0] = 0;
        int c = 1, guard = 0;
        while (c < d && guard < 1000) {
            guard++;
            int x = 1 + rndint(N - 1), dup = 0;
            for (int i = 0; i < c; i++) if (Sv[i] == x) { dup = 1; break; }
            if (!dup) Sv[c++] = x;
        }
        if (c < d) return 0;
        for (int i = 0; i < d; i++) Si[i] = INV[Sv[i]];
        if (check_cay()) {
            bg = g;
            memcpy(bS, Sv, sizeof(int) * d);
            found = 1;
            return 1;
        }
    }
    return 0;
}

/* Sweep N downward from the Moore limit; the first N with a valid graph is the largest. */
static void search(double until) {
    long moore = moore_bound();
    long Nmax = moore / 2;
    if (Nmax > CAY_MAX) Nmax = CAY_MAX;
    for (int N = (int)Nmax; N >= 2 && now() < until && !found; N--) {
        int G = enum_groups(N);
        if (G == 0) continue;
        for (int i = G - 1; i > 0; i--) {
            int j = rndint(i + 1);
            Grp t = gl[i]; gl[i] = gl[j]; gl[j] = t;
        }
        int lim = G < GROUPS_PER_N ? G : GROUPS_PER_N;
        for (int i = 0; i < lim && !found && now() < until; i++)
            search_group(gl[i], PAIR_TRIES, until);
    }
}

static void print_found(void) {
    if (!found) { printf("0 0\n"); return; }
    build_group(bg);
    int N = N_;
    printf("%d %ld\n", 2 * N, (long)N * d);
    for (int x = 0; x < N; x++)
        for (int i = 0; i < d; i++)
            printf("%d %d\n", x, N + MT[x * N + bS[i]]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 2;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    t_end = now() + limit * 0.92;
    if (d >= 2 && d <= MAXD && D >= 2 && moore_bound() >= 4) search(t_end);
    print_found();
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
    if start is None:
        start = lib.haar_graph(d, range(d))            # K_{d,d}: valid for D >= 2
    if not lib.is_valid(*start, d, D):
        start = (2, [(0, 1)])                          # always valid for d, D >= 1
    best = start

    if best[0] >= lib.moore_bound(d, D):
        return best                                    # Moore graph: nothing to beat

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if budget > 0.5:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, budget], stdin_graph=None,
                             timeout=budget + 5)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(*out, d, D):
                best = out
        except (RuntimeError, ValueError):
            pass   # keep the valid fallback
    return best
