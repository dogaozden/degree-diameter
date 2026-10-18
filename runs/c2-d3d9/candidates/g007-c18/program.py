"""Bold variant: voltage lifts of multi-vertex bipartite base graphs over metacyclic groups.

Parent approach: bi-Cayley graphs, i.e. one base pair (A, B) with d parallel-class darts.
This variant uses a different family. The base is a d-regular bipartite multigraph on P+P
vertices, built from d permutations sigma_k of {0..P-1}: dart k joins left i to right sigma_k(i).
Each dart carries a voltage g in a metacyclic group G = Z_m x| Z_k of order N. The lift has
vertices (side, base index, x in G), with (L_i, x) ~ (R_j, x g) for each dart from i to j.

Key facts used by the search:
  - Right multiplication by G is not an automorphism, but left multiplication is. So the lift
    is symmetric within each fiber, and the diameter equals the max eccentricity over the 2P
    base representatives (L_i, 1) and (R_j, 1). That is 2P BFS runs, not 2PN.
  - Simple-graph condition: two darts from the same left vertex to the same right vertex must
    have different voltages. Violations are penalised.

Search: simulated annealing over voltages and permutations, minimising the number of
(vertex, unreachable-within-D) pairs summed over the representatives. For each base size P in
a rotating schedule, the order N is raised one step at a time after each success. The output is
the largest valid lift found, or K_{d,d} if none beats the start. Python checks everything with
lib.is_valid and keeps the best of the known start and the C result.
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

#define MAXN 1024
#define MAXP 8
#define MAXD 16
#define MAXV (2 * MAXP * MAXN)
#define MAXGRP 4096
#define ITERS 30000
#define PEN_T 1.0

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
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

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

/* ---------------------------------------------------------- groups Z_m x| Z_k */

typedef struct { int m, k, r; } Grp;
static Grp grp_list[MAXGRP];
static int ngrp;

static void enum_groups(int n) {
    ngrp = 0;
    for (int m = 1; m <= n; m++) {
        if (n % m) continue;
        int k = n / m;
        for (int r = 0; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            if (ngrp < MAXGRP) {
                grp_list[ngrp].m = m;
                grp_list[ngrp].k = k;
                grp_list[ngrp].r = r;
                ngrp++;
            }
        }
    }
}

static int N;                 /* current group order */
static int MT[MAXN * MAXN];   /* multiplication table, stride N */
static int INV[MAXN];

/* Element (a, b) is coded a*k + b; (a,b)(c,e) = (a + r^b c mod m, b + e mod k). */
static void build_group(Grp G) {
    int n = G.m * G.k;
    N = n;
    int rp[MAXN];
    rp[0] = 1 % G.m;
    for (int b = 1; b < G.k; b++) rp[b] = (int)((long)rp[b - 1] * G.r % G.m);
    for (int x = 0; x < n; x++) {
        int a = x / G.k, b = x % G.k;
        for (int y = 0; y < n; y++) {
            int c = y / G.k, e = y % G.k;
            MT[x * n + y] = (int)(((long)a + (long)rp[b] * c) % G.m) * G.k + (b + e) % G.k;
        }
    }
    for (int x = 0; x < n; x++)
        for (int y = 0; y < n; y++)
            if (MT[x * n + y] == 0) { INV[x] = y; break; }
}

/* ---------------------------------------------------------- voltage lift state */

static int P;                   /* base vertices per side */
static int sig[MAXD][MAXP];     /* dart k: left i -> right sig[k][i] */
static int isig[MAXD][MAXP];    /* inverse: isig[k][j] = i */
static int volt[MAXP][MAXD];    /* voltage of dart k at left i */

/* Vertex ids: side*P + idx, times N, plus x.  Left side = 0, right side = 1. */
static int dist_[MAXV], qu[MAXV];

/* BFS from src in the lift; returns the number of vertices within distance D. */
static int bfs_count(int src) {
    int V = 2 * P * N, LN = P * N;
    for (int v = 0; v < V; v++) dist_[v] = -1;
    int h = 0, t = 0;
    dist_[src] = 0;
    qu[t++] = src;
    while (h < t) {
        int v = qu[h++];
        int dv = dist_[v];
        if (dv >= D) continue;
        if (v < LN) {
            int i = v / N, x = v % N;
            for (int k = 0; k < d; k++) {
                int j = sig[k][i];
                int y = MT[x * N + volt[i][k]];
                int u = (P + j) * N + y;
                if (dist_[u] < 0) { dist_[u] = dv + 1; qu[t++] = u; }
            }
        } else {
            int w = v - LN, j = w / N, y = w % N;
            for (int k = 0; k < d; k++) {
                int i = isig[k][j];
                int x = MT[y * N + INV[volt[i][k]]];
                int u = i * N + x;
                if (dist_[u] < 0) { dist_[u] = dv + 1; qu[t++] = u; }
            }
        }
    }
    return t;
}

/* 0 iff the lift is simple and has diameter <= D. Otherwise a positive penalty. */
static long cost_of_state(void) {
    int V = 2 * P * N;
    long bad = 0;
    for (int r = 0; r < 2 * P; r++) {
        int reached = bfs_count(r * N);   /* representative (side, idx, identity) */
        bad += V - reached;
    }
    long dup = 0;
    for (int i = 0; i < P; i++)
        for (int k = 0; k < d; k++)
            for (int k2 = k + 1; k2 < d; k2++)
                if (sig[k][i] == sig[k2][i] && volt[i][k] == volt[i][k2]) dup++;
    return bad + (long)V * dup;
}

static void random_state(void) {
    for (int k = 0; k < d; k++) {
        for (int i = 0; i < P; i++) sig[k][i] = i;
        for (int i = P - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int tmp = sig[k][i];
            sig[k][i] = sig[k][j];
            sig[k][j] = tmp;
        }
        for (int i = 0; i < P; i++) isig[k][sig[k][i]] = i;
    }
    for (int i = 0; i < P; i++)
        for (int k = 0; k < d; k++)
            volt[i][k] = rndint(N);
}

/* ---------------------------------------------------------- search state */

static int bestV = 0, bestP = 0;
static Grp bestG;
static int bestSig[MAXD][MAXP];
static int bestVolt[MAXP][MAXD];

/* Anneal over voltages and permutations for base size p and group order n, until 'until'.
 * Returns 1 and records the result in best* if a valid lift is found. */
static int try_state_search(int p, int n, double until) {
    P = p;
    enum_groups(n);
    if (ngrp == 0) return 0;
    while (now() < until) {
        Grp G = grp_list[rndint(ngrp)];
        build_group(G);
        random_state();
        long cur = cost_of_state();
        const double T0 = 10.0, T1 = 0.2;
        int found = 0;
        for (int it = 0; it < ITERS && now() < until; it++) {
            if (cur == 0) { found = 1; break; }
            double T = T0 * pow(T1 / T0, (double)it / ITERS);
            if (rndint(10) < 6) {
                /* change one voltage */
                int i = rndint(P), k = rndint(d);
                int old = volt[i][k];
                int nv = rndint(N);
                if (nv == old) continue;
                volt[i][k] = nv;
                long c = cost_of_state();
                long delta = c - cur;
                if (delta <= 0 || rnd01() < exp(-(double)delta / T)) cur = c;
                else volt[i][k] = old;
            } else {
                /* swap two images under one permutation */
                int k = rndint(d), i1 = rndint(P), i2 = rndint(P);
                if (i1 == i2) continue;
                int j1 = sig[k][i1], j2 = sig[k][i2];
                sig[k][i1] = j2;
                sig[k][i2] = j1;
                isig[k][j2] = i1;
                isig[k][j1] = i2;
                long c = cost_of_state();
                long delta = c - cur;
                if (delta <= 0 || rnd01() < exp(-(double)delta / T)) cur = c;
                else {
                    sig[k][i1] = j1;
                    sig[k][i2] = j2;
                    isig[k][j1] = i1;
                    isig[k][j2] = i2;
                }
            }
        }
        if (!found && cur == 0) found = 1;
        if (found) {
            long ord = 2L * p * n;
            if (ord > bestV) {
                bestV = (int)ord;
                bestP = p;
                bestG = G;
                memcpy(bestSig, sig, sizeof sig);
                memcpy(bestVolt, volt, sizeof volt);
            }
            return 1;
        }
    }
    return 0;
}

/* ---------------------------------------------------------- output */

static void set_complete(void) {
    printf("%d %d\n", 2 * d, d * d);
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) printf("%d %d\n", a, d + b);
}

static void print_best(void) {
    if (bestV == 0) { set_complete(); return; }
    P = bestP;
    build_group(bestG);
    memcpy(sig, bestSig, sizeof sig);
    memcpy(volt, bestVolt, sizeof volt);
    for (int k = 0; k < d; k++)
        for (int i = 0; i < P; i++) isig[k][sig[k][i]] = i;
    if (cost_of_state() != 0) { set_complete(); return; }
    int LN = P * N, V = 2 * LN;
    printf("%d %d\n", V, d * LN);
    for (int i = 0; i < P; i++)
        for (int x = 0; x < N; x++)
            for (int k = 0; k < d; k++) {
                int u = i * N + x;
                int v = (P + sig[k][i]) * N + MT[x * N + volt[i][k]];
                printf("%d %d\n", u, v);
            }
}

/* ---------------------------------------------------------- main */

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed budget\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double budget = atof(argv[4]);

    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 2) { printf("0 0\n"); return 0; }

    double t0 = now();
    t_end = t0 + budget * 0.92;

    long moore = moore_bound();
    int pset[] = {2, 1, 3, 4, 6, 5, 8};
    int np = (int)(sizeof pset / sizeof pset[0]);
    int Nn[8];
    for (int idx = 0; idx < np; idx++) {
        int p = pset[idx];
        long start = (long)(0.4 * (double)moore / (2.0 * p));
        if (start < d + 1) start = d + 1;
        if (start > MAXN) start = MAXN;
        Nn[idx] = (int)start;
    }

    double slice = budget / 20.0;
    if (slice < 0.8) slice = 0.8;
    if (slice > 3.0) slice = 3.0;

    while (now() < t_end) {
        for (int idx = 0; idx < np && now() < t_end; idx++) {
            int p = pset[idx];
            double until = now() + slice;
            if (until > t_end) until = t_end;
            while (now() < until && Nn[idx] <= MAXN) {
                if (try_state_search(p, Nn[idx], until)) Nn[idx]++;
                else break;
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


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    start = known_start(d, D)
    best = start if start is not None else lib.haar_graph(d, range(d))   # K_{d,d}
    moore = lib.moore_bound(d, D)
    if best[0] >= moore or d < 2 or D < 2 or d > 16:
        return best

    budget = 0.80 * time_limit - (time.monotonic() - t0) - 2.0
    if budget < 1.0:
        return best

    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=None, timeout=budget + 8)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except (RuntimeError, ValueError):
        pass   # keep the valid fallback
    return best
