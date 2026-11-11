"""Bi-Cayley (generalized Haar) graphs over metacyclic groups, searched by hill climbing.

Construction: for a group G of order N and a connection set S = {0, s_1, ..., s_{d-1}}
(WLOG 0 is in S), the bipartite graph has parts A_x, B_x (x in G) and edges A_x ~ B_{x s}.
Left multiplication is an automorphism, so only two BFS runs (from A_0 and B_0) are needed
to check the diameter.

Change in this version: instead of sampling random connection sets, each group runs a
simulated-annealing climb on S. The cost is the number of (vertex, source) pairs left
unreached within distance D from A_0 and B_0, so cost 0 means a valid graph. The climb
replaces one generator at a time. Group multiplication is computed by formula, so no
N x N table is built, and each evaluation is cheap.

The order scan starts closer to the known record (about 0.47 of the Moore bound) and
gives each order a slice of the time budget. Any graph found is re-verified by a full BFS
from every vertex before it is printed. If nothing is found, the C program prints K_{d,d}.
Python keeps the best of the known start and the C result, and checks everything with
lib.is_valid.
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

#define MAXG 1024
#define MAXV (2 * MAXG)
#define MAXDEG 16
#define MAXGRP 4096
#define ITERS 2000

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
static Grp groups[MAXGRP];
static int ngroups;

/* Nonabelian groups (r != 1) first, then abelian ones. */
static void enum_groups(int n) {
    ngroups = 0;
    for (int pass = 0; pass < 2; pass++) {
        for (int m = 1; m <= n; m++) {
            if (n % m) continue;
            int k = n / m;
            if (m == 1) {
                if (pass == 1 && ngroups < MAXGRP) {
                    groups[ngroups].m = 1;
                    groups[ngroups].k = k;
                    groups[ngroups].r = 0;
                    ngroups++;
                }
                continue;
            }
            for (int r = 1; r < m; r++) {
                if (gcd(r, m) != 1) continue;
                if (powmod(r, k, m) != 1 % m) continue;
                int nonab = (r != 1);
                if ((pass == 0) != nonab) continue;
                if (ngroups < MAXGRP) {
                    groups[ngroups].m = m;
                    groups[ngroups].k = k;
                    groups[ngroups].r = r;
                    ngroups++;
                }
            }
        }
    }
}

/* Current group. Element (a,b) is coded a*GK+b; (a,b)(c,e) = (a + RP[b] c mod GM, b+e mod GK). */
static int GM, GK, GN;
static int RP[MAXG];   /* RP[b] = r^b mod m */

static void build_group(Grp G) {
    GM = G.m;
    GK = G.k;
    GN = G.m * G.k;
    RP[0] = 1 % GM;
    for (int b = 1; b < GK; b++) RP[b] = (int)((long)RP[b - 1] * G.r % GM);
}

static inline int gmul(int x, int y) {
    int a = x / GK, b = x % GK, c = y / GK, e = y % GK;
    int na = (int)(((long)a + (long)RP[b] * c) % GM);
    int nb = b + e;
    if (nb >= GK) nb -= GK;
    return na * GK + nb;
}

/* Inverse of (a,b) is (-r^{-b} a, -b), and r^{-b} = RP[(k-b) mod k] since r^k = 1. */
static inline int ginv(int x) {
    int a = x / GK, b = x % GK;
    int nb = (GK - b) % GK;
    long na = (-((long)RP[nb] * a)) % GM;
    if (na < 0) na += GM;
    return (int)na * GK + nb;
}

/* ---------------------------------------------------------- bi-Cayley evaluation */

static int dist_[MAXV], queue_[MAXV];
static int SI[MAXDEG];   /* inverses of the current connection set */

/* Number of vertices within distance D of src.
 * Vertex A_x = x, B_h = GN + h. A_x ~ B_{x s}; B_h ~ A_{h s^-1}. */
static int reach_count(const int *S, int src) {
    int n = GN, V = 2 * n;
    for (int i = 0; i < V; i++) dist_[i] = -1;
    int head = 0, tail = 0;
    dist_[src] = 0;
    queue_[tail++] = src;
    while (head < tail) {
        int v = queue_[head++];
        int dv = dist_[v];
        if (dv >= D) continue;
        if (v < n) {
            for (int i = 0; i < d; i++) {
                int u = n + gmul(v, S[i]);
                if (dist_[u] < 0) { dist_[u] = dv + 1; queue_[tail++] = u; }
            }
        } else {
            int h = v - n;
            for (int i = 0; i < d; i++) {
                int u = gmul(h, SI[i]);
                if (dist_[u] < 0) { dist_[u] = dv + 1; queue_[tail++] = u; }
            }
        }
    }
    return tail;
}

/* Number of (vertex, source) pairs left unreached. 0 iff S gives diameter <= D. */
static int cost_of(const int *S) {
    int V = 2 * GN;
    for (int i = 0; i < d; i++) SI[i] = ginv(S[i]);
    int r0 = reach_count(S, 0);
    int r1 = reach_count(S, GN);
    return (V - r0) + (V - r1);
}

/* S[0] = 0, and S[1..d-1] are distinct nonzero elements. */
static void pick_set(int n, int *S) {
    S[0] = 0;
    for (int i = 1; i < d; i++) {
        for (;;) {
            int x = 1 + rndint(n - 1);
            int dup = 0;
            for (int j = 0; j < i; j++)
                if (S[j] == x) { dup = 1; break; }
            if (!dup) { S[i] = x; break; }
        }
    }
}

/* Simulated-annealing climb on S for the current group. Returns 1 if cost 0 is reached. */
static int climb(int *S, double until) {
    int n = GN;
    pick_set(n, S);
    int cur = cost_of(S);
    for (int it = 0; it < ITERS && cur > 0; it++) {
        if ((it & 31) == 0 && now() >= until) break;
        double T = 2.0 * (1.0 - (double)it / ITERS) + 0.02;
        int i = 1 + rndint(d - 1);
        int old = S[i], x;
        for (;;) {
            x = 1 + rndint(n - 1);
            int dup = 0;
            for (int j = 0; j < d; j++)
                if (S[j] == x) { dup = 1; break; }
            if (!dup) break;
        }
        S[i] = x;
        int nc = cost_of(S);
        int delta = nc - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) cur = nc;
        else S[i] = old;
    }
    return cur == 0;
}

/* ---------------------------------------------------------- search state */

static int bestN = 0;
static Grp bestG;
static int bestS[MAXDEG];

/* Try groups of order n, each with a climb, until success or the time slice ends. */
static int search_n(int n, double until) {
    enum_groups(n);
    if (ngroups == 0) return 0;
    int S[MAXDEG];
    for (int g = 0; now() < until; g++) {
        Grp G = groups[g % ngroups];
        build_group(G);
        if (climb(S, until)) {
            bestN = n;
            bestG = G;
            memcpy(bestS, S, sizeof(int) * (size_t)d);
            return 1;
        }
    }
    return 0;
}

/* ---------------------------------------------------------- explicit graph */

static int adjl[MAXV][MAXDEG], degl[MAXV];

static void add_e(int u, int v) {
    adjl[u][degl[u]++] = v;
    adjl[v][degl[v]++] = u;
}

/* Full BFS from every vertex with explicit adjacency. */
static int verify_explicit(int V) {
    static int dd[MAXV], qq[MAXV];
    for (int v = 0; v < V; v++) if (degl[v] > d || degl[v] < 1) return 0;
    for (int s = 0; s < V; s++) {
        for (int i = 0; i < V; i++) dd[i] = -1;
        int head = 0, tail = 0;
        dd[s] = 0;
        qq[tail++] = s;
        while (head < tail) {
            int v = qq[head++];
            if (dd[v] >= D) continue;
            for (int i = 0; i < degl[v]; i++) {
                int u = adjl[v][i];
                if (dd[u] < 0) { dd[u] = dd[v] + 1; qq[tail++] = u; }
            }
        }
        if (tail != V) return 0;
    }
    return 1;
}

static void set_complete(void) {
    int V = 2 * d;
    for (int v = 0; v < V; v++) degl[v] = 0;
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_e(a, d + b);
    printf("%d %d\n", V, d * d);
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) printf("%d %d\n", a, d + b);
}

static void print_explicit(int V) {
    long m = 0;
    for (int u = 0; u < V; u++)
        for (int i = 0; i < degl[u]; i++)
            if (u < adjl[u][i]) m++;
    printf("%d %ld\n", V, m);
    for (int u = 0; u < V; u++)
        for (int i = 0; i < degl[u]; i++)
            if (u < adjl[u][i]) printf("%d %d\n", u, adjl[u][i]);
}

/* ---------------------------------------------------------- main */

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: %s d D seed budget nlo\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double budget = atof(argv[4]);
    int nlo = atoi(argv[5]);

    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXDEG) { printf("0 0\n"); return 0; }

    double t0 = now();
    t_end = t0 + budget * 0.95;

    long moore = moore_bound();
    int nmax = (int)(moore / 2);
    if (nmax > MAXG - 1) nmax = MAXG - 1;
    int nstart = nlo;
    if (nstart < d + 1) nstart = d + 1;
    double slice = budget / 25.0;
    if (slice < 0.3) slice = 0.3;
    if (slice > 2.0) slice = 2.0;

    if (d >= 2 && D >= 2) {
        for (int n = nstart; n <= nmax && now() < t_end; n++) {
            double until = now() + slice;
            if (until > t_end) until = t_end;
            search_n(n, until);
        }
    }

    int ok = 0;
    if (bestN > 0) {
        int n = bestN, V = 2 * n;
        build_group(bestG);
        for (int v = 0; v < V; v++) degl[v] = 0;
        for (int x = 0; x < n; x++)
            for (int i = 0; i < d; i++) {
                int y = gmul(x, bestS[i]);
                add_e(x, n + y);
            }
        ok = verify_explicit(V);
        if (ok) print_explicit(V);
    }
    if (!ok) set_complete();
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

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if budget < 1.0:
        return best

    # Lower bound for the scan: about 0.47 of the Moore bound (in half-order units),
    # and never below what we already have.
    nlo = max(d + 1, best[0] // 2 + 1, int(0.47 * moore) // 2)
    if nlo > moore // 2:
        return best

    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), nlo],
                         stdin_graph=None, timeout=budget + 5)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except (RuntimeError, ValueError):
        pass   # keep the valid fallback
    return best
