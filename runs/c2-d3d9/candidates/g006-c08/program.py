"""Bold variant: two-phase search with a new lift family.

Phase 1 is the parent's bi-Cayley scan over groups Z_m x| Z_k (it reproduces the
parent's order when that is the best available). Phase 2 is new: random voltage
lifts of a d-regular bipartite base multigraph with P vertices per side, built
from d perfect matchings (the first is fixed to identity voltages by switching).
Each candidate is scored by simulated annealing on the number of vertex pairs
at distance > D, computed from only 2P BFS runs, since left multiplication by
the group is an automorphism that acts transitively on each fibre. Phase 2 looks
for lifts with more vertices than the best so far, and it rotates through base
sizes P and nearby group orders. Every result is re-verified by a full BFS from
every vertex before printing. If nothing is valid, the C program prints K_{d,d},
and Python keeps the best of the start graph and the C result after lib.is_valid.
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
#define MAXP 12
#define MAXGRP 512
#define PMAX 8

static int d, D;
static double tEnd;

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

static int gcd(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }

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

/* ---------------------------------------------------------- groups Z_m x| Z_k */

typedef struct { int m, k, r; } Grp;

static int enum_into(int n, Grp *arr, int cap) {
    int c = 0;
    for (int m = 1; m <= n; m++) {
        if (n % m) continue;
        int k = n / m;
        if (m == 1) {
            if (c < cap) { arr[c].m = 1; arr[c].k = k; arr[c].r = 0; c++; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            if (c < cap) { arr[c].m = m; arr[c].k = k; arr[c].r = r; c++; }
        }
    }
    return c;
}

/* Element (a, b) is coded a*k + b; (a,b)(c,e) = (a + r^b c mod m, b + e mod k). Identity is 0. */
static int MT[MAXG * MAXG];
static int INVT[MAXG];
static int NN;

static void build_group(Grp G) {
    int n = G.m * G.k;
    NN = n;
    static int rp[MAXG];
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
            if (MT[x * n + y] == 0) { INVT[x] = y; break; }
}

/* ---------------------------------------------------------- phase 1: bi-Cayley */

static int dist_[MAXV], queue_[MAXV];

static int reach_all(const int *S, int src) {
    int n = NN, V = 2 * n;
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
                int u = n + MT[v * n + S[i]];
                if (dist_[u] < 0) { dist_[u] = dv + 1; queue_[tail++] = u; }
            }
        } else {
            int h = v - n;
            for (int i = 0; i < d; i++) {
                int u = MT[h * n + INVT[S[i]]];
                if (dist_[u] < 0) { dist_[u] = dv + 1; queue_[tail++] = u; }
            }
        }
    }
    return tail == V;
}

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

static Grp groups[MAXGRP];
static int bestN = 0;
static Grp bestG;
static int bestS[MAXDEG];

static int search_n(int n, double until) {
    int ng = enum_into(n, groups, MAXGRP);
    if (ng <= 0) return 0;
    int S[MAXDEG];
    while (now() < until) {
        for (int gi = 0; gi < ng; gi++) {
            if (now() >= until) break;
            build_group(groups[gi]);
            for (int t = 0; t < 200; t++) {
                pick_set(n, S);
                if (reach_all(S, 0) && reach_all(S, n)) {
                    bestN = n;
                    bestG = groups[gi];
                    memcpy(bestS, S, sizeof(int) * (size_t)d);
                    return 1;
                }
            }
        }
    }
    return 0;
}

/* ---------------------------------------------------------- phase 2: voltage lifts */

static Grp lgroups[MAXGRP];
static int P_, N_;
static Grp LG;
/* sig[k][i]: matching k sends A_i to B_{sig[k][i]}; sig[0] is the identity. gv[k][i]: voltage. */
static int sig[MAXDEG][MAXP], sinv[MAXDEG][MAXP], gv[MAXDEG][MAXP];
static int bestLP = 0, bestLN = 0, bestLHalf = 0;
static Grp bestLG;
static int bsig[MAXDEG][MAXP], bgv[MAXDEG][MAXP];

/* Vertices: A_(i,x) = i*N + x, B_(j,y) = P*N + j*N + y.
 * Dart (k,i): A_(i,x) ~ B_(sig[k][i], x*g). Returns number of vertices NOT within D of src. */
static int far_from(int src) {
    int P = P_, N = N_, V = 2 * P * N, H = P * N;
    static int dist[MAXV], q[MAXV];
    for (int v = 0; v < V; v++) dist[v] = -1;
    int head = 0, tail = 0;
    dist[src] = 0;
    q[tail++] = src;
    while (head < tail) {
        int v = q[head++];
        int dv = dist[v];
        if (dv >= D) continue;
        if (v < H) {
            int i = v / N, x = v % N;
            for (int k = 0; k < d; k++) {
                int j = sig[k][i];
                int u = H + j * N + MT[x * N + gv[k][i]];
                if (dist[u] < 0) { dist[u] = dv + 1; q[tail++] = u; }
            }
        } else {
            int w = v - H;
            int j = w / N, y = w % N;
            for (int k = 0; k < d; k++) {
                int i = sinv[k][j];
                int x = MT[y * N + INVT[gv[k][i]]];
                int u = i * N + x;
                if (dist[u] < 0) { dist[u] = dv + 1; q[tail++] = u; }
            }
        }
    }
    return V - tail;
}

/* Left multiplication is an automorphism, so BFS from one representative per fibre suffices. */
static long eval_cost(void) {
    long c = 0;
    int P = P_, N = N_, H = P * N;
    for (int i = 0; i < P; i++) {
        c += far_from(i * N);
        c += far_from(H + i * N);
    }
    return c;
}

static void random_setup(int P, int N, Grp G) {
    P_ = P;
    N_ = N;
    LG = G;
    build_group(G);
    for (int k = 0; k < d; k++) {
        int perm[MAXP];
        for (int i = 0; i < P; i++) perm[i] = i;
        if (k > 0)
            for (int i = P - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
            }
        for (int i = 0; i < P; i++) {
            sig[k][i] = perm[i];
            sinv[k][perm[i]] = i;
        }
    }
    for (int i = 0; i < P; i++) gv[0][i] = 0;   /* switching makes matching 0 trivial */
    for (int k = 1; k < d; k++)
        for (int i = 0; i < P; i++) gv[k][i] = rndint(N);
}

static void randomize_voltages(void) {
    for (int k = 1; k < d; k++)
        for (int i = 0; i < P_; i++) gv[k][i] = rndint(N_);
}

/* Simulated annealing on the voltages. Returns 1 when cost 0 is reached (config left in gv). */
static int sa_run(double until, long iters) {
    while (now() < until) {
        randomize_voltages();
        long cost = eval_cost();
        if (cost == 0) return 1;
        const double T0 = 2.0, T1 = 0.05;
        for (long it = 0; it < iters; it++) {
            if ((it & 511) == 0 && now() >= until) break;
            double T = T0 * pow(T1 / T0, (double)it / (double)iters);
            int k = 1 + rndint(d - 1);
            int i = rndint(P_);
            int old = gv[k][i];
            int nw = rndint(N_);
            if (nw == old) continue;
            gv[k][i] = nw;
            long c2 = eval_cost();
            long delta = c2 - cost;
            if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
                cost = c2;
                if (cost == 0) return 1;
            } else {
                gv[k][i] = old;
            }
        }
    }
    return 0;
}

/* ---------------------------------------------------------- explicit graphs */

static int adjl[MAXV][MAXDEG], degl[MAXV];

static void clear_adj(int V) { for (int v = 0; v < V; v++) degl[v] = 0; }

static void add_e(int u, int v) {
    adjl[u][degl[u]++] = v;
    adjl[v][degl[v]++] = u;
}

static int verify_explicit(int V) {
    static int dd[MAXV], qq[MAXV];
    for (int v = 0; v < V; v++)
        if (degl[v] > d || degl[v] < 1) return 0;
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

static void set_complete(void) {
    int V = 2 * d;
    printf("%d %d\n", V, d * d);
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++)
            printf("%d %d\n", a, d + b);
}

static int explicit_bicay(void) {
    if (bestN <= 0) return 0;
    int n = bestN, V = 2 * n;
    build_group(bestG);
    clear_adj(V);
    for (int x = 0; x < n; x++)
        for (int i = 0; i < d; i++) {
            int y = MT[x * n + bestS[i]];
            add_e(x, n + y);
        }
    return verify_explicit(V) ? V : 0;
}

static int explicit_lift(void) {
    if (bestLHalf <= 0) return 0;
    int P = bestLP, N = bestLN, H = P * N, V = 2 * H;
    build_group(bestLG);
    clear_adj(V);
    for (int i = 0; i < P; i++)
        for (int x = 0; x < N; x++) {
            int u = i * N + x;
            for (int k = 0; k < d; k++) {
                int j = bsig[k][i];
                int w = H + j * N + MT[x * N + bgv[k][i]];
                int dup = 0;
                for (int t = 0; t < degl[u]; t++)
                    if (adjl[u][t] == w) { dup = 1; break; }
                if (!dup) add_e(u, w);
            }
        }
    return verify_explicit(V) ? V : 0;
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

    if (d < 2 || d > MAXDEG || D < 2) {
        if (d >= 1 && d <= MAXDEG) set_complete();
        else printf("0 0\n");
        return 0;
    }

    double t0 = now();
    tEnd = t0 + budget * 0.9;
    double tPh1 = t0 + budget * 0.5;

    /* Phase 1: bi-Cayley scan, as in the parent. */
    long moore = moore_bound();
    int nmax = (int)(moore / 2);
    if (nmax > MAXG - 1) nmax = MAXG - 1;
    int nstart = nlo;
    if (nstart < d + 1) nstart = d + 1;
    double slice1 = budget / 60.0;
    if (slice1 < 0.5) slice1 = 0.5;
    if (slice1 > 1.5) slice1 = 1.5;
    for (int n = nstart; n <= nmax && now() < tPh1; n++) {
        double until = now() + slice1;
        if (until > tPh1) until = tPh1;
        search_n(n, until);
    }

    /* Phase 2: voltage lifts with more vertices than the best so far. */
    double slice2 = budget * 0.04;
    if (slice2 < 0.8) slice2 = 0.8;
    if (slice2 > 3.0) slice2 = 3.0;
    int rot = 0;
    while (now() < tEnd) {
        int have = bestN > bestLHalf ? bestN : bestLHalf;
        int H = have + 1;
        int P = 2 + rot % (PMAX - 1);
        rot++;
        int Nc = (H + P - 1) / P + rndint(3);
        if (P * Nc > MAXG) continue;
        int ng = enum_into(Nc, lgroups, MAXGRP);
        if (ng <= 0) continue;
        Grp G = lgroups[rndint(ng)];
        random_setup(P, Nc, G);
        double until = now() + slice2;
        if (until > tEnd) until = tEnd;
        if (sa_run(until, 40000)) {
            bestLP = P;
            bestLN = Nc;
            bestLG = G;
            bestLHalf = P * Nc;
            for (int k = 0; k < d; k++)
                for (int i = 0; i < P; i++) {
                    bsig[k][i] = sig[k][i];
                    bgv[k][i] = gv[k][i];
                }
        }
    }

    int ok = 0;
    if (bestLHalf > bestN) ok = explicit_lift();
    if (!ok && bestN > 0) ok = explicit_bicay();
    if (ok) print_explicit(ok);
    else set_complete();
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

    elapsed = time.monotonic() - t0
    budget = 0.85 * time_limit - elapsed - 2.0
    if budget < 1.0:
        return best

    nlo = max(d + 1, best[0] // 2 + 1, int(0.45 * moore) // 2)
    if nlo > moore // 2:
        return best

    timeout = time_limit - (time.monotonic() - t0) - 3.0
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), nlo],
                         stdin_graph=None, timeout=timeout)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except (RuntimeError, ValueError):
        pass   # keep the valid fallback
    return best
