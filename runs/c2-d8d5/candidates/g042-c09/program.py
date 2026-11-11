"""Bi-Cayley voltage lifts over semidirect products Z_m x| Z_k2, searched in C.

Construction: k blocks per side, each block of size G. Layer l joins left block i to right
block perm[l][i] by a voltage vol[l][i] in G, giving (i,g) ~ (j, g*s). Every layer is a perfect
matching, so the lift is d-regular and bipartite. The group acts by left multiplication
as automorphisms, so the distance condition only needs BFS from one representative per block.
The C engine anneals voltages and block permutations, and whenever the cost reaches zero it
keeps the lift and moves to a larger group order.
"""
import math
import random
import time

import lib


C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int n) { return (int)(rnd() % (u64)n); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

#define MAXK 6
#define GMAX 2200
#define MAXD 64

static int d_, D_;
static int K, G, M, K2, RR;
static int pw[GMAX + 1];
static int *MT, *INV;
static int perm[MAXD][MAXK], invp[MAXD][MAXK], vol[MAXD][MAXK];
static int tb[MAXD][2 * MAXK], tv[MAXD][2 * MAXK];
static int *vis, *qb, *qg;
static int stamp_ = 0;
static double tlimit;
static clock_t t_start;
static int best_n = 0, best_m = 0;
static int *bestEu, *bestEv;

static double elapsed(void) { return (double)(clock() - t_start) / CLOCKS_PER_SEC; }

static int gcd_(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }

static int powmod_(long long b, int e, int m) {
    long long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return (int)r;
}

static void setup_group(void) {
    pw[0] = 1 % M;
    for (int t = 1; t < K2; t++) pw[t] = (int)((long long)pw[t - 1] * RR % M);
    for (int x = 0; x < G; x++) {
        int a = x / K2, b = x % K2;
        for (int y = 0; y < G; y++) {
            int c = y / K2, dd = y % K2;
            int aa = (int)(((long long)a + (long long)pw[b] * c) % M);
            int bb = (b + dd) % K2;
            MT[x * G + y] = aa * K2 + bb;
        }
    }
    for (int x = 0; x < G; x++)
        for (int y = 0; y < G; y++)
            if (MT[x * G + y] == 0) { INV[x] = y; break; }
}

static void random_lift(void) {
    for (int l = 0; l < d_; l++) {
        for (int i = 0; i < K; i++) perm[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = perm[l][i]; perm[l][i] = perm[l][j]; perm[l][j] = t;
        }
        for (int i = 0; i < K; i++) {
            invp[l][perm[l][i]] = i;
            vol[l][i] = rint_(G);
        }
    }
}

static void swap_perm(int l, int i1, int i2) {
    int t = perm[l][i1]; perm[l][i1] = perm[l][i2]; perm[l][i2] = t;
    invp[l][perm[l][i1]] = i1;
    invp[l][perm[l][i2]] = i2;
}

static void build_tables(void) {
    for (int l = 0; l < d_; l++) {
        for (int i = 0; i < K; i++) {
            tb[l][i] = K + perm[l][i];
            tv[l][i] = vol[l][i];
        }
        for (int j = 0; j < K; j++) {
            int i = invp[l][j];
            tb[l][K + j] = i;
            tv[l][K + j] = INV[vol[l][i]];
        }
    }
}

static long long dup_count(void) {
    long long dup = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < d_; l1++)
            for (int l2 = l1 + 1; l2 < d_; l2++)
                if (perm[l1][i] == perm[l2][i] && vol[l1][i] == vol[l2][i]) dup++;
    return dup;
}

/* Cost = (representative, vertex) pairs at distance > D, plus a penalty per duplicate edge.
   Zero means valid: the group acts by automorphisms, so BFS from (b,e) for every block b suffices. */
static long long evalcost(void) {
    int N = 2 * K * G;
    long long cost = 0;
    for (int b0 = 0; b0 < 2 * K; b0++) {
        stamp_++;
        int h = 0, t = 0;
        qb[t] = b0; qg[t] = 0; t++;
        vis[b0 * G] = stamp_;
        for (int dep = 0; dep < D_ && h < t; dep++) {
            int end = t;
            while (h < end) {
                int b = qb[h], g = qg[h];
                h++;
                for (int l = 0; l < d_; l++) {
                    int nb = tb[l][b];
                    int ng = MT[g * G + tv[l][b]];
                    int id = nb * G + ng;
                    if (vis[id] != stamp_) {
                        vis[id] = stamp_;
                        qb[t] = nb; qg[t] = ng; t++;
                    }
                }
            }
        }
        cost += N - t;
    }
    long long dup = dup_count();
    return cost + (long long)(2 * N) * dup;
}

static void save_best(void) {
    int m = 0;
    for (int i = 0; i < K; i++)
        for (int g = 0; g < G; g++)
            for (int l = 0; l < d_; l++) {
                int v = i * G + g;
                int w = (K + perm[l][i]) * G + MT[g * G + vol[l][i]];
                bestEu[m] = v; bestEv[m] = w; m++;
            }
    best_n = 2 * K * G;
    best_m = m;
}

/* Simulated annealing over voltages and block permutations. Returns final cost (0 = valid). */
static long long anneal(int iters) {
    random_lift();
    build_tables();
    long long cost = evalcost();
    long long cstart = cost > 0 ? cost : 1;
    double T0 = 0.05 * (double)cstart + 2.0, T1 = 0.3;
    long long bestc = cost;
    int since = 0;
    for (int it = 0; it < iters && cost > 0; it++) {
        if ((it & 127) == 0 && elapsed() > tlimit) break;
        if (since > iters / 3) break;
        double T = T0 * pow(T1 / T0, (double)it / iters);
        int mtype = 0, l = 0, i = 0, i1 = 0, i2 = 0, oldv = 0;
        if (K >= 2 && rdbl() < 0.2) {
            mtype = 1;
            l = rint_(d_);
            i1 = rint_(K);
            do { i2 = rint_(K); } while (i2 == i1);
            swap_perm(l, i1, i2);
        } else {
            l = rint_(d_);
            i = rint_(K);
            oldv = vol[l][i];
            int nv;
            do { nv = rint_(G); } while (nv == oldv);
            vol[l][i] = nv;
        }
        build_tables();
        long long nc = evalcost();
        if (nc <= cost || rdbl() < exp(-(double)(nc - cost) / T)) {
            cost = nc;
        } else {
            if (mtype == 1) swap_perm(l, i1, i2);
            else vol[l][i] = oldv;
            build_tables();
        }
        if (cost < bestc) { bestc = cost; since = 0; }
        else since++;
    }
    return cost;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    double limit = atof(argv[4]);
    if (d_ < 1 || d_ > MAXD || D_ < 1) { printf("0 0\n"); return 0; }

    MT = malloc(sizeof(int) * (size_t)GMAX * GMAX);
    INV = malloc(sizeof(int) * GMAX);
    vis = calloc(2 * MAXK * GMAX + 8, sizeof(int));
    qb = malloc(sizeof(int) * (2 * MAXK * GMAX + 8));
    qg = malloc(sizeof(int) * (2 * MAXK * GMAX + 8));
    bestEu = malloc(sizeof(int) * ((size_t)MAXK * GMAX * d_ + 16));
    bestEv = malloc(sizeof(int) * ((size_t)MAXK * GMAX * d_ + 16));
    if (!MT || !INV || !vis || !qb || !qg || !bestEu || !bestEv) { printf("0 0\n"); return 0; }

    tlimit = limit;
    t_start = clock();
    int Kmax = d_ < MAXK ? d_ : MAXK;
    static int divs[GMAX + 1];

    while (elapsed() < tlimit - 0.3) {
        K = 1 + rint_(Kmax);
        int base = best_n / (2 * K);
        int Gc = base + 1 + rint_(1 + base / 40);
        if (Gc < 2) Gc = 2;
        if (Gc > GMAX) continue;
        G = Gc;

        int nd = 0;
        for (int t = 1; t <= G; t++) if (G % t == 0) divs[nd++] = t;
        K2 = divs[rint_(nd)];
        M = G / K2;

        RR = 1 % M;
        if (K2 > 1 && M >= 2 && rint_(10) < 7) {
            for (int tries = 0; tries < 60; tries++) {
                int r = 1 + rint_(M - 1);
                if (gcd_(r, M) == 1 && powmod_(r, K2, M) == 1 % M) { RR = r; break; }
            }
        }
        if (M == 1) RR = 0;

        setup_group();
        long long res = anneal(6000);
        if (res == 0) {
            int N = 2 * K * G;
            if (N > best_n) save_best();
        }
    }

    if (best_n == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", best_n, best_m);
    for (int e = 0; e < best_m; e++) printf("%d %d\n", bestEu[e], bestEv[e]);
    return 0;
}
"""


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}, valid for D >= 2

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact construction for D = 3 (calibration case): return immediately.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    # Bi-Cayley lift search in C over semidirect products.
    budget = time_limit - (time.monotonic() - t0) - 10.0
    if budget >= 3.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                            stdin_graph=None, timeout=budget + 20.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass  # keep the valid fallback

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
