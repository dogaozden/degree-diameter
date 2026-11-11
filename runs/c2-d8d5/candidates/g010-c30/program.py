"""Bipartite (d, D) graph builder: C voltage search over semidirect-product lifts.

New in this version: the search over bi-Cayley lifts with semidirect-product voltage
groups Z_m x| Z_k2 runs entirely in C. The cost counts (vertex, base-block) pairs that are
still too far apart, computed with 2k-bit reach masks, so one evaluation is a few
bitwise passes over the lift. The C loop samples groups, picks the base size k with a
bandit, and ratchets the target order upward after every success.
"""
import time

import lib


# ----------------------------------------------------------------------------
# C engine: voltage annealer over semidirect-product lifts with a bitmask cost.
#
# Vertices: k left blocks and k right blocks, each block a copy of G = m*k2 elements.
# Layer l pairs left block i with right block perm[l][i] through the voltage s:
#   left (i,g) ~ right (perm, g*s).  Each layer is a perfect matching, so with d layers
#   every vertex has degree d. Duplicate (i, j, s) triples are penalised.
# Left multiplication by G is an automorphism, so requiring every vertex to reach
# every base vertex within D steps is equivalent to the full diameter bound.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;
typedef uint32_t u32;

#define NMAX 20000
#define DMAX 32
#define PEN 1000

static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int n) { return (int)(rnd() % (u64)n); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int d_, D_;
static double tlimit;
static clock_t t_start;
static int min_n = 0;

/* current group and base size */
static int gk, gG, gN, gm, gk2, gr;
static long long PWv[64];

static int perm[DMAX][4];
static int Sv[DMAX][4];
static int *nb;                 /* nb[l*NMAX + v] */
static u32 *bA, *bB, *accR, *candR;

static int best_n = 0, best_m = 0;
static int *bestU, *bestV;
static long long trials[5], wins[5];

static int gcd_(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }
static long long powmod_(long long b, int e, long long m) {
    long long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static int time_up(void) {
    return (double)(clock() - t_start) / CLOCKS_PER_SEC >= tlimit;
}

/* Semidirect product Z_m x| Z_k2 with r^k2 = 1 mod m; element a*k2+b. */
static int gmul(int x, int y) {
    int a = x / gk2, b = x % gk2, c = y / gk2, e = y % gk2;
    long long v = ((long long)a + PWv[b] * c) % gm;
    return (int)(v * gk2 + (b + e) % gk2);
}
static int ginv(int x) {
    int a = x / gk2, b = x % gk2;
    int nbb = (gk2 - b) % gk2;
    long long v = ((-(PWv[nbb] * a)) % gm + gm) % gm;
    return (int)(v * gk2 + nbb);
}

static void setup_group(int m, int k2, int r, int kk) {
    gm = m; gk2 = k2; gr = r; gG = m * k2; gk = kk; gN = 2 * kk * gG;
    PWv[0] = 1 % m;
    for (int b = 1; b < k2; b++) PWv[b] = PWv[b - 1] * r % m;
}

static void set_dart(int l, int i) {
    int j = perm[l][i], s = Sv[l][i];
    int is = ginv(s);
    int *row = nb + (size_t)l * NMAX;
    int bl = i * gG, br = (gk + j) * gG;
    for (int g = 0; g < gG; g++) {
        row[bl + g] = br + gmul(g, s);
        row[br + g] = bl + gmul(g, is);
    }
}

/* Cost = unreached (vertex, base-block) pairs + PEN * duplicate triples.
   Writes the reach masks into candR. */
static long long eval_cost(void) {
    int N = gN, G = gG, k = gk;
    int dup = 0;
    for (int i = 0; i < k; i++)
        for (int l1 = 0; l1 < d_; l1++)
            for (int l2 = l1 + 1; l2 < d_; l2++)
                if (perm[l1][i] == perm[l2][i] && Sv[l1][i] == Sv[l2][i]) dup++;

    u32 *cur = bA, *nxt = bB;
    for (int v = 0; v < N; v++) cur[v] = 0;
    for (int b = 0; b < 2 * k; b++) cur[b * G] |= (1u << b);
    for (int it = 0; it < D_; it++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            u32 x = cur[v];
            for (int l = 0; l < d_; l++) x |= cur[nb[(size_t)l * NMAX + v]];
            nxt[v] = x;
            if (x != cur[v]) changed = 1;
        }
        u32 *t = cur; cur = nxt; nxt = t;
        if (!changed) break;
    }
    long long cnt = 0;
    for (int v = 0; v < N; v++) cnt += __builtin_popcount(cur[v]);
    memcpy(candR, cur, sizeof(u32) * (size_t)N);
    long long unr = (long long)2 * k * N - cnt;
    return unr + (long long)PEN * dup;
}

static int anneal(int iters, int patience) {
    int k = gk, G = gG, N = gN;
    int full = (1 << (2 * k)) - 1;
    for (int l = 0; l < d_; l++) {
        for (int i = 0; i < k; i++) perm[l][i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = perm[l][i]; perm[l][i] = perm[l][j]; perm[l][j] = t;
        }
        for (int i = 0; i < k; i++) Sv[l][i] = rint_(G);
    }
    for (int l = 0; l < d_; l++)
        for (int i = 0; i < k; i++) set_dart(l, i);

    long long cost = eval_cost();
    memcpy(accR, candR, sizeof(u32) * (size_t)N);
    double c0v = cost > 1 ? (double)cost : 1.0;
    long long bestc = cost;
    int last = 0;

    for (int t = 0; t < iters; t++) {
        if (cost == 0) break;
        if (t - last > patience) break;
        if (time_up()) return 0;
        double temp = 0.01 * c0v * (1.0 - (double)t / iters);
        if (temp < 0.5) temp = 0.5;
        double x = rdbl();

        if (k >= 2 && x < 0.25) {
            int l = rint_(d_);
            int i1 = rint_(k), i2 = rint_(k - 1);
            if (i2 >= i1) i2++;
            int tp = perm[l][i1]; perm[l][i1] = perm[l][i2]; perm[l][i2] = tp;
            set_dart(l, i1); set_dart(l, i2);
            long long c2 = eval_cost();
            if (c2 <= cost || rdbl() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                u32 *tmp = accR; accR = candR; candR = tmp;
                if (cost < bestc) { bestc = cost; last = t; }
            } else {
                tp = perm[l][i1]; perm[l][i1] = perm[l][i2]; perm[l][i2] = tp;
                set_dart(l, i1); set_dart(l, i2);
            }
            continue;
        }

        int l = -1, i = -1;
        if (rdbl() < 0.4) {
            /* Targeted: pick a uniformly random unreached vertex and move a voltage at it. */
            int pick = -1, cntb = 0;
            for (int v = 0; v < N; v++)
                if (accR[v] != (u32)full) { cntb++; if (rint_(cntb) == 0) pick = v; }
            if (pick >= 0) {
                int block = pick / G;
                l = rint_(d_);
                if (block < k) {
                    i = block;
                } else {
                    int jj = block - k;
                    for (int ii = 0; ii < k; ii++) if (perm[l][ii] == jj) { i = ii; break; }
                }
            }
        }
        if (i < 0) { l = rint_(d_); i = rint_(k); }

        int oldS = Sv[l][i];
        int ns = rint_(G);
        if (ns == oldS) continue;
        Sv[l][i] = ns;
        set_dart(l, i);
        long long c2 = eval_cost();
        if (c2 <= cost || rdbl() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
            u32 *tmp = accR; accR = candR; candR = tmp;
            if (cost < bestc) { bestc = cost; last = t; }
        } else {
            Sv[l][i] = oldS;
            set_dart(l, i);
        }
    }
    return cost == 0;
}

static void save_best(void) {
    int m = 0, k = gk, G = gG;
    for (int v = 0; v < k * G; v++)
        for (int l = 0; l < d_; l++) {
            bestU[m] = v;
            bestV[m] = nb[(size_t)l * NMAX + v];
            m++;
        }
    best_n = gN;
    best_m = m;
}

static int sample_group(int T, int *mo, int *ko, int *ro) {
    static const int K2S[20] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36};
    for (int tr = 0; tr < 200; tr++) {
        int k2 = K2S[rint_(20)];
        int m = (T + k2 - 1) / k2;
        if (m < 2) m = 2;
        int r = 1;
        if (k2 == 1) {
            r = 1;
        } else if (rint_(4) == 0) {
            r = 1;                       /* direct product */
        } else if (k2 == 2 && rint_(3) == 0) {
            r = m - 1;
            if (gcd_(r, m) != 1 || powmod_(r, 2, m) != 1 % m) continue;
        } else {
            int ok = 0;
            for (int t = 0; t < 60; t++) {
                int c = (m > 2) ? 2 + rint_(m - 2) : 1;
                if (gcd_(c, m) == 1 && powmod_(c, k2, m) == 1 % m) { r = c; ok = 1; break; }
            }
            if (!ok) continue;
        }
        *mo = m; *ko = k2; *ro = r;
        return 1;
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    u64 seed = strtoull(argv[3], NULL, 10);
    rs ^= seed * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    tlimit = atof(argv[4]);
    min_n = argc > 5 ? atoi(argv[5]) : 0;
    if (d_ < 1 || d_ > DMAX || D_ < 1) { printf("0 0\n"); return 0; }

    nb = malloc(sizeof(int) * (size_t)DMAX * NMAX);
    bA = malloc(sizeof(u32) * NMAX);
    bB = malloc(sizeof(u32) * NMAX);
    accR = malloc(sizeof(u32) * NMAX);
    candR = malloc(sizeof(u32) * NMAX);
    bestU = malloc(sizeof(int) * (size_t)NMAX * DMAX);
    bestV = malloc(sizeof(int) * (size_t)NMAX * DMAX);
    if (!nb || !bA || !bB || !accR || !candR || !bestU || !bestV) { printf("0 0\n"); return 0; }

    t_start = clock();
    while (!time_up()) {
        int kk = 1;
        if (rdbl() < 0.2) {
            kk = 1 + rint_(4);
        } else {
            double bs = -1.0;
            for (int k = 1; k <= 4; k++) {
                double sc = (wins[k] + 1.0) / (trials[k] + 2.0) + 0.02 * rdbl();
                if (sc > bs) { bs = sc; kk = k; }
            }
        }
        int lower = best_n > min_n ? best_n : min_n;
        int base = lower / (2 * kk);
        int T = base + 1 + rint_(base / 16 + 2);
        int m, k2, r;
        if (!sample_group(T, &m, &k2, &r)) continue;
        int G = m * k2;
        if (2 * kk * G <= lower || 2 * kk * G > NMAX) continue;
        setup_group(m, k2, r, kk);
        trials[kk]++;
        if (anneal(4000, 1200)) {
            wins[kk]++;
            if (gN > best_n) save_best();
        }
    }

    if (best_n == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", best_n, best_m);
    for (int i = 0; i < best_m; i++) printf("%d %d\n", bestU[i], bestV[i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions and glue.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo and Lopez graph for degree d = q + 2 with q a prime power, or None."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
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

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D == 3:
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])
        return best

    # C voltage search over semidirect-product lifts, seeded with the best known size.
    remaining = time_limit - (time.monotonic() - t0) - 3.0
    if remaining >= 2.0:
        budget = remaining * 0.92
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", best[0]],
                            stdin_graph=None, timeout=remaining)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass  # keep the valid fallback

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
