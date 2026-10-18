import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bi-Cayley (voltage) lift search over semidirect products
# G = Z_m x| Z_k2 (element a*k2+b, (a,b)(c,e) = (a + r^b c, b+e)).
#
# A graph has 2K blocks of |G| vertices: left blocks 0..K-1, right blocks K..2K-1.
# Vertex (block, g) has one neighbour per layer l. Left (i, g) joins right
# (j, g*s) where j = lay[l][i] and s = S[l][i]. Left multiplication by G is an
# automorphism, so validity reduces to: every vertex reaches, within D steps,
# the identity of every block. Cost = unreached (vertex, block) pairs plus a
# penalty for parallel darts. The search climbs: each success raises the
# required order, and random groups are sampled for each trial.
# ----------------------------------------------------------------------------

LIFT_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;
typedef uint32_t u32;

#define MAXD 16
#define MAXK 8
#define MAXV 40000
#define PEN 50

static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int n) { return (int)(rnd() % (u64)n); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now_s(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int d_, D_, K_, G_, m_, k2_;
static long long pw_[64];
static u32 full_;
static double deadline_;
static int lay[MAXD][MAXK];
static int S[MAXD][MAXK];
static int nbr[MAXD][MAXV];
static u32 bufA[MAXV], bufB[MAXV];
static u32 *reachF = bufA;
static int *bestEu, *bestEv;
static int bestM_ = 0, bestN_ = 0;

static long long gcdll(long long a, long long b) {
    while (b) { long long t = a % b; a = b; b = t; }
    return a;
}

static long long powmod(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static int gmul(int x, int y) {
    int a = x / k2_, b = x % k2_;
    int c = y / k2_, e = y % k2_;
    long long A = ((long long)a + pw_[b] * (long long)c) % m_;
    int B = (b + e) % k2_;
    return (int)A * k2_ + B;
}

static void set_dart(int l, int i) {
    int j = lay[l][i], s = S[l][i];
    for (int g = 0; g < G_; g++) {
        int h = gmul(g, s);
        int lv = i * G_ + g;
        int rv = (K_ + j) * G_ + h;
        nbr[l][lv] = rv;
        nbr[l][rv] = lv;
    }
}

static int dupcount(void) {
    int dup = 0;
    for (int i = 0; i < K_; i++)
        for (int l = 0; l < d_; l++)
            for (int l2 = l + 1; l2 < d_; l2++)
                if (lay[l][i] == lay[l2][i] && S[l][i] == S[l2][i]) dup++;
    return dup;
}

static long long reach_cost(void) {
    int N = 2 * K_ * G_;
    u32 *c = bufA, *x = bufB;
    for (int v = 0; v < N; v++) c[v] = 0;
    for (int b = 0; b < 2 * K_; b++) c[b * G_] = 1u << b;
    for (int t = 0; t < D_; t++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            u32 y = c[v];
            for (int l = 0; l < d_; l++) y |= c[nbr[l][v]];
            x[v] = y;
            if (y != c[v]) changed = 1;
        }
        u32 *tmp = c; c = x; x = tmp;
        if (!changed) break;
    }
    reachF = c;
    long long cost = 0;
    for (int v = 0; v < N; v++) cost += __builtin_popcount(full_ & ~c[v]);
    return cost;
}

static long long total_cost(void) {
    return (long long)PEN * dupcount() + reach_cost();
}

static int anneal(int maxIt, int patience) {
    long long cost = total_cost();
    long long bestc = cost;
    double c0 = (double)(cost > 1 ? cost : 1);
    int N = 2 * K_ * G_;
    int last = 0;
    for (int it = 0; it < maxIt && cost > 0; it++) {
        if (it - last > patience) break;
        if ((it & 127) == 0 && now_s() > deadline_) break;
        double frac = (double)it / (double)maxIt;
        double T = 0.3 + 0.05 * c0 * (1.0 - frac);
        if (K_ >= 2 && rdbl() < 0.25) {
            int l = rint_(d_);
            int i1 = rint_(K_), i2 = rint_(K_ - 1);
            if (i2 >= i1) i2++;
            int t = lay[l][i1]; lay[l][i1] = lay[l][i2]; lay[l][i2] = t;
            set_dart(l, i1); set_dart(l, i2);
            long long nc = total_cost();
            if (nc <= cost || rdbl() < exp(-(double)(nc - cost) / T)) {
                cost = nc;
            } else {
                t = lay[l][i1]; lay[l][i1] = lay[l][i2]; lay[l][i2] = t;
                set_dart(l, i1); set_dart(l, i2);
            }
        } else {
            int l = rint_(d_), i = rint_(K_);
            if (rdbl() < 0.4) {
                for (int tries = 0; tries < 30; tries++) {
                    int v = rint_(N);
                    if (reachF[v] != full_) {
                        int block = v / G_;
                        if (block < K_) {
                            i = block;
                        } else {
                            int j = block - K_;
                            for (int ii = 0; ii < K_; ii++)
                                if (lay[l][ii] == j) { i = ii; break; }
                        }
                        break;
                    }
                }
            }
            int old = S[l][i];
            int ns = rint_(G_);
            if (ns == old) continue;
            S[l][i] = ns;
            set_dart(l, i);
            long long nc = total_cost();
            if (nc <= cost || rdbl() < exp(-(double)(nc - cost) / T)) {
                cost = nc;
            } else {
                S[l][i] = old;
                set_dart(l, i);
            }
        }
        if (cost < bestc) { bestc = cost; last = it; }
    }
    return cost == 0;
}

static void save_edges(void) {
    int L = K_ * G_, m = 0;
    for (int v = 0; v < L; v++)
        for (int l = 0; l < d_; l++) {
            bestEu[m] = v;
            bestEv[m] = nbr[l][v];
            m++;
        }
    bestM_ = m;
}

int main(int argc, char **argv) {
    if (argc < 6) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    u64 seed = strtoull(argv[3], NULL, 10);
    rs ^= seed * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double limit = atof(argv[4]);
    int minN = atoi(argv[5]);
    if (d_ < 2 || d_ > MAXD || D_ < 1 || minN < 0) { printf("0 0\n"); return 0; }

    bestEu = malloc(sizeof(int) * (size_t)MAXV * MAXD);
    bestEv = malloc(sizeof(int) * (size_t)MAXV * MAXD);
    if (!bestEu || !bestEv) { printf("0 0\n"); return 0; }

    double start = now_s();
    deadline_ = start + limit;
    bestN_ = minN;

    static const int Kopts[] = {1, 2, 2, 3, 3, 4, 4, 5, 6};
    static const int K2opts[] = {1, 2, 2, 3, 4, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24};
    const int nK = (int)(sizeof(Kopts) / sizeof(Kopts[0]));
    const int nK2 = (int)(sizeof(K2opts) / sizeof(K2opts[0]));

    while (now_s() < deadline_) {
        int step = bestN_ / 100;
        if (step < 2) step = 2;
        int want = bestN_ + step;
        int K = Kopts[rint_(nK)];
        int Gmin = (want + 2 * K - 1) / (2 * K);

        int bestG = -1, bm = 0, bk2 = 0;
        long long br = 0;
        for (int tries = 0; tries < 40; tries++) {
            int k2 = K2opts[rint_(nK2)];
            int m = (Gmin + k2 - 1) / k2;
            if (m < 2) m = 2;
            int G = m * k2;
            if (bestG >= 0 && G >= bestG) continue;
            if (2 * K * G > MAXV) continue;
            long long r = -1;
            if (k2 == 1) {
                r = 0;
            } else {
                for (int t = 0; t < 200; t++) {
                    long long c = 1 + rint_(m - 1);
                    if (gcdll(c, m) == 1 && powmod(c, k2, m) == 1 % m) { r = c; break; }
                }
            }
            if (r < 0) continue;
            bestG = G; bm = m; bk2 = k2; br = r;
        }
        if (bestG < 0) continue;

        m_ = bm; k2_ = bk2;
        G_ = bm * bk2;
        K_ = K;
        full_ = (1u << (2 * K_)) - 1;
        pw_[0] = 1 % m_;
        for (int t = 1; t < k2_; t++) pw_[t] = pw_[t - 1] * br % m_;

        for (int l = 0; l < d_; l++) {
            for (int i = 0; i < K_; i++) lay[l][i] = i;
            for (int i = K_ - 1; i > 0; i--) {
                int j = rint_(i + 1);
                int t = lay[l][i]; lay[l][i] = lay[l][j]; lay[l][j] = t;
            }
            for (int i = 0; i < K_; i++) S[l][i] = rint_(G_);
        }
        for (int l = 0; l < d_; l++)
            for (int i = 0; i < K_; i++) set_dart(l, i);

        if (anneal(30000, 4000)) {
            save_edges();
            bestN_ = 2 * K_ * G_;
        }
    }

    if (bestM_ == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", bestN_, bestM_);
    for (int i = 0; i < bestM_; i++) printf("%d %d\n", bestEu[i], bestEv[i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python glue and deterministic constructions.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _lift_in_c(d, D, seed, seconds, min_n):
    """Run the C voltage-lift climber; returns (n, edges), or (0, []) if nothing beat min_n."""
    out = lib.run_c(LIFT_SOURCE, [d, D, seed, f"{seconds:.2f}", min_n],
                    stdin_graph=None, timeout=seconds + 4.0)
    return lib.parse_graph_text(out)


def build(d, D, seed, time_limit):
    t0 = time.monotonic()

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}: valid for D >= 2

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

    # Main phase: voltage lifts over random semidirect products, climbing in order.
    if d >= 3 and D >= 2:
        left = time_limit - 9.0 - (time.monotonic() - t0)
        if left >= 2.0:
            try:
                cseed = abs(int(seed)) % (1 << 30) + 1
                n, e = _lift_in_c(d, D, cseed, left, best[0])
                consider(n, e)
            except Exception:
                pass  # keep the valid fallback

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
