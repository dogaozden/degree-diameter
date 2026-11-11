import time

import lib


# ----------------------------------------------------------------------------
# C engine: bi-Cayley lift search over semidirect products Z_m x| Z_k2.
#
# The graph is a lift of a base bipartite multigraph with k vertices per side,
# where each side is a copy of a group G of order m*k2. Layer l joins A_i to
# B_{perm_l(i)} through a voltage s: A_i,g ~ B_j,g*s. Every layer is a perfect
# matching between blocks, so the lift is d-regular and bipartite.
#
# Validity is checked by ball expansion from the identity of each base block
# (G-invariance makes this sufficient). The search anneals the layer
# permutations and voltages to remove unreached pairs. It repeatedly samples
# a group slightly larger than the current best and keeps the largest success.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

#define KMAX 5
#define CAPN 80000
#define MAXS 64

static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int n) { return (int)(rnd() % (u64)n); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int d_, D_;
static double limit_;
static clock_t c0_;

static int K, G, GM, K2, N;
static int pw[MAXS];
static int *nbr, *lay, *Sv;
static u64 *rA, *rB, *rf;
static u64 fullm;
static int *bestU, *bestV, best_n = 0, best_m = 0;

static const int KS2[20] = {1,1,2,2,3,4,5,6,7,8,9,10,12,14,16,18,20,24,30,36};

static int timeup(void) {
    return (double)(clock() - c0_) / CLOCKS_PER_SEC >= limit_;
}

static int gcd_(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static long long powmod_(long long b, int e, int m) {
    long long r = 1 % m, x = b % m;
    while (e > 0) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return r;
}

/* Element a*K2+b, product (a,b)(c,e) = (a + r^b c, b + e). */
static int gmul_(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, e = y % K2;
    long long t = ((long long)a + (long long)pw[b] * c) % GM;
    return (int)(t * K2 + (b + e) % K2);
}

/* Inverse of (a,b) is (-r^(-b) a, -b). */
static int ginv_(int x) {
    int a = x / K2, b = x % K2;
    int nb = (K2 - b) % K2;
    long long t = ((long long)pw[nb] * a) % GM;
    return (int)(((GM - t) % GM) * K2 + nb);
}

/* Layer l, A block i: A_i,g ~ B_j,g*s with j = lay[l][i], s = Sv[l][i]. */
static void set_dart(int l, int i) {
    int j = lay[l * K + i], s = Sv[l * K + i];
    int si = ginv_(s);
    int *nb = nbr + (long)l * N;
    for (int g = 0; g < G; g++) {
        int h = gmul_(g, s);
        nb[i * G + g] = (K + j) * G + h;
        nb[(K + j) * G + h] = i * G + gmul_(h, si);
    }
}

/* Number of unreached (block-identity, vertex) pairs. Stores final reach in rf. */
static long long unreached(void) {
    u64 *cur = rA, *alt = rB;
    for (int v = 0; v < N; v++) cur[v] = 0;
    for (int b = 0; b < 2 * K; b++) cur[(long)b * G] = 1ULL << b;
    for (int t = 0; t < D_; t++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            u64 x = cur[v];
            for (int l = 0; l < d_; l++) x |= cur[nbr[(long)l * N + v]];
            alt[v] = x;
            changed |= (x != cur[v]);
        }
        u64 *tmp = cur; cur = alt; alt = tmp;
        if (!changed) break;
    }
    long long unr = 0;
    for (int v = 0; v < N; v++) unr += 2 * K - __builtin_popcountll(cur[v]);
    memcpy(rf, cur, sizeof(u64) * (size_t)N);
    return unr;
}

/* Number of repeated (layer, j, s) keys for the same A block (wasted degree). */
static int dupcount(void) {
    int dup = 0;
    for (int i = 0; i < K; i++)
        for (int l = 1; l < d_; l++)
            for (int l2 = 0; l2 < l; l2++)
                if (lay[l * K + i] == lay[l2 * K + i] && Sv[l * K + i] == Sv[l2 * K + i]) {
                    dup++;
                    break;
                }
    return dup;
}

static void random_state(void) {
    for (int l = 0; l < d_; l++) {
        int *p = lay + l * K;
        for (int i = 0; i < K; i++) p[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int r = rint_(i + 1);
            int t = p[i]; p[i] = p[r]; p[r] = t;
        }
        for (int i = 0; i < K; i++) Sv[l * K + i] = rint_(G);
    }
    for (int l = 0; l < d_; l++)
        for (int i = 0; i < K; i++) set_dart(l, i);
}

static int search(long long iters, long long patience) {
    random_state();
    long long unr = unreached();
    int dup = dupcount();
    long long cur = unr + 1000LL * dup;
    long long c0 = cur > 1 ? cur : 1;
    long long best = cur, last = 0;

    for (long long t = 0; t < iters; t++) {
        if (unr == 0) return 1;
        if (t - last > patience) break;
        if ((t & 255) == 0 && timeup()) break;

        double frac = (double)t / (double)iters;
        double temp = 0.01 * (double)c0 * (1.0 - frac);
        if (temp < 0.5) temp = 0.5;

        int mv = rint_(100);
        if (K >= 2 && mv < 20) {
            /* Swap the B-targets of two A blocks in one layer. */
            int l = rint_(d_);
            int i1 = rint_(K), i2 = rint_(K - 1);
            if (i2 >= i1) i2++;
            int *p = lay + l * K;
            int tt = p[i1]; p[i1] = p[i2]; p[i2] = tt;
            set_dart(l, i1);
            set_dart(l, i2);
            long long nu = unreached();
            int nd = dupcount();
            long long nc = nu + 1000LL * nd;
            if (nc <= cur || rdbl() < exp(-(double)(nc - cur) / temp)) {
                cur = nc; unr = nu; dup = nd;
                if (cur < best) { best = cur; last = t; }
            } else {
                tt = p[i1]; p[i1] = p[i2]; p[i2] = tt;
                set_dart(l, i1);
                set_dart(l, i2);
            }
            continue;
        }

        int l, i;
        if (mv < 60) {
            /* Bias the move toward a vertex that is still unreached. */
            int found = -1;
            for (int k = 0; k < 8; k++) {
                int v = rint_(N);
                if (rf[v] != fullm) { found = v; break; }
            }
            if (found >= 0) {
                int blk = found / G;
                l = rint_(d_);
                if (blk < K) {
                    i = blk;
                } else {
                    int j = blk - K;
                    i = 0;
                    for (int q = 0; q < K; q++)
                        if (lay[l * K + q] == j) { i = q; break; }
                }
            } else {
                l = rint_(d_);
                i = rint_(K);
            }
        } else {
            l = rint_(d_);
            i = rint_(K);
        }

        int old = Sv[l * K + i];
        int nw = rint_(G);
        if (nw == old) continue;
        Sv[l * K + i] = nw;
        set_dart(l, i);
        long long nu = unreached();
        int nd = dupcount();
        long long nc = nu + 1000LL * nd;
        if (nc <= cur || rdbl() < exp(-(double)(nc - cur) / temp)) {
            cur = nc; unr = nu; dup = nd;
            if (cur < best) { best = cur; last = t; }
        } else {
            Sv[l * K + i] = old;
            set_dart(l, i);
        }
    }
    return unr == 0;
}

static void save_best(void) {
    int m = 0;
    for (int u = 0; u < K * G; u++) {
        for (int l = 0; l < d_; l++) {
            int v = nbr[(long)l * N + u];
            int dup = 0;
            for (int l2 = 0; l2 < l; l2++)
                if (nbr[(long)l2 * N + u] == v) { dup = 1; break; }
            if (!dup) { bestU[m] = u; bestV[m] = v; m++; }
        }
    }
    best_n = N;
    best_m = m;
}

static int sample_group(int target) {
    for (int tries = 0; tries < 200; tries++) {
        K2 = KS2[rint_(20)];
        int m = (target + K2 - 1) / K2;
        if (m < 2) m = 2;
        int r = -1;
        if (K2 == 1) {
            r = 1 % m;
        } else if (K2 == 2 && rdbl() < 0.3) {
            r = m - 1;
            if (gcd_(r, m) != 1 || powmod_(r, 2, m) != 1 % m) continue;
        } else {
            for (int t = 0; t < 60; t++) {
                int c = (m > 2) ? 2 + rint_(m - 2) : 1;
                if (gcd_(c, m) == 1 && powmod_(c, K2, m) == 1 % m) { r = c; break; }
            }
            if (r < 0) continue;
        }
        GM = m;
        pw[0] = 1 % m;
        for (int b = 1; b < K2; b++) pw[b] = (int)((long long)pw[b - 1] * r % m);
        G = m * K2;
        return 1;
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    limit_ = atof(argv[4]);
    c0_ = clock();

    if (d_ < 1 || D_ < 1) { printf("0 0\n"); return 0; }

    nbr = malloc(sizeof(int) * (size_t)d_ * CAPN);
    lay = malloc(sizeof(int) * (size_t)d_ * KMAX);
    Sv = malloc(sizeof(int) * (size_t)d_ * KMAX);
    rA = malloc(sizeof(u64) * CAPN);
    rB = malloc(sizeof(u64) * CAPN);
    rf = malloc(sizeof(u64) * CAPN);
    bestU = malloc(sizeof(int) * (size_t)d_ * (CAPN / 2 + 2));
    bestV = malloc(sizeof(int) * (size_t)d_ * (CAPN / 2 + 2));
    if (!nbr || !lay || !Sv || !rA || !rB || !rf || !bestU || !bestV) {
        printf("0 0\n");
        return 0;
    }

    long long trials[KMAX + 1], wins[KMAX + 1];
    for (int q = 0; q <= KMAX; q++) { trials[q] = 0; wins[q] = 0; }

    const int iters = 20000;
    const long long patience = 4000;

    while (!timeup()) {
        int k;
        if (rdbl() < 0.2) {
            k = 1 + rint_(KMAX);
        } else {
            double bv = -1.0;
            k = 1;
            for (int q = 1; q <= KMAX; q++) {
                double v = (wins[q] + 1.0) / (trials[q] + 2.0) + 0.05 * rdbl();
                if (v > bv) { bv = v; k = q; }
            }
        }
        K = k;
        int base = best_n / (2 * K);
        int target = base + 1 + rint_(base / 8 + 2);
        if (!sample_group(target)) continue;
        N = 2 * K * G;
        if (N <= best_n || N > CAPN) continue;
        fullm = (1ULL << (2 * K)) - 1;
        trials[K]++;
        if (search(iters, patience)) {
            wins[K]++;
            save_best();
        }
    }

    if (best_n == 0) {
        printf("0 0\n");
        return 0;
    }
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


def build(d, D, seed, time_limit):
    t0 = time.monotonic()

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}: valid fallback for D >= 2

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact construction for D = 3 when d - 1 is a prime power (calibration case).
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    # Bi-Cayley lift search in C, using most of the time budget.
    budget = 0.85 * time_limit - 3.0 - (time.monotonic() - t0)
    if budget >= 2.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                            timeout=budget + 15.0)
            n, e = lib.parse_graph_text(out)
            e = sorted({(min(u, v), max(u, v)) for u, v in e if u != v})
            consider(n, e)
        except Exception:
            pass  # keep the valid fallback

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
