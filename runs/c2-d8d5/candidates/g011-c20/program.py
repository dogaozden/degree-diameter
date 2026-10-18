import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: annealing over bi-Cayley lifts (voltage graphs over groups).
#
# Base graph: K blocks on side A and K blocks on side B, with d layers. Layer l
# is a bijection sigma_l from A-blocks to B-blocks, and each A-block i carries a
# voltage s_l(i) in G = Z_m x| Z_k2. Lifted vertices are (block, g). The vertex
# (i, x) on side A joins (sigma_l(i), x*s) on side B, so the graph is d-regular
# and bipartite.
#
# Left multiplication by G is an automorphism group that acts transitively on
# each block. So the diameter is at most D exactly when the 2K block
# representatives (b*G, the identity of each block) reach every vertex within
# D steps. The cost is the sum of unreached counts over those 2K representatives,
# plus a penalty for parallel darts. Moves change a voltage or swap two entries of
# a layer permutation. The run stops as soon as the cost reaches zero.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#define _POSIX_C_SOURCE 199309L
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
static double now_s(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int d_, D_, K_, M_, K2_, G_, N_;
static int *pw, *sig, *sv, *nbr, *dist, *queue_;
static long long PEN;

static int gcd_(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a < 0 ? -a : a;
}

/* Element a*K2+b of Z_M x| Z_K2 with (a,b)*(c,e) = (a + r^b c, b + e). */
static int gmul(int x, int y) {
    int a = x / K2_, b = x % K2_;
    int c = y / K2_, e = y % K2_;
    int aa = (int)(((long long)a + (long long)pw[b] * c) % M_);
    int bb = (b + e) % K2_;
    return aa * K2_ + bb;
}

static void build_nbr(void) {
    for (int l = 0; l < d_; l++) {
        for (int i = 0; i < K_; i++) {
            int j = sig[l * K_ + i];
            int s = sv[l * K_ + i];
            for (int x = 0; x < G_; x++) {
                int a = i * G_ + x;
                int b = (K_ + j) * G_ + gmul(x, s);
                nbr[a * d_ + l] = b;
                nbr[b * d_ + l] = a;
            }
        }
    }
}

static int bfs_count(int src) {
    int h = 0, t = 0, cnt = 1;
    for (int v = 0; v < N_; v++) dist[v] = -1;
    dist[src] = 0;
    queue_[t++] = src;
    while (h < t) {
        int v = queue_[h++];
        if (dist[v] >= D_) continue;
        for (int l = 0; l < d_; l++) {
            int u = nbr[v * d_ + l];
            if (dist[u] < 0) { dist[u] = dist[v] + 1; queue_[t++] = u; cnt++; }
        }
    }
    return cnt;
}

static long long evalc(void) {
    build_nbr();
    long long bad = 0;
    for (int b = 0; b < 2 * K_; b++) bad += (long long)(N_ - bfs_count(b * G_));
    long long dup = 0;
    for (int i = 0; i < K_; i++)
        for (int l = 0; l < d_; l++)
            for (int l2 = l + 1; l2 < d_; l2++)
                if (sig[l * K_ + i] == sig[l2 * K_ + i] && sv[l * K_ + i] == sv[l2 * K_ + i]) dup++;
    return bad + PEN * dup;
}

static void output_graph(void) {
    int half = N_ / 2;
    printf("%d %d\n", N_, half * d_);
    for (int a = 0; a < half; a++)
        for (int l = 0; l < d_; l++)
            printf("%d %d\n", a, nbr[a * d_ + l]);
}

static void shuffle_perm(int *p, int n) {
    for (int i = 0; i < n; i++) p[i] = i;
    for (int i = n - 1; i > 0; i--) {
        int j = rint_(i + 1);
        int t = p[i]; p[i] = p[j]; p[j] = t;
    }
}

int main(int argc, char **argv) {
    if (argc < 9) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double limit = atof(argv[4]);
    K_ = atoi(argv[5]);
    M_ = atoi(argv[6]);
    K2_ = atoi(argv[7]);
    int r = atoi(argv[8]);
    if (d_ < 1 || D_ < 1 || K_ < 1 || M_ < 1 || K2_ < 1) { printf("0 0\n"); return 0; }
    long long Gll = (long long)M_ * K2_;
    long long Nll = 2LL * K_ * Gll;
    if (Gll > 100000 || Nll > 20000 || Nll < 2) { printf("0 0\n"); return 0; }
    G_ = (int)Gll;
    N_ = (int)Nll;
    int rr = ((r % M_) + M_) % M_;
    if (gcd_(rr, M_) != 1) { printf("0 0\n"); return 0; }
    pw = malloc(sizeof(int) * (size_t)K2_);
    if (!pw) { printf("0 0\n"); return 0; }
    pw[0] = 1 % M_;
    for (int b = 1; b < K2_; b++) pw[b] = (int)(((long long)pw[b - 1] * rr) % M_);
    if ((((long long)pw[K2_ - 1] * rr) % M_) != (1 % M_)) { printf("0 0\n"); return 0; }

    sig = malloc(sizeof(int) * (size_t)d_ * K_);
    sv = malloc(sizeof(int) * (size_t)d_ * K_);
    nbr = malloc(sizeof(int) * (size_t)N_ * d_);
    dist = malloc(sizeof(int) * (size_t)N_);
    queue_ = malloc(sizeof(int) * (size_t)N_);
    if (!sig || !sv || !nbr || !dist || !queue_) { printf("0 0\n"); return 0; }
    PEN = 4LL * N_ + 100;

    double T0 = 0.02 * N_ + 5.0, T1 = 0.3;
    double runLen = limit / 3.0;
    if (runLen < 1.0) runLen = 1.0;
    double tstart = now_s();

    while (1) {
        for (int l = 0; l < d_; l++) shuffle_perm(&sig[l * K_], K_);
        for (int t = 0; t < d_ * K_; t++) sv[t] = rint_(G_);
        long long cost = evalc();
        if (cost == 0) { output_graph(); return 0; }
        double rst = now_s();

        while (1) {
            double tn = now_s();
            if (tn - tstart >= limit) { printf("0 0\n"); return 0; }
            double frac = (tn - rst) / runLen;
            if (frac >= 1.0) break;
            double T = T0 * pow(T1 / T0, frac);

            int undo_type = 0, ua = 0, ub = 0, ul = 0, uold = 0;
            if (K_ >= 2 && rdbl() < 0.2) {
                int l = rint_(d_);
                int i1 = rint_(K_);
                int i2 = rint_(K_ - 1);
                if (i2 >= i1) i2++;
                int *p = &sig[l * K_];
                int tmp = p[i1]; p[i1] = p[i2]; p[i2] = tmp;
                undo_type = 1; ul = l; ua = i1; ub = i2;
            } else {
                int idx = rint_(d_ * K_);
                int nw = rint_(G_);
                if (nw == sv[idx]) continue;
                undo_type = 2; ua = idx; uold = sv[idx];
                sv[idx] = nw;
            }

            long long nc = evalc();
            if (nc <= cost || rdbl() < exp(-(double)(nc - cost) / T)) {
                cost = nc;
                if (cost == 0) { output_graph(); return 0; }
            } else {
                if (undo_type == 1) {
                    int *p = &sig[ul * K_];
                    int tmp = p[ua]; p[ua] = p[ub]; p[ub] = tmp;
                } else {
                    sv[ua] = uold;
                }
            }
        }
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions and glue.
# ----------------------------------------------------------------------------

_MAX_N = 8000


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _sample_group(target_g, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 of order at least target_g, or None."""
    for _ in range(300):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 8, 10, 12])
        m = max(2, -(-target_g // k2))
        if k2 == 1:
            return m, 1, 1
        for _ in range(60):
            c = rng.randrange(1, m)
            if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                return m, k2, c
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 2:
        return best

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best  # exact optimum for the calibration case

    # Main search: bi-Cayley lifts over semidirect products, found by the C annealer.
    deadline = t0 + max(1.0, 0.82 * time_limit - 1.0)
    slice_cap = min(8.0, max(2.0, 0.1 * time_limit))
    step = 0.03

    while True:
        remain = deadline - time.monotonic()
        if remain < 2.0:
            break
        slice_s = min(remain - 1.0, slice_cap)

        k = rng.choice([1, 1, 2, 2, 3, 3, 4, 5, 6])
        n_best = best[0]
        extra = max(2, int(n_best * step * rng.uniform(0.5, 1.0)))
        target_n = n_best + extra
        g = _sample_group(-(-target_n // (2 * k)), rng)
        if g is None:
            continue
        m, k2, r = g
        n_try = 2 * k * m * k2
        if n_try <= n_best or n_try > _MAX_N:
            continue

        seed_c = rng.randrange(1, 1 << 30)
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed_c, f"{slice_s:.2f}", k, m, k2, r],
                            timeout=slice_s + 20.0)
            n_new, e_new = lib.parse_graph_text(out)
        except Exception:
            continue

        if n_new > best[0] and lib.is_valid(n_new, e_new, d, D):
            best = (n_new, e_new)
            step = min(0.08, step * 1.5)
        else:
            step = max(0.002, step * 0.85)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
