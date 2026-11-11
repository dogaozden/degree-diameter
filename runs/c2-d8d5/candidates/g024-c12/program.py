import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bi-Cayley lift annealer over Z_m x| Z_k2.
#
# Base: k vertices A_0..A_{k-1} and k vertices B_0..B_{k-1}. Each of the d layers
# is a permutation perm[l] of {0..k-1} plus voltages volt[l][i] in G. Layer l
# joins A_i,x to B_{perm[l][i]}, x*volt[l][i] for every group element x. Left
# multiplication by G is an automorphism that acts regularly on each block, so
# the graph has diameter <= D iff every block-root (b, identity) reaches all N
# vertices within D steps. The cost is the total number of unreached vertices
# over the 2k roots, and a plain BFS per root is enough.
# ----------------------------------------------------------------------------

LIFT_C = r"""
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

static int d_, D_, k_, m_, k2_, G_, N_;
static int *pw, *perm, *volt, *nbr, *stampv, *queue_;
static int stamp_ = 0;

static int mulg(int x, int y) {
    int a = x / k2_, b = x % k2_, c = y / k2_, e = y % k2_;
    int a2 = (int)(((long long)a + (long long)pw[b] * c) % m_);
    return a2 * k2_ + (b + e) % k2_;
}

static int invg(int x) {
    int a = x / k2_, b = x % k2_;
    int nb = (k2_ - b) % k2_;
    int a2 = (int)((m_ - ((long long)pw[nb] * a) % m_) % m_);
    return a2 * k2_ + nb;
}

static void set_layer(int l) {
    int d = d_, k = k_, G = G_;
    for (int i = 0; i < k; i++) {
        int p = perm[l * k + i], s = volt[l * k + i], si = invg(s);
        for (int x = 0; x < G; x++) {
            int A = i * G + x;
            int B = (k + p) * G + x;
            nbr[A * d + l] = (k + p) * G + mulg(x, s);
            nbr[B * d + l] = i * G + mulg(x, si);
        }
    }
}

static int unreached(int src) {
    int head = 0, tail = 0;
    stamp_++;
    queue_[tail++] = src;
    stampv[src] = stamp_;
    for (int lvl = 0; lvl < D_ && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = queue_[head++];
            const int *row = nbr + (size_t)v * d_;
            for (int l = 0; l < d_; l++) {
                int u = row[l];
                if (stampv[u] != stamp_) { stampv[u] = stamp_; queue_[tail++] = u; }
            }
        }
    }
    return N_ - tail;
}

static long long total_cost(void) {
    long long c = 0;
    for (int b = 0; b < 2 * k_; b++) c += unreached(b * G_);
    return c;
}

int main(int argc, char **argv) {
    if (argc < 9) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double limit = atof(argv[4]);
    k_ = atoi(argv[5]);
    m_ = atoi(argv[6]);
    k2_ = atoi(argv[7]);
    int r = atoi(argv[8]);
    if (d_ < 1 || D_ < 1 || k_ < 1 || m_ < 1 || k2_ < 1) { printf("0 0\n"); return 0; }
    G_ = m_ * k2_;
    N_ = 2 * k_ * G_;
    if (G_ > 200000 || N_ > 400000) { printf("0 0\n"); return 0; }

    pw = malloc(sizeof(int) * (size_t)k2_);
    pw[0] = 1 % m_;
    for (int t = 1; t < k2_; t++) pw[t] = (int)((long long)pw[t - 1] * r % m_);

    perm = malloc(sizeof(int) * (size_t)d_ * k_);
    volt = malloc(sizeof(int) * (size_t)d_ * k_);
    nbr = malloc(sizeof(int) * (size_t)N_ * d_);
    stampv = calloc((size_t)N_, sizeof(int));
    queue_ = malloc(sizeof(int) * (size_t)N_);
    int *sp = malloc(sizeof(int) * (size_t)k_);
    int *sv = malloc(sizeof(int) * (size_t)k_);
    if (!pw || !perm || !volt || !nbr || !stampv || !queue_ || !sp || !sv) {
        printf("0 0\n");
        return 0;
    }

    for (int l = 0; l < d_; l++) {
        for (int i = 0; i < k_; i++) perm[l * k_ + i] = i;
        for (int i = k_ - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = perm[l * k_ + i];
            perm[l * k_ + i] = perm[l * k_ + j];
            perm[l * k_ + j] = t;
        }
        for (int i = 0; i < k_; i++) volt[l * k_ + i] = rint_(G_);
        set_layer(l);
    }

    long long cost = total_cost();
    long long c0 = cost > 0 ? cost : 1;
    double T0 = fmax(1.0, 0.05 * (double)c0), T1 = 0.3;
    double T = T0, el = 0.0;
    clock_t cst = clock();
    long long iter = 0;

    while (cost > 0) {
        if ((iter & 15) == 0) {
            el = (double)(clock() - cst) / CLOCKS_PER_SEC;
            if (el >= limit) break;
            T = T0 * pow(T1 / T0, el / limit);
        }
        iter++;
        int l = rint_(d_);
        memcpy(sp, perm + l * k_, sizeof(int) * (size_t)k_);
        memcpy(sv, volt + l * k_, sizeof(int) * (size_t)k_);
        if (k_ == 1 || rdbl() < 0.5) {
            int i = rint_(k_);
            volt[l * k_ + i] = rint_(G_);
        } else {
            int i1 = rint_(k_), i2 = rint_(k_ - 1);
            if (i2 >= i1) i2++;
            int t = perm[l * k_ + i1];
            perm[l * k_ + i1] = perm[l * k_ + i2];
            perm[l * k_ + i2] = t;
        }
        set_layer(l);
        long long nc = total_cost();
        long long delta = nc - cost;
        if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
            cost = nc;
        } else {
            memcpy(perm + l * k_, sp, sizeof(int) * (size_t)k_);
            memcpy(volt + l * k_, sv, sizeof(int) * (size_t)k_);
            set_layer(l);
        }
    }

    if (cost != 0) { printf("0 0\n"); return 0; }
    int kG = k_ * G_;
    printf("%d %d\n", N_, kG * d_);
    for (int v = 0; v < kG; v++)
        for (int l = 0; l < d_; l++)
            printf("%d %d\n", v, nbr[v * d_ + l]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python glue and constructions.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _sample_group(target, rng):
    """Return (m, k2, r) describing Z_m x| Z_k2 with m*k2 >= target."""
    k2 = rng.choice((1, 1, 2, 2, 3, 4, 5, 6, 8, 10, 12, 16, 20, 24))
    m = max(2, -(-target // k2))
    r = 1
    if k2 == 2 and rng.random() < 0.5:
        r = m - 1
    elif k2 > 2 and rng.random() < 0.7:
        for _ in range(200):
            c = rng.randrange(2, m) if m > 2 else 1
            if c > 1 and math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                r = c
                break
    return m, k2, r


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    rng = random.Random(seed)

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

    # Bi-Cayley lift search in C. Each successful run raises the bar, so the
    # next attempt targets a larger group order.
    reserve = max(4.0, 0.08 * time_limit)
    lift_end = t0 + time_limit - reserve
    ks = (1, 2, 3, 4, 6)
    while True:
        remaining = lift_end - time.monotonic()
        if remaining < 1.5:
            break
        k = rng.choice(ks)
        g_min = best[0] // (2 * k) + 1
        target = g_min + rng.randrange(0, max(1, g_min // 30) + 1)
        m, k2, r = _sample_group(target, rng)
        if 2 * k * m * k2 <= best[0]:
            continue
        budget = min(remaining, rng.choice((5.0, 8.0, 12.0)))
        try:
            out = lib.run_c(LIFT_C,
                            [d, D, rng.randrange(1, 1 << 30), f"{budget:.2f}", k, m, k2, r],
                            timeout=budget + 20.0)
            n, e = lib.parse_graph_text(out)
            if n > 0 and e:
                consider(n, sorted({(min(u, v), max(u, v)) for u, v in e}))
        except Exception:
            pass  # keep the valid fallback

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
