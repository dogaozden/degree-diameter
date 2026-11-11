import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bi-Cayley lift over the semidirect product Z_m1 x| Z_m2.
#
# Base graph: k A-blocks and k B-blocks, with d darts per A-block. Dart j
# belongs to A-block j // d and joins it to B-block sig[j]. Each B-block must
# receive exactly d darts, which holds by construction and is kept by swapping
# targets between darts. Dart j with voltage s joins A_i x to B_t (x * s).
#
# Left multiplication by the group is an automorphism, so validity only needs
# BFS balls of radius D around the 2k block identities. The cost is the number
# of unreached vertices, plus a penalty for duplicate darts.
# Element (a, b) is coded a*m2 + b with (a,b)(c,e) = (a + r^b c, b + e).
# r = 1 gives the abelian group Z_m1 x Z_m2.
# ----------------------------------------------------------------------------

C_BLOCK = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int n) { return (int)(rnd() % (uint64_t)n); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int d_, D_, k_, m1_, m2_, G_, N_, J_;
static int *sig_, *vol_, *bslot_, *pw_, *nbr_, *queue_, *stamp_, *cntk_;
static int curstamp_ = 0;

static int gmul(int x, int y) {
    int a = x / m2_, b = x % m2_;
    int c = y / m2_, e = y % m2_;
    int a2 = (int)(((long long)a + (long long)pw_[b] * c) % m1_);
    int b2 = (b + e) % m2_;
    return a2 * m2_ + b2;
}

static void build_nbr(void) {
    for (int t = 0; t < k_; t++) cntk_[t] = 0;
    for (int j = 0; j < J_; j++) bslot_[j] = cntk_[sig_[j]]++;
    for (int j = 0; j < J_; j++) {
        int i = j / d_, l = j % d_, t = sig_[j], s = vol_[j], bs = bslot_[j];
        for (int x = 0; x < G_; x++) {
            int y = gmul(x, s);
            int a = i * G_ + x, b = (k_ + t) * G_ + y;
            nbr_[(size_t)a * d_ + l] = b;
            nbr_[(size_t)b * d_ + bs] = a;
        }
    }
}

static long long eval_cost(void) {
    long long dup = 0;
    for (int j1 = 0; j1 < J_; j1++)
        for (int j2 = j1 + 1; j2 < J_; j2++)
            if (j1 / d_ == j2 / d_ && sig_[j1] == sig_[j2] && vol_[j1] == vol_[j2]) dup++;
    build_nbr();
    long long cost = 0;
    for (int b = 0; b < 2 * k_; b++) {
        curstamp_++;
        int h = 0, t = 0;
        int src = b * G_;
        queue_[t++] = src;
        stamp_[src] = curstamp_;
        for (int dist = 0; dist < D_ && h < t; dist++) {
            int end = t;
            while (h < end) {
                int v = queue_[h++];
                const int *nv = nbr_ + (size_t)v * d_;
                for (int l = 0; l < d_; l++) {
                    int u = nv[l];
                    if (stamp_[u] != curstamp_) {
                        stamp_[u] = curstamp_;
                        queue_[t++] = u;
                    }
                }
            }
        }
        cost += N_ - t;
    }
    return cost + 20 * dup;
}

static int cmp_ll(const void *a, const void *b) {
    long long x = *(const long long *)a, y = *(const long long *)b;
    return (x > y) - (x < y);
}

int main(int argc, char **argv) {
    if (argc < 9) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double limit = atof(argv[4]);
    k_ = atoi(argv[5]);
    m1_ = atoi(argv[6]);
    m2_ = atoi(argv[7]);
    int r = atoi(argv[8]);
    if (d_ < 1 || d_ > 64 || D_ < 1 || k_ < 1 || k_ > 64 || m1_ < 1 || m2_ < 1) {
        printf("0 0\n");
        return 0;
    }
    G_ = m1_ * m2_;
    if (G_ < 2 || (long long)G_ * 2 * k_ > 200000) { printf("0 0\n"); return 0; }
    r %= m1_;
    if (r < 0) r += m1_;
    N_ = 2 * k_ * G_;
    J_ = k_ * d_;

    pw_ = malloc(sizeof(int) * (size_t)(m2_ + 1));
    pw_[0] = 1 % m1_;
    for (int b = 1; b <= m2_; b++) pw_[b] = (int)((long long)pw_[b - 1] * r % m1_);
    if (pw_[m2_] != 1 % m1_) { printf("0 0\n"); return 0; }

    sig_ = malloc(sizeof(int) * (size_t)J_);
    vol_ = malloc(sizeof(int) * (size_t)J_);
    bslot_ = malloc(sizeof(int) * (size_t)J_);
    nbr_ = malloc(sizeof(int) * (size_t)N_ * d_);
    queue_ = malloc(sizeof(int) * (size_t)N_);
    stamp_ = calloc((size_t)N_, sizeof(int));
    cntk_ = malloc(sizeof(int) * (size_t)k_);
    if (!sig_ || !vol_ || !bslot_ || !nbr_ || !queue_ || !stamp_ || !cntk_) {
        printf("0 0\n");
        return 0;
    }

    /* each B-block index t appears exactly d times in sig */
    for (int idx = 0; idx < J_; idx++) sig_[idx] = idx / d_;
    for (int i = J_ - 1; i > 0; i--) {
        int j = rint_(i + 1);
        int tmp = sig_[i]; sig_[i] = sig_[j]; sig_[j] = tmp;
    }
    for (int j = 0; j < J_; j++) vol_[j] = rint_(G_);

    long long cost = eval_cost();
    const double T0 = 8.0, T1 = 0.2;
    clock_t c0 = clock();
    while (cost > 0) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (el >= limit) break;
        double T = T0 * pow(T1 / T0, el / limit);
        if (rint_(2) == 0) {
            int j1 = rint_(J_), j2 = rint_(J_);
            if (j1 == j2 || sig_[j1] == sig_[j2]) continue;
            int tmp = sig_[j1]; sig_[j1] = sig_[j2]; sig_[j2] = tmp;
            long long nc = eval_cost();
            long long delta = nc - cost;
            if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
                cost = nc;
            } else {
                tmp = sig_[j1]; sig_[j1] = sig_[j2]; sig_[j2] = tmp;
            }
        } else {
            int j = rint_(J_);
            int old = vol_[j];
            int nv = rint_(G_);
            if (nv == old) continue;
            vol_[j] = nv;
            long long nc = eval_cost();
            long long delta = nc - cost;
            if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
                cost = nc;
            } else {
                vol_[j] = old;
            }
        }
    }

    if (cost != 0) { printf("0 0\n"); return 0; }

    long long *keys = malloc(sizeof(long long) * (size_t)J_ * G_);
    if (!keys) { printf("0 0\n"); return 0; }
    int cnt = 0;
    for (int j = 0; j < J_; j++) {
        int i = j / d_, t = sig_[j], s = vol_[j];
        for (int x = 0; x < G_; x++) {
            int y = gmul(x, s);
            long long a = (long long)i * G_ + x;
            long long b = (long long)(k_ + t) * G_ + y;
            if (a > b) { long long tt = a; a = b; b = tt; }
            keys[cnt++] = a * (long long)N_ + b;
        }
    }
    qsort(keys, (size_t)cnt, sizeof(long long), cmp_ll);
    int uniq = 0;
    for (int i = 0; i < cnt; i++)
        if (uniq == 0 || keys[i] != keys[uniq - 1]) keys[uniq++] = keys[i];
    printf("%d %d\n", N_, uniq);
    for (int i = 0; i < uniq; i++)
        printf("%lld %lld\n", keys[i] / N_, keys[i] % N_);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions and glue.
# ----------------------------------------------------------------------------

_KS = (2, 3, 4, 5, 6, 8)
_M2 = (1, 1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 16)


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo & Lopez graph for degree d = q + 2 with q a prime power >= 3, else None."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


def _pick_r(m1, m2, rng):
    """Random valid action r of Z_m2 on Z_m1 (r^m2 = 1 mod m1, gcd(r, m1) = 1); r = 1 is always valid."""
    cands = [r for r in range(1, m1) if math.gcd(r, m1) == 1 and pow(r, m2, m1) == 1 % m1]
    if not cands or rng.random() < 0.3:
        return 1
    return rng.choice(cands)


def _pick_k(rng, stats):
    """Bandit choice of base-block count k (mostly exploit, sometimes explore)."""
    if rng.random() < 0.25:
        return rng.choice(_KS)
    return max(_KS, key=lambda k: (stats[k][1] + 1) / (stats[k][0] + 2) + 0.02 * rng.random())


def _run_block(d, D, k, m1, m2, r, seconds, seed):
    """Run the C block-lift annealer; returns (n, edges) or (0, [])."""
    out = lib.run_c(C_BLOCK, [d, D, seed, f"{seconds:.2f}", k, m1, m2, r],
                    stdin_graph=None, timeout=seconds + 15.0)
    return lib.parse_graph_text(out)


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

    # Exact constructions (calibration case returns here).
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

    # Block-lift annealing over small groups Z_m1 x| Z_m2, adaptive target size.
    lift_end = t0 + 0.92 * time_limit - 1.0
    stats = {k: [0, 0] for k in _KS}  # [trials, wins]
    frac = 0.04                       # target = best * (1 + frac)
    while True:
        remaining = lift_end - time.monotonic()
        if remaining < 1.0:
            break
        k = _pick_k(rng, stats)
        target = int(best[0] * (1.0 + frac)) + 2
        g_need = -(-target // (2 * k))
        m2 = rng.choice(_M2)
        m1 = max(2, -(-g_need // m2))
        if 2 * k * m1 * m2 > 200000:
            continue
        r = _pick_r(m1, m2, rng)
        stats[k][0] += 1
        slice_s = min(remaining, max(3.0, 0.3 * remaining))
        try:
            n_, e_ = _run_block(d, D, k, m1, m2, r, slice_s, rng.randrange(1, 1 << 30))
        except (RuntimeError, ValueError):
            n_, e_ = 0, []
        if n_ > best[0] and lib.is_valid(n_, e_, d, D):
            stats[k][1] += 1
            best = (n_, e_)
            frac = min(0.2, frac * 1.3)
        else:
            frac = max(0.005, frac * 0.85)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
