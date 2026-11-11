import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: focused bi-Cayley lift annealer over Z_m x| Z_k2.
#
# Vertices: A_i x and B_t x for i, t in [0, k), x in G (index i*G+x, (k+t)*G+x).
# Layer l gives perm[l][i] = t and voltage vol[l][i] = s, joining
#     A_i x ~ B_t (x * s).
# Left multiplication by G is an automorphism, so only the 2k block
# representatives need BFS checks. Cost = unreached pairs over those balls
# plus a penalty for repeated darts. The Python side re-validates every result.
#
# Differences from the previous engine:
#  - per-block unreached counts guide moves: with probability 0.7 the move
#    touches a dart incident to a block that still has unreached vertices;
#  - sawtooth temperature (several reheats per run) instead of one decay;
#  - a rejected move restores the stored per-block counts.
# ----------------------------------------------------------------------------

C_LIFT = r"""
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

static int d_, D_, k_, m_, k2_, G_, N_;
static int *perm, *vol, *nbr, *pw, *queue_, *stamp, *ucnt, *usave;
static int curstamp = 0;

static int gmul(int x, int y) {
    int a = x / k2_, b = x % k2_;
    int c = y / k2_, e = y % k2_;
    int a2 = (a + (pw[b] * c) % m_) % m_;
    int b2 = (b + e) % k2_;
    return a2 * k2_ + b2;
}

static void set_dart(int l, int i) {
    int k = k_, G = G_, d = d_;
    int t = perm[l * k + i], s = vol[l * k + i];
    for (int x = 0; x < G; x++) {
        int y = gmul(x, s);
        int a = i * G + x, b = (k + t) * G + y;
        nbr[a * d + l] = b;
        nbr[b * d + l] = a;
    }
}

static void set_all_darts(void) {
    for (int l = 0; l < d_; l++)
        for (int i = 0; i < k_; i++) set_dart(l, i);
}

static long long eval_cost(void) {
    int k = k_, d = d_, D = D_, N = N_, G = G_;
    long long dups = 0;
    for (int i = 0; i < k; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (perm[l1 * k + i] == perm[l2 * k + i] && vol[l1 * k + i] == vol[l2 * k + i])
                    dups++;
    long long cost = 0;
    for (int b = 0; b < 2 * k; b++) {
        if (curstamp > 2000000000) {
            memset(stamp, 0, sizeof(int) * (size_t)N);
            curstamp = 0;
        }
        curstamp++;
        int src = b * G;
        int h = 0, t = 0;
        queue_[t++] = src;
        stamp[src] = curstamp;
        int dist = 0;
        while (h < t && dist < D) {
            int end = t;
            while (h < end) {
                int v = queue_[h++];
                const int *nv = nbr + (size_t)v * d;
                for (int l = 0; l < d; l++) {
                    int u = nv[l];
                    if (stamp[u] != curstamp) {
                        stamp[u] = curstamp;
                        queue_[t++] = u;
                    }
                }
            }
            dist++;
        }
        ucnt[b] = N - t;
        cost += N - t;
    }
    return cost + 50 * dups;
}

/* Uniform random block among those with unreached vertices, or -1. */
static int pick_focus_block(void) {
    int tot = 0, pick = -1;
    for (int b = 0; b < 2 * k_; b++) {
        if (ucnt[b] > 0) {
            tot++;
            if (rint_(tot) == 0) pick = b;
        }
    }
    return pick;
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
    m_ = atoi(argv[6]);
    k2_ = atoi(argv[7]);
    int r = atoi(argv[8]);
    if (d_ < 1 || d_ > 64 || D_ < 1 || k_ < 1 || m_ < 2 || k2_ < 1) { printf("0 0\n"); return 0; }
    r %= m_;
    if (r < 0) r += m_;
    G_ = m_ * k2_;
    if ((long long)G_ * 2 * k_ > 200000) { printf("0 0\n"); return 0; }
    N_ = 2 * k_ * G_;

    pw = malloc(sizeof(int) * (size_t)(k2_ + 1));
    pw[0] = 1 % m_;
    for (int b = 1; b <= k2_; b++) pw[b] = (int)((long long)pw[b - 1] * r % m_);
    if (pw[k2_] != 1 % m_) { printf("0 0\n"); return 0; }

    perm = malloc(sizeof(int) * (size_t)d_ * k_);
    vol = malloc(sizeof(int) * (size_t)d_ * k_);
    nbr = malloc(sizeof(int) * (size_t)N_ * d_);
    queue_ = malloc(sizeof(int) * (size_t)N_);
    stamp = calloc((size_t)N_, sizeof(int));
    ucnt = calloc((size_t)2 * k_, sizeof(int));
    usave = calloc((size_t)2 * k_, sizeof(int));
    if (!perm || !vol || !nbr || !queue_ || !stamp || !ucnt || !usave) { printf("0 0\n"); return 0; }

    for (int l = 0; l < d_; l++) {
        for (int i = 0; i < k_; i++) perm[l * k_ + i] = i;
        for (int i = k_ - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = perm[l * k_ + i];
            perm[l * k_ + i] = perm[l * k_ + j];
            perm[l * k_ + j] = t;
        }
        for (int i = 0; i < k_; i++) vol[l * k_ + i] = rint_(G_);
    }

    set_all_darts();
    long long cost = eval_cost();
    const double T0 = 5.0, T1 = 0.2;
    const int cycles = 4;
    clock_t c0 = clock();
    while (cost > 0) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (el >= limit) break;
        double ph = fmod((el / limit) * cycles, 1.0);
        double T = T0 * pow(T1 / T0, ph);

        int l = rint_(d_);
        int i = -1;
        int blk = (rint_(10) < 7) ? pick_focus_block() : -1;
        if (blk >= 0) {
            if (blk < k_) {
                i = blk;
            } else {
                int tt = blk - k_;
                for (int j = 0; j < k_; j++)
                    if (perm[l * k_ + j] == tt) { i = j; break; }
                if (i < 0) continue;
            }
        } else {
            i = rint_(k_);
        }

        memcpy(usave, ucnt, sizeof(int) * (size_t)(2 * k_));
        if (k_ >= 2 && rint_(2) == 0) {
            int i2 = rint_(k_ - 1);
            if (i2 >= i) i2++;
            int *p1 = &perm[l * k_ + i], *p2 = &perm[l * k_ + i2];
            int tmp = *p1; *p1 = *p2; *p2 = tmp;
            set_dart(l, i);
            set_dart(l, i2);
            long long nc = eval_cost();
            long long delta = nc - cost;
            if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
                cost = nc;
            } else {
                tmp = *p1; *p1 = *p2; *p2 = tmp;
                set_dart(l, i);
                set_dart(l, i2);
                memcpy(ucnt, usave, sizeof(int) * (size_t)(2 * k_));
            }
        } else {
            int idx = l * k_ + i;
            int old = vol[idx];
            int nv = rint_(G_);
            if (nv == old) continue;
            vol[idx] = nv;
            set_dart(l, i);
            long long nc = eval_cost();
            long long delta = nc - cost;
            if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
                cost = nc;
            } else {
                vol[idx] = old;
                set_dart(l, i);
                memcpy(ucnt, usave, sizeof(int) * (size_t)(2 * k_));
            }
        }
    }

    if (cost != 0) { printf("0 0\n"); return 0; }

    long long *pairs = malloc(sizeof(long long) * (size_t)N_ * d_);
    if (!pairs) { printf("0 0\n"); return 0; }
    int cnt = 0;
    for (int v = 0; v < N_; v++)
        for (int l = 0; l < d_; l++) {
            int u = nbr[v * d_ + l];
            if (u > v) pairs[cnt++] = (long long)v * N_ + u;
        }
    qsort(pairs, (size_t)cnt, sizeof(long long), cmp_ll);
    int uniq = 0;
    for (int i = 0; i < cnt; i++)
        if (i == 0 || pairs[i] != pairs[i - 1]) pairs[uniq++] = pairs[i];
    printf("%d %d\n", N_, uniq);
    for (int i = 0; i < uniq; i++)
        printf("%lld %lld\n", pairs[i] / N_, pairs[i] % N_);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions and glue.
# ----------------------------------------------------------------------------

_KS = (1, 2, 3, 4, 5, 6, 8)


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, -(-target // k2))
        if k2 == 1:
            r = 1
        elif k2 == 2 and rng.random() < 0.3:
            r = m - 1
            if math.gcd(r, m) != 1 or pow(r, 2, m) != 1 % m:
                continue
        else:
            r = None
            for _ in range(60):
                c = rng.randrange(2, m) if m > 2 else 1
                if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                    r = c
                    break
            if r is None:
                continue
        return m, k2, r
    return None


def _pick_k(rng, stats):
    """Bandit choice of base-block count k (mostly exploit, sometimes explore)."""
    if rng.random() < 0.25:
        return rng.choice(_KS)
    return max(_KS, key=lambda k: (stats[k][1] + 1) / (stats[k][0] + 2) + 0.02 * rng.random())


def _lift_in_c(d, D, k, m, k2, r, seconds, seed):
    """Run the C lift annealer for one group; returns (n, edges) or (0, [])."""
    out = lib.run_c(C_LIFT, [d, D, seed, f"{seconds:.2f}", k, m, k2, r],
                    stdin_graph=None, timeout=seconds + 5.0)
    return lib.parse_graph_text(out)


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget_end = t0 + max(1.0, 0.85 * time_limit - 2.0)
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

    # Focused lift annealing over groups, with an adaptive target size.
    stats = {k: [0, 0] for k in _KS}   # [trials, wins]
    frac = 0.08                         # target = best * (1 + frac)
    while True:
        remaining = budget_end - time.monotonic()
        if remaining < 1.5:
            break
        k = _pick_k(rng, stats)
        target_n = int(best[0] * (1.0 + frac)) + 2
        g = _sample_group(max(2, -(-target_n // (2 * k))), rng)
        if g is None:
            continue
        m, k2, r = g
        if 2 * k * m * k2 <= best[0]:
            continue
        stats[k][0] += 1
        slice_s = min(remaining - 0.5, 10.0)
        try:
            n_, e_ = _lift_in_c(d, D, k, m, k2, r, slice_s, rng.randrange(1, 1 << 30))
        except Exception:
            n_, e_ = 0, []
        if n_ > best[0] and lib.is_valid(n_, e_, d, D):
            stats[k][1] += 1
            best = (n_, e_)
            frac = min(0.25, frac * 1.3)
        else:
            frac = max(0.003, frac * 0.85)

    if not lib.is_valid(best[0], best[1], d, D):
        return lib.haar_graph(d, range(d))
    return best
