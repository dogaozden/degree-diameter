import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine 1 (new): bi-Cayley annealer over G = Z_m x| Z_k2 (single base block).
# Vertices A_x = x and B_y = n + y for x, y in G, with n = |G|.
# Edges: A_x ~ B_{x*s} for s in S, |S| = d. Left multiplication by G is an
# automorphism, so validity only needs BFS from A_e and B_e to reach all 2n
# vertices within D steps. Cost = total unreached over those two BFS balls.
# ----------------------------------------------------------------------------

C_CAYLEY = r"""
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

static int d_, D_, n_, m_, k2_;
static int *mt, *invt, *S, *Sinv, *stamp_, *queue_;
static char *inS;
static int curstamp = 0;

static int bfs_count(int src) {
    curstamp++;
    int h = 0, t = 0, dist = 0;
    queue_[t++] = src;
    stamp_[src] = curstamp;
    while (h < t && dist < D_) {
        int end = t;
        while (h < end) {
            int v = queue_[h++];
            if (v < n_) {
                const int *row = mt + (size_t)v * n_;
                for (int j = 0; j < d_; j++) {
                    int u = n_ + row[S[j]];
                    if (stamp_[u] != curstamp) { stamp_[u] = curstamp; queue_[t++] = u; }
                }
            } else {
                const int *row = mt + (size_t)(v - n_) * n_;
                for (int j = 0; j < d_; j++) {
                    int u = row[Sinv[j]];
                    if (stamp_[u] != curstamp) { stamp_[u] = curstamp; queue_[t++] = u; }
                }
            }
        }
        dist++;
    }
    return t;
}

static long long eval_cost(void) {
    long long vis = (long long)bfs_count(0) + (long long)bfs_count(n_);
    return 4LL * n_ - vis;
}

static void write_graph(void) {
    printf("%d %d\n", 2 * n_, n_ * d_);
    for (int x = 0; x < n_; x++)
        for (int j = 0; j < d_; j++)
            printf("%d %d\n", x, n_ + mt[(size_t)x * n_ + S[j]]);
}

int main(int argc, char **argv) {
    if (argc < 8) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double limit = atof(argv[4]);
    m_ = atoi(argv[5]);
    k2_ = atoi(argv[6]);
    int r = atoi(argv[7]);
    if (d_ < 1 || D_ < 1 || m_ < 1 || k2_ < 1) { printf("0 0\n"); return 0; }
    n_ = m_ * k2_;
    if (n_ < d_ || n_ > 3000) { printf("0 0\n"); return 0; }
    r %= m_;
    if (r < 0) r += m_;

    int *pw = malloc(sizeof(int) * (size_t)(k2_ + 1));
    pw[0] = 1 % m_;
    for (int b = 1; b <= k2_; b++) pw[b] = (int)((long long)pw[b - 1] * r % m_);
    if (pw[k2_] != 1 % m_) { printf("0 0\n"); return 0; }

    mt = malloc(sizeof(int) * (size_t)n_ * (size_t)n_);
    if (!mt) { printf("0 0\n"); return 0; }
    for (int x = 0; x < n_; x++) {
        int a = x / k2_, b = x % k2_;
        for (int y = 0; y < n_; y++) {
            int c = y / k2_, e = y % k2_;
            int a2 = (int)((a + (long long)pw[b] * c) % m_);
            int b2 = (b + e) % k2_;
            mt[(size_t)x * n_ + y] = a2 * k2_ + b2;
        }
    }
    invt = malloc(sizeof(int) * (size_t)n_);
    for (int x = 0; x < n_; x++) {
        invt[x] = -1;
        for (int y = 0; y < n_; y++)
            if (mt[(size_t)x * n_ + y] == 0) { invt[x] = y; break; }
        if (invt[x] < 0) { printf("0 0\n"); return 0; }
    }

    S = malloc(sizeof(int) * (size_t)d_);
    Sinv = malloc(sizeof(int) * (size_t)d_);
    inS = calloc((size_t)n_, 1);
    stamp_ = calloc((size_t)2 * n_, sizeof(int));
    queue_ = malloc(sizeof(int) * (size_t)2 * n_);
    if (!S || !Sinv || !inS || !stamp_ || !queue_) { printf("0 0\n"); return 0; }

    clock_t c0 = clock();
    const double T0 = 3.0, T1 = 0.15;
    const long long CHUNK = 300000;

    while (1) {
        memset(inS, 0, (size_t)n_);
        for (int j = 0; j < d_; j++) {
            int t;
            do { t = rint_(n_); } while (inS[t]);
            inS[t] = 1;
            S[j] = t;
            Sinv[j] = invt[t];
        }
        long long cost = eval_cost();
        for (long long it = 0; it < CHUNK && cost > 0; it++) {
            if ((it & 63) == 0) {
                if ((double)(clock() - c0) / CLOCKS_PER_SEC >= limit) goto out;
            }
            double frac = (double)it / (double)CHUNK;
            double T = T0 * pow(T1 / T0, frac);
            int j = rint_(d_), t = rint_(n_);
            if (inS[t]) continue;
            int old = S[j];
            inS[old] = 0; inS[t] = 1;
            S[j] = t; Sinv[j] = invt[t];
            long long nc = eval_cost();
            long long delta = nc - cost;
            if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
                cost = nc;
            } else {
                inS[t] = 0; inS[old] = 1;
                S[j] = old; Sinv[j] = invt[old];
            }
        }
        if (cost == 0) { write_graph(); return 0; }
    }
out:
    printf("0 0\n");
    return 0;
}
"""


# ----------------------------------------------------------------------------
# C engine 2 (parent's voltage-lift annealer, kept as a fallback phase).
# Vertices: A_i x and B_t x for i, t in [0, k), x in G = Z_m x| Z_k2.
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
static int *perm, *vol, *nbr, *pw, *queue_, *stamp;
static int curstamp = 0;

static int gmul(int x, int y) {
    int a = x / k2_, b = x % k2_;
    int c = y / k2_, e = y % k2_;
    int a2 = (a + (pw[b] * c) % m_) % m_;
    int b2 = (b + e) % k2_;
    return a2 * k2_ + b2;
}

static void build_nbr(void) {
    int k = k_, G = G_, d = d_;
    for (int l = 0; l < d; l++)
        for (int i = 0; i < k; i++) {
            int t = perm[l * k + i], s = vol[l * k + i];
            for (int x = 0; x < G; x++) {
                int y = gmul(x, s);
                int a = i * G + x, b = (k + t) * G + y;
                nbr[a * d + l] = b;
                nbr[b * d + l] = a;
            }
        }
}

static long long eval_cost(void) {
    int k = k_, d = d_, G = G_, N = N_;
    long long dups = 0;
    for (int i = 0; i < k; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (perm[l1 * k + i] == perm[l2 * k + i] && vol[l1 * k + i] == vol[l2 * k + i])
                    dups++;
    build_nbr();
    long long cost = 0;
    for (int b = 0; b < 2 * k; b++) {
        int src = b * G;
        curstamp++;
        int h = 0, t = 0;
        queue_[t++] = src;
        stamp[src] = curstamp;
        int dist = 0;
        while (h < t && dist < D_) {
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
        cost += N - t;
    }
    return cost + 50 * dups;
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
    if (!perm || !vol || !nbr || !queue_ || !stamp) { printf("0 0\n"); return 0; }

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

    long long cost = eval_cost();
    const double T0 = 6.0, T1 = 0.15;
    clock_t c0 = clock();
    while (cost > 0) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (el >= limit) break;
        double T = T0 * pow(T1 / T0, el / limit);
        int l = rint_(d_), i = rint_(k_);
        if (k_ >= 2 && rint_(3) == 0) {
            int i2 = rint_(k_ - 1);
            if (i2 >= i) i2++;
            int *p1 = &perm[l * k_ + i], *p2 = &perm[l * k_ + i2];
            int t = *p1; *p1 = *p2; *p2 = t;
            long long nc = eval_cost();
            long long delta = nc - cost;
            if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
                cost = nc;
            } else {
                t = *p1; *p1 = *p2; *p2 = t;
            }
        } else {
            int old = vol[l * k_ + i];
            int nv = rint_(G_);
            if (nv == old) continue;
            vol[l * k_ + i] = nv;
            long long nc = eval_cost();
            long long delta = nc - cost;
            if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
                cost = nc;
            } else {
                vol[l * k_ + i] = old;
            }
        }
    }

    if (cost != 0) { printf("0 0\n"); return 0; }

    long long *pairs = malloc(sizeof(long long) * (size_t)N_ * d_);
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

_KS = (1, 2, 3, 4, 5)
_CAP_HALF = 2600  # max group order for the Cayley engine (table is n*n ints)


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _sample_cayley_group(n, rng):
    """Return (m, k2, r) for a group Z_m x| Z_k2 of order exactly n (m >= 2)."""
    divs = [k for k in range(1, n + 1) if n % k == 0 and n // k >= 2]
    small = [k for k in divs if k <= 40]
    k2 = 1 if (rng.random() < 0.3 or not small) else rng.choice(small)
    m = n // k2
    r = 1
    if k2 > 1 and m > 2 and rng.random() < 0.75:
        for _ in range(80):
            c = rng.randrange(2, m)
            if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                r = c
                break
    return m, k2, r


def _cayley_in_c(d, D, m, k2, r, seconds, seed):
    """Run the bi-Cayley annealer on G = Z_m x| Z_k2; returns (n, edges) or (0, [])."""
    out = lib.run_c(C_CAYLEY, [d, D, seed, f"{seconds:.2f}", m, k2, r],
                    stdin_graph=None, timeout=seconds + 10.0)
    return lib.parse_graph_text(out)


def _sample_lift_group(target, rng):
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
    if rng.random() < 0.2:
        return rng.choice(_KS)
    return max(_KS, key=lambda k: (stats[k][1] + 1) / (stats[k][0] + 2) + 0.02 * rng.random())


def _lift_in_c(d, D, k, m, k2, r, seconds, seed):
    """Run the C voltage-lift annealer for one group; returns (n, edges) or (0, [])."""
    out = lib.run_c(C_LIFT, [d, D, seed, f"{seconds:.2f}", k, m, k2, r],
                    stdin_graph=None, timeout=seconds + 10.0)
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

    # Exact construction for D = 3 when d-1 is a prime power (calibration case).
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    end = t0 + max(1.0, 0.9 * time_limit - 1.0)
    a_end = t0 + 0.6 * (end - t0)

    # Phase A: bi-Cayley single-block search over groups of growing order.
    moore_half = max(d, lib.moore_bound(d, D) // 2)
    cap_half = min(_CAP_HALF, moore_half)
    frac = 0.03
    while True:
        remaining = a_end - time.monotonic()
        if remaining < 1.0:
            break
        lo = best[0] // 2
        if lo >= cap_half:
            break
        n_try = min(cap_half, max(lo + 1, int(lo * (1.0 + frac)) + 1))
        m, k2, r = _sample_cayley_group(n_try, rng)
        slice_s = min(8.0, max(1.5, remaining / 3.0), remaining)
        if slice_s < 0.5:
            break
        try:
            n_, e_ = _cayley_in_c(d, D, m, k2, r, slice_s, rng.randrange(1, 1 << 30))
        except RuntimeError:
            n_, e_ = 0, []
        if n_ > best[0] and lib.is_valid(n_, e_, d, D):
            best = (n_, e_)
            frac = min(0.15, frac * 1.5)
        else:
            frac = max(0.002, frac * 0.7)

    # Phase B: voltage-lift annealing over non-cyclic groups for the rest of the budget.
    stats = {k: [0, 0] for k in _KS}
    frac = 0.05
    while True:
        remaining = end - time.monotonic()
        if remaining < 1.0:
            break
        k = _pick_k(rng, stats)
        target_n = int(best[0] * (1.0 + frac)) + 2
        g = _sample_lift_group(max(2, -(-target_n // (2 * k))), rng)
        if g is None:
            continue
        m, k2, r = g
        if 2 * k * m * k2 <= best[0]:
            continue
        stats[k][0] += 1
        slice_s = min(4.0, max(1.0, 0.25 * remaining), remaining)
        try:
            n_, e_ = _lift_in_c(d, D, k, m, k2, r, slice_s, rng.randrange(1, 1 << 30))
        except RuntimeError:
            n_, e_ = 0, []
        if n_ > best[0] and lib.is_valid(n_, e_, d, D):
            stats[k][1] += 1
            best = (n_, e_)
            frac = min(0.25, frac * 1.3)
        else:
            frac = max(0.003, frac * 0.85)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
