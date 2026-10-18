import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing over bi-Cayley lifts of Z_m x| Z_k2.
#
# The graph is a lift of a base with k vertices per side. Every base vertex has
# one dart per layer l: side-0 base i is joined to side-1 base sigma_l(i) with
# group voltage vol_l(i), so the lift is d-regular. Left multiplication by any
# group element is an automorphism that is transitive on each block of G
# vertices, so diameter only needs bitmask propagation from the 2k base
# identities. Each source carries one bit in a 64-bit mask per vertex. The cost
# is G times the number of unreached (source, vertex) pairs, plus a penalty for
# parallel darts. Cost zero means a valid graph, which is printed at once.
# ----------------------------------------------------------------------------

C_LIFT = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

#define MAXD 32
#define MAXK 32
#define MAXPW 64

static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int n) { return (int)(rnd() % (u64)n); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int d_, D_, m_, k2_, k_, G_, N_;
static long long PEN_;
static int pw_[MAXPW];
static int sig_[MAXD][MAXK], sinv_[MAXD][MAXK], vol_[MAXD][MAXK], ivol_[MAXD][MAXK];
static int *nbr;
static u64 *bufA, *bufB;

static int gmul(int x, int y) {
    int a1 = x / k2_, b1 = x % k2_;
    int a2 = y / k2_, b2 = y % k2_;
    int a = (int)(((long long)a1 + (long long)pw_[b1] * a2) % m_);
    int b = (b1 + b2) % k2_;
    return a * k2_ + b;
}

static int ginv(int x) {
    int a = x / k2_, b = x % k2_;
    int e = (k2_ - b) % k2_;
    int c = (int)((m_ - ((long long)pw_[e] * a) % m_) % m_);
    return c * k2_ + e;
}

static void fix_sinv(int l) {
    for (int i = 0; i < k_; i++) sinv_[l][sig_[l][i]] = i;
}

static void build_nbr(void) {
    int d = d_, k = k_, G = G_;
    for (int l = 0; l < d; l++)
        for (int i = 0; i < k; i++) ivol_[l][i] = ginv(vol_[l][i]);
    for (int i = 0; i < k; i++)
        for (int x = 0; x < G; x++) {
            int v = i * G + x;
            int *nb = nbr + (size_t)v * d;
            for (int l = 0; l < d; l++)
                nb[l] = (k + sig_[l][i]) * G + gmul(x, vol_[l][i]);
        }
    for (int j = 0; j < k; j++)
        for (int y = 0; y < G; y++) {
            int v = (k + j) * G + y;
            int *nb = nbr + (size_t)v * d;
            for (int l = 0; l < d; l++) {
                int i = sinv_[l][j];
                nb[l] = i * G + gmul(y, ivol_[l][i]);
            }
        }
}

static long long eval_cost(void) {
    int d = d_, k = k_, G = G_, N = N_, B = 2 * k_;
    build_nbr();
    long long dup = 0;
    for (int i = 0; i < k; i++)
        for (int l = 0; l < d; l++)
            for (int l2 = l + 1; l2 < d; l2++)
                if (sig_[l][i] == sig_[l2][i] && vol_[l][i] == vol_[l2][i]) dup++;
    u64 *cur = bufA, *nxt = bufB;
    for (int v = 0; v < N; v++) cur[v] = 0;
    for (int b = 0; b < B; b++) cur[(size_t)b * G] |= 1ULL << b;
    for (int it = 0; it < D_; it++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            u64 x = cur[v];
            const int *nb = nbr + (size_t)v * d;
            for (int l = 0; l < d; l++) x |= cur[nb[l]];
            nxt[v] = x;
            if (x != cur[v]) changed = 1;
        }
        u64 *t = cur; cur = nxt; nxt = t;
        if (!changed) break;
    }
    long long bad = 0;
    for (int b = 0; b < B; b++) {
        long long cnt = 0;
        for (int v = 0; v < N; v++) cnt += (long long)((cur[v] >> b) & 1ULL);
        bad += (long long)N - cnt;
    }
    return bad * (long long)G + PEN_ * dup;
}

int main(int argc, char **argv) {
    if (argc < 9) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    m_ = atoi(argv[3]);
    k2_ = atoi(argv[4]);
    int r = atoi(argv[5]);
    k_ = atoi(argv[6]);
    rs ^= (u64)strtoull(argv[7], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double limit = atof(argv[8]);
    if (d_ < 1 || d_ > MAXD || D_ < 1 || m_ < 2 || k2_ < 1 || k2_ > MAXPW - 1 ||
        k_ < 1 || k_ > MAXK) {
        printf("0 0\n");
        return 0;
    }
    r %= m_;
    if (r < 0) r += m_;
    pw_[0] = 1 % m_;
    for (int t = 1; t < k2_; t++) pw_[t] = (int)((long long)pw_[t - 1] * r % m_);
    if ((long long)pw_[k2_ - 1] * r % m_ != 1 % m_) { printf("0 0\n"); return 0; }

    G_ = m_ * k2_;
    N_ = 2 * k_ * G_;
    if (N_ > 4000000) { printf("0 0\n"); return 0; }
    nbr = malloc(sizeof(int) * (size_t)N_ * d_);
    bufA = malloc(sizeof(u64) * (size_t)N_);
    bufB = malloc(sizeof(u64) * (size_t)N_);
    if (!nbr || !bufA || !bufB) { printf("0 0\n"); return 0; }
    PEN_ = 20LL * G_;

    for (int l = 0; l < d_; l++) {
        for (int i = 0; i < k_; i++) sig_[l][i] = i;
        for (int i = k_ - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = sig_[l][i]; sig_[l][i] = sig_[l][j]; sig_[l][j] = t;
        }
        fix_sinv(l);
        for (int i = 0; i < k_; i++) vol_[l][i] = rint_(G_);
    }

    long long cost = eval_cost();
    const double T0 = 1.5 * G_, T1 = 0.1 * G_;
    double frac = 0.0;
    clock_t c0 = clock();
    unsigned long long iter = 0;
    while (cost > 0) {
        if ((iter & 15ULL) == 0) {
            double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
            if (el >= limit) break;
            frac = el / limit;
        }
        iter++;
        double T = T0 * pow(T1 / T0, frac);
        int l = rint_(d_);
        int i = rint_(k_);
        int swapped = 0, i2 = 0, oldv = 0;
        if (k_ >= 2 && rdbl() < 0.3) {
            swapped = 1;
            i2 = rint_(k_ - 1);
            if (i2 >= i) i2++;
            int t = sig_[l][i]; sig_[l][i] = sig_[l][i2]; sig_[l][i2] = t;
            fix_sinv(l);
        } else {
            oldv = vol_[l][i];
            int nv = rint_(G_);
            if (nv == oldv) continue;
            vol_[l][i] = nv;
        }
        long long nc = eval_cost();
        long long delta = nc - cost;
        if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
            cost = nc;
        } else if (swapped) {
            int t = sig_[l][i]; sig_[l][i] = sig_[l][i2]; sig_[l][i2] = t;
            fix_sinv(l);
        } else {
            vol_[l][i] = oldv;
        }
    }

    if (cost != 0) { printf("0 0\n"); return 0; }
    int nh = k_ * G_;
    printf("%d %d\n", N_, nh * d_);
    for (int v = 0; v < nh; v++)
        for (int l = 0; l < d_; l++)
            printf("%d %d\n", v, nbr[(size_t)v * d_ + l]);
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


def _run_lift(d, D, m, k2, r, k, seed, seconds):
    """Anneal one lift configuration in C; returns (n, edges), with n = 0 on failure."""
    out = lib.run_c(C_LIFT, [d, D, m, k2, r, k, seed, f"{seconds:.2f}"],
                    timeout=seconds + 20.0)
    return lib.parse_graph_text(out)


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    end = t0 + max(1.0, 0.85 * time_limit - 1.0)
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

    if D == 2:
        return best  # K_{d,d} is optimal for diameter 2

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best
        if D == 3 and d >= 5 and lib.is_prime_power(d - 2):
            try:
                n, e = lib.araujo_lopez_graph(d - 2)
                consider(n, e)
            except (ValueError, RuntimeError):
                pass

    # Lift annealing ladder: each success raises the target order.
    KS = (1, 2, 3, 4)
    trials = {k: 0 for k in KS}
    wins = {k: 0 for k in KS}

    def pick_k():
        if rng.random() < 0.25:
            return rng.choice(KS)
        return max(KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.05 * rng.random())

    while True:
        remaining = end - time.monotonic()
        if remaining < 1.5:
            break
        k = pick_k()
        nb = best[0]
        step = max(2, nb // 60)
        target_n = nb + step + rng.randrange(0, max(1, step))
        Gt = max(2, -(-target_n // (2 * k)))
        g = _sample_group(Gt, rng)
        if g is None:
            continue
        m, k2, r = g
        if 2 * k * m * k2 <= nb:
            continue
        slice_s = min(remaining - 0.5, max(2.0, 0.12 * time_limit))
        trials[k] += 1
        try:
            n, e = _run_lift(d, D, m, k2, r, k, rng.randrange(1, 1 << 30), slice_s)
        except Exception:
            break  # C engine unavailable: keep the valid fallback
        if n > 0:
            wins[k] += 1
            consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
