import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing over bi-Cayley lifts.
#
# The group is Z_m x|_r Z_k2 (element a*k2+b). The base graph has k vertices on
# each side and d "layers"; layer l is a perfect matching between the A and B
# base vertices (perm), and each dart carries a voltage in the group. The lift
# has 2*k*G vertices and is d-regular bipartite.
#
# The lift is invariant under left multiplication by the group, so the
# distance condition reduces to: for every base root (one per block), every
# lifted vertex lies within distance D. Reach sets are kept as bitmasks over
# the 2k roots, so one evaluation is D*N*d word operations. Cost = unreached
# (root, vertex) pairs + a large penalty per duplicate dart. Cost 0 gives a
# valid graph with 2*k*G vertices.
# ----------------------------------------------------------------------------

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

static int d_, D_, k_, m_, k2_, r_, G_, N_;
static u64 full_;
static long long PEN_;
static int *tab_, *inv_, *powr_, *perm_, *invp_, *volt_, *nbr_;
static u64 *cur_, *nxt_, *resv_;

static int gcd_(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }

static int gmul(int x, int y) {
    int a = x / k2_, b = x % k2_, c = y / k2_, e = y % k2_;
    int aa = (int)(((long long)a + (long long)powr_[b] * c) % m_);
    int bb = (b + e) % k2_;
    return aa * k2_ + bb;
}

static int ginv(int x) {
    int a = x / k2_, b = x % k2_;
    int nb = (k2_ - b) % k2_;
    long long t = ((long long)a * powr_[nb]) % m_;
    int c = (int)((m_ - t) % m_);
    return c * k2_ + nb;
}

static void build_nbr(void) {
    int k = k_, G = G_, d = d_;
    for (int i = 0; i < k; i++) {
        for (int g = 0; g < G; g++) {
            int v = i * G + g;
            for (int l = 0; l < d; l++) {
                int j = perm_[l * k + i];
                int s = volt_[l * k + i];
                nbr_[(size_t)v * d + l] = (k + j) * G + tab_[(size_t)g * G + s];
            }
        }
    }
    for (int j = 0; j < k; j++) {
        for (int h = 0; h < G; h++) {
            int v = (k + j) * G + h;
            for (int l = 0; l < d; l++) {
                int i = invp_[l * k + j];
                int s = volt_[l * k + i];
                nbr_[(size_t)v * d + l] = i * G + tab_[(size_t)h * G + inv_[s]];
            }
        }
    }
}

static long long evalcost(void) {
    int N = N_, G = G_, d = d_, k = k_;
    build_nbr();
    for (int v = 0; v < N; v++) cur_[v] = 0;
    for (int b = 0; b < 2 * k; b++) cur_[(size_t)b * G] |= 1ULL << b;
    u64 *a = cur_, *bb = nxt_;
    for (int t = 0; t < D_; t++) {
        for (int v = 0; v < N; v++) {
            u64 x = a[v];
            const int *nb = nbr_ + (size_t)v * d;
            for (int l = 0; l < d; l++) x |= a[nb[l]];
            bb[v] = x;
        }
        u64 *tmp = a; a = bb; bb = tmp;
    }
    resv_ = a;
    long long cost = 0;
    for (int v = 0; v < N; v++) cost += __builtin_popcountll(full_ & ~a[v]);
    long long dup = 0;
    for (int i = 0; i < k; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (perm_[l1 * k + i] == perm_[l2 * k + i] &&
                    volt_[l1 * k + i] == volt_[l2 * k + i])
                    dup++;
    return cost + dup * PEN_;
}

static void randomize(void) {
    int k = k_, d = d_, G = G_;
    for (int l = 0; l < d; l++) {
        int *p = perm_ + (size_t)l * k;
        for (int i = 0; i < k; i++) p[i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = p[i]; p[i] = p[j]; p[j] = t;
        }
        for (int i = 0; i < k; i++) invp_[l * k + p[i]] = i;
    }
    for (int x = 0; x < d * k; x++) volt_[x] = rint_(G);
}

int main(int argc, char **argv) {
    if (argc < 9) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    u64 seed = strtoull(argv[3], NULL, 10);
    double limit = atof(argv[4]);
    m_ = atoi(argv[5]);
    k2_ = atoi(argv[6]);
    r_ = atoi(argv[7]);
    k_ = atoi(argv[8]);
    rs ^= seed * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    if (d_ < 1 || D_ < 1 || m_ < 2 || k2_ < 1 || k_ < 1 || k_ > 32 || r_ < 1 || r_ >= m_) {
        printf("0 0\n"); return 0;
    }
    if ((long long)m_ * k2_ > 2400) { printf("0 0\n"); return 0; }
    if (gcd_(r_, m_) != 1) { printf("0 0\n"); return 0; }
    G_ = m_ * k2_;

    powr_ = malloc(sizeof(int) * (size_t)k2_);
    if (!powr_) { printf("0 0\n"); return 0; }
    powr_[0] = 1 % m_;
    for (int b = 1; b < k2_; b++) powr_[b] = (int)((long long)powr_[b - 1] * r_ % m_);
    if ((((long long)powr_[k2_ - 1] * r_) % m_) != (1 % m_)) { printf("0 0\n"); return 0; }

    N_ = 2 * k_ * G_;
    full_ = (2 * k_ >= 64) ? ~0ULL : ((1ULL << (2 * k_)) - 1);
    PEN_ = N_;

    tab_ = malloc(sizeof(int) * (size_t)G_ * G_);
    inv_ = malloc(sizeof(int) * (size_t)G_);
    perm_ = malloc(sizeof(int) * (size_t)d_ * k_);
    invp_ = malloc(sizeof(int) * (size_t)d_ * k_);
    volt_ = malloc(sizeof(int) * (size_t)d_ * k_);
    nbr_ = malloc(sizeof(int) * (size_t)N_ * d_);
    cur_ = malloc(sizeof(u64) * (size_t)N_);
    nxt_ = malloc(sizeof(u64) * (size_t)N_);
    if (!tab_ || !inv_ || !perm_ || !invp_ || !volt_ || !nbr_ || !cur_ || !nxt_) {
        printf("0 0\n"); return 0;
    }
    for (int x = 0; x < G_; x++)
        for (int y = 0; y < G_; y++)
            tab_[(size_t)x * G_ + y] = gmul(x, y);
    for (int x = 0; x < G_; x++) {
        inv_[x] = ginv(x);
        if (tab_[(size_t)x * G_ + inv_[x]] != 0) { printf("0 0\n"); return 0; }
    }
    resv_ = cur_;

    randomize();
    long long cost = evalcost();
    int found = (cost == 0);
    clock_t c0 = clock();
    const double T0 = 8.0, T1 = 0.2;
    const int CYC = 60000;
    int cyc = 0;
    long long iter = 0;

    while (!found) {
        if ((iter & 63) == 0) {
            double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
            if (el >= limit) break;
        }
        iter++;
        if (cyc >= CYC) {
            randomize();
            cost = evalcost();
            cyc = 0;
            if (cost == 0) found = 1;
            continue;
        }
        double frac = (double)cyc / CYC;
        double T = T0 * pow(T1 / T0, frac);
        cyc++;

        int l = rint_(d_), i = rint_(k_);

        if (k_ >= 2 && rdbl() < 0.2) {
            int i2 = rint_(k_);
            if (i2 == i) continue;
            int *p = perm_ + (size_t)l * k_;
            int ja = p[i], jb = p[i2];
            p[i] = jb; p[i2] = ja;
            invp_[l * k_ + jb] = i;
            invp_[l * k_ + ja] = i2;
            long long nc = evalcost();
            if (nc <= cost || rdbl() < exp(-(double)(nc - cost) / T)) {
                cost = nc;
                if (cost == 0) found = 1;
            } else {
                p[i] = ja; p[i2] = jb;
                invp_[l * k_ + ja] = i;
                invp_[l * k_ + jb] = i2;
            }
            continue;
        }

        if (rdbl() < 0.4) {
            int v = -1;
            for (int t = 0; t < 16; t++) {
                int x = rint_(N_);
                if (resv_[x] != full_) { v = x; break; }
            }
            if (v >= 0) {
                int block = v / G_;
                if (block < k_) {
                    i = block;
                } else {
                    int j = block - k_;
                    i = invp_[l * k_ + j];
                }
            }
        }

        int idx = l * k_ + i;
        int old = volt_[idx];
        int nw = rint_(G_);
        if (nw == old) continue;
        volt_[idx] = nw;
        long long nc = evalcost();
        if (nc <= cost || rdbl() < exp(-(double)(nc - cost) / T)) {
            cost = nc;
            if (cost == 0) found = 1;
        } else {
            volt_[idx] = old;
        }
    }

    if (!found) {
        printf("0 0\n");
        return 0;
    }
    int A = k_ * G_;
    printf("%d %lld\n", N_, (long long)A * d_);
    for (int v = 0; v < A; v++)
        for (int l = 0; l < d_; l++)
            printf("%d %d\n", v, nbr_[(size_t)v * d_ + l]);
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
    """Return (m, k2, r) for Z_m x|_r Z_k2 with m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 8, 9, 10, 12, 16])
        m = max(2, -(-target // k2))
        if k2 == 1:
            return m, 1, 1
        r = None
        for _ in range(80):
            if m <= 2 or rng.random() < 0.2:
                c = 1
            else:
                c = rng.randrange(2, m)
            if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                r = c
                break
        if r is not None:
            return m, k2, r
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

    # Bi-Cayley lift search in C. Each run targets a group order just above
    # the current best size, and the step size adapts to the outcomes.
    search_end = t0 + max(1.0, 0.85 * time_limit - 3.0)
    ks = (1, 2, 3, 4)
    trials = {k: 0 for k in ks}
    wins = {k: 0 for k in ks}
    step = 0.03
    errors = 0

    try:
        while errors < 3:
            remaining = search_end - time.monotonic()
            if remaining < 2.0:
                break
            slice_s = min(remaining, 10.0)

            if rng.random() < 0.15:
                k = rng.choice(ks)
            else:
                k = max(ks, key=lambda x: (wins[x] + 1) / (trials[x] + 2) + 0.05 * rng.random())

            need = int(best[0] * (1.0 + step * rng.uniform(0.5, 1.5))) + 2
            target_G = -(-need // (2 * k))
            if target_G > 2400:
                break
            g = _sample_group(target_G, rng)
            if g is None:
                continue
            m, k2, r = g
            if m * k2 > 2400:
                continue

            trials[k] += 1
            try:
                out = lib.run_c(
                    C_SOURCE,
                    [d, D, rng.randrange(1, 1 << 30), f"{slice_s:.2f}", m, k2, r, k],
                    timeout=slice_s + 10.0,
                )
                n, e = lib.parse_graph_text(out)
            except Exception:
                errors += 1
                continue

            before = best[0]
            consider(n, e)
            if best[0] > before:
                wins[k] += 1
                step = min(0.1, step * 1.25)
            else:
                step = max(0.002, step * 0.92)
    except Exception:
        pass  # keep the valid fallback

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
