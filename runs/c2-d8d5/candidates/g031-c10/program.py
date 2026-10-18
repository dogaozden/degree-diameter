import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: exact annealer over bi-Cayley lifts with group Z_m x| Z_k2.
#
# Base graph: K blocks per side. Layer l (0..d-1) has a permutation perm[l][i]
# (A-block i -> B-block perm[l][i]) and a voltage vol[l][i] in the group G.
# A-vertex (i,x) is joined to B-vertex (perm[l][i], x*vol[l][i]) for each layer l.
#
# Left multiplication by any group element is an automorphism, so the graph is
# vertex-transitive within each block. Validity therefore only needs BFS from
# the identity of each of the 2K blocks: cost = total unreached vertices over
# those 2K sources, plus a penalty for duplicate edges. Cost 0 means valid.
# Moves: change one voltage, or swap two targets within one layer.
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

static int d_, D_, K_, M_, K2_, G_, N_;
static int *perm_, *vol_, *nbr_, *pw_, *mark_, *queue_;
static int stamp_ = 0;
static const long long PEN = 40;

static int gmul(int x, int y) {
    int a = x / K2_, b = x % K2_;
    int c = y / K2_, e = y % K2_;
    int na = (int)(((long long)a + (long long)pw_[b] * c) % M_);
    int nb = (b + e) % K2_;
    return na * K2_ + nb;
}

static void build_nbr(void) {
    for (int i = 0; i < K_; i++) {
        for (int x = 0; x < G_; x++) {
            int u = i * G_ + x;
            for (int l = 0; l < d_; l++) {
                int j = perm_[l * K_ + i];
                int s = vol_[l * K_ + i];
                int w = (K_ + j) * G_ + gmul(x, s);
                nbr_[(size_t)u * d_ + l] = w;
                nbr_[(size_t)w * d_ + l] = u;
            }
        }
    }
}

static long long count_dups(void) {
    long long c = 0;
    for (int i = 0; i < K_; i++)
        for (int l = 0; l < d_; l++)
            for (int l2 = l + 1; l2 < d_; l2++)
                if (perm_[l * K_ + i] == perm_[l2 * K_ + i] &&
                    vol_[l * K_ + i] == vol_[l2 * K_ + i])
                    c++;
    return c;
}

static long long eval_cost(void) {
    build_nbr();
    long long unreached = 0;
    for (int b = 0; b < 2 * K_; b++) {
        int src = b * G_;
        stamp_++;
        int h = 0, t = 0;
        queue_[t++] = src;
        mark_[src] = stamp_;
        for (int depth = 0; depth < D_ && h < t; depth++) {
            int end = t;
            while (h < end) {
                int v = queue_[h++];
                const int *nb = nbr_ + (size_t)v * d_;
                for (int l = 0; l < d_; l++) {
                    int u = nb[l];
                    if (mark_[u] != stamp_) {
                        mark_[u] = stamp_;
                        queue_[t++] = u;
                    }
                }
            }
        }
        unreached += (long long)(N_ - t);
    }
    return unreached + PEN * count_dups();
}

int main(int argc, char **argv) {
    if (argc < 9) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    K_ = atoi(argv[3]);
    M_ = atoi(argv[4]);
    K2_ = atoi(argv[5]);
    int R = atoi(argv[6]);
    rs ^= (u64)strtoull(argv[7], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double limit = atof(argv[8]);
    if (d_ < 1 || D_ < 1 || K_ < 1 || M_ < 2 || K2_ < 1 || R < 0 || R >= M_) {
        printf("0 0\n");
        return 0;
    }
    G_ = M_ * K2_;
    if ((long long)2 * K_ * G_ > 400000LL) { printf("0 0\n"); return 0; }
    N_ = 2 * K_ * G_;

    perm_ = malloc(sizeof(int) * (size_t)d_ * K_);
    vol_ = malloc(sizeof(int) * (size_t)d_ * K_);
    nbr_ = malloc(sizeof(int) * (size_t)N_ * d_);
    pw_ = malloc(sizeof(int) * K2_);
    mark_ = calloc((size_t)N_, sizeof(int));
    queue_ = malloc(sizeof(int) * (size_t)N_);
    int *tmp = malloc(sizeof(int) * K_);
    if (!perm_ || !vol_ || !nbr_ || !pw_ || !mark_ || !queue_ || !tmp) {
        printf("0 0\n");
        return 0;
    }

    pw_[0] = 1 % M_;
    for (int b = 1; b < K2_; b++) pw_[b] = (int)((long long)pw_[b - 1] * R % M_);

    for (int l = 0; l < d_; l++) {
        for (int i = 0; i < K_; i++) tmp[i] = i;
        for (int i = K_ - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = tmp[i]; tmp[i] = tmp[j]; tmp[j] = t;
        }
        for (int i = 0; i < K_; i++) perm_[l * K_ + i] = tmp[i];
    }
    for (int i = 0; i < d_ * K_; i++) vol_[i] = rint_(G_);
    free(tmp);

    long long cost = eval_cost();
    int found = (cost == 0);
    const double T0 = 3.0, T1 = 0.05;
    clock_t c0 = clock();

    while (!found) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (el >= limit) break;
        double T = T0 * pow(T1 / T0, el / limit);
        int l = rint_(d_);
        if (K_ >= 2 && rdbl() < 0.3) {
            int i1 = rint_(K_);
            int i2 = rint_(K_ - 1);
            if (i2 >= i1) i2++;
            int *p1 = &perm_[l * K_ + i1];
            int *p2 = &perm_[l * K_ + i2];
            int sw = *p1; *p1 = *p2; *p2 = sw;
            long long nc = eval_cost();
            if (nc <= cost || rdbl() < exp(-(double)(nc - cost) / T)) {
                cost = nc;
            } else {
                int *q1 = &perm_[l * K_ + i1];
                int *q2 = &perm_[l * K_ + i2];
                int sw2 = *q1; *q1 = *q2; *q2 = sw2;
            }
        } else {
            int idx = l * K_ + rint_(K_);
            int old = vol_[idx];
            int nv = rint_(G_);
            if (nv == old) continue;
            vol_[idx] = nv;
            long long nc = eval_cost();
            if (nc <= cost || rdbl() < exp(-(double)(nc - cost) / T)) {
                cost = nc;
            } else {
                vol_[idx] = old;
            }
        }
        if (cost == 0) found = 1;
    }

    if (!found) {
        printf("0 0\n");
        return 0;
    }
    build_nbr();
    int A = K_ * G_;
    printf("%d %d\n", N_, A * d_);
    for (int u = 0; u < A; u++)
        for (int l = 0; l < d_; l++)
            printf("%d %d\n", u, nbr_[(size_t)u * d_ + l]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python glue.
# ----------------------------------------------------------------------------

_LIFT_KS = (1, 2, 3, 4, 6)
_K2S = (1, 1, 1, 2, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24)


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _sample_group(G_target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= G_target, or None."""
    for _ in range(50):
        k2 = rng.choice(_K2S)
        m = max(2, -(-G_target // k2))
        if k2 == 1:
            r = 1
        else:
            cands = [c for c in range(1, m)
                     if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        return m, k2, r
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}: valid fallback for D >= 2

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 2:
        return best

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if lib.is_prime_power(d - 1):
                return best
        if d >= 5 and lib.is_prime_power(d - 2):
            try:
                consider(*lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass

    budget = min(0.88 * time_limit - 2.0, time_limit - 3.0)
    end = t0 + budget

    # Main search: exact bi-Cayley lift annealing in C, one group per call.
    # Each success raises the target order, so the search climbs step by step.
    while True:
        remaining = end - time.monotonic()
        if remaining < 1.0:
            break
        K = rng.choice(_LIFT_KS)
        G_target = best[0] // (2 * K) + 1 + rng.randrange(0, 3)
        g = _sample_group(G_target, rng)
        if g is None:
            continue
        m, k2, r = g
        seconds = min(remaining, 3.0 + 2.0 * rng.random())
        try:
            out = lib.run_c(LIFT_C,
                            [d, D, K, m, k2, r, rng.randrange(1, 1 << 30), f"{seconds:.2f}"],
                            timeout=seconds + 15.0)
            n2, e2 = lib.parse_graph_text(out)
        except Exception:
            break  # keep the valid fallback
        if n2 > 0:
            consider(n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
