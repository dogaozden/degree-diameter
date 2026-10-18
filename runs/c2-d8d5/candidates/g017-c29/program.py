import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# C engine: bi-Cayley voltage lift annealer over Z_m x| Z_k2.
#
# The graph is a lift of a base with k blocks per side over the group
# G = Z_m x| Z_k2 (element a*k2+b, product (a,b)(c,e) = (a + r^b c, b+e)).
# Layer l (0..d-1) joins A-block i to B-block layers[l][i] with voltage S[l][i]:
# A(i,g) ~ B(j, g*s). Left multiplication is an automorphism that is transitive
# on each block, so validity only needs the 2k base vertices to reach every
# vertex within D. Reachability is tracked as a 2k-bit mask per vertex, which
# makes each cost evaluation O(N*d*D). Cost = unreached (base, vertex) pairs
# plus a penalty for duplicate edges. Zero cost means a valid simple lift.
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

static int d_, D_, m_, k2_, r_, k_, G_, N_;
static int *pw, *ginvT, *layers, *invl, *S, *nbr;
static u64 *bufA, *bufB, *cur;
static const long long PEN = 500;

static int gcd_i(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }

static int gmul(int x, int y) {
    int a = x / k2_, b = x % k2_;
    int c = y / k2_, e = y % k2_;
    int aa = (int)(((long long)a + (long long)pw[b] * c) % m_);
    int bb = (b + e) % k2_;
    return aa * k2_ + bb;
}

static int ginv_calc(int x) {
    int a = x / k2_, b = x % k2_;
    int nb = (k2_ - b) % k2_;
    long long t = ((long long)pw[nb] * a) % m_;
    int na = (int)((m_ - t) % m_);
    return na * k2_ + nb;
}

static void build_nbr(void) {
    const int k = k_, G = G_, d = d_;
    for (int l = 0; l < d; l++)
        for (int i = 0; i < k; i++)
            invl[l * k + layers[l * k + i]] = i;
    for (int i = 0; i < k; i++)
        for (int g = 0; g < G; g++) {
            int v = i * G + g;
            for (int l = 0; l < d; l++) {
                int j = layers[l * k + i];
                int s = S[l * k + i];
                nbr[(size_t)v * d + l] = (k + j) * G + gmul(g, s);
            }
        }
    for (int j = 0; j < k; j++)
        for (int h = 0; h < G; h++) {
            int v = (k + j) * G + h;
            for (int l = 0; l < d; l++) {
                int i = invl[l * k + j];
                int s = S[l * k + i];
                nbr[(size_t)v * d + l] = i * G + gmul(h, ginvT[s]);
            }
        }
}

static int dupcount(void) {
    int c = 0;
    const int k = k_, d = d_;
    for (int i = 0; i < k; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (layers[l1 * k + i] == layers[l2 * k + i] &&
                    S[l1 * k + i] == S[l2 * k + i])
                    c++;
    return c;
}

static long long eval_cost(void) {
    const int N = N_, d = d_, k = k_;
    build_nbr();
    u64 *a = bufA, *b = bufB;
    for (int v = 0; v < N; v++) a[v] = 0;
    for (int bl = 0; bl < 2 * k; bl++) a[(size_t)bl * G_] = 1ULL << bl;
    for (int it = 0; it < D_; it++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            u64 x = a[v];
            const int *nb = nbr + (size_t)v * d;
            for (int l = 0; l < d; l++) x |= a[nb[l]];
            b[v] = x;
            if (x != a[v]) changed = 1;
        }
        u64 *t = a; a = b; b = t;
        if (!changed) break;
    }
    cur = a;
    long long un = 0;
    for (int v = 0; v < N; v++) un += 2 * k - __builtin_popcountll(a[v]);
    return un + PEN * (long long)dupcount();
}

int main(int argc, char **argv) {
    if (argc < 9) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    m_ = atoi(argv[3]);
    k2_ = atoi(argv[4]);
    r_ = atoi(argv[5]);
    k_ = atoi(argv[6]);
    rs ^= (u64)strtoull(argv[7], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double limit = atof(argv[8]);

    if (d_ < 1 || D_ < 1 || m_ < 2 || k2_ < 1 || k_ < 1 || 2 * k_ > 64 ||
        r_ < 1 || r_ >= m_ || gcd_i(r_, m_) != 1) {
        printf("0 0\n");
        return 0;
    }
    pw = malloc(sizeof(int) * (size_t)k2_);
    if (!pw) { printf("0 0\n"); return 0; }
    pw[0] = 1 % m_;
    for (int b = 1; b < k2_; b++) pw[b] = (int)((long long)pw[b - 1] * r_ % m_);
    if (((long long)pw[k2_ - 1] * r_) % m_ != 1 % m_) { printf("0 0\n"); return 0; }

    G_ = m_ * k2_;
    long long Nll = 2LL * k_ * G_;
    if (Nll > 300000LL || (double)Nll * d_ > 4e6) { printf("0 0\n"); return 0; }
    N_ = (int)Nll;

    ginvT = malloc(sizeof(int) * (size_t)G_);
    layers = malloc(sizeof(int) * (size_t)d_ * k_);
    invl = malloc(sizeof(int) * (size_t)d_ * k_);
    S = malloc(sizeof(int) * (size_t)d_ * k_);
    nbr = malloc(sizeof(int) * (size_t)N_ * d_);
    bufA = malloc(sizeof(u64) * (size_t)N_);
    bufB = malloc(sizeof(u64) * (size_t)N_);
    if (!ginvT || !layers || !invl || !S || !nbr || !bufA || !bufB) {
        printf("0 0\n");
        return 0;
    }
    for (int s = 0; s < G_; s++) ginvT[s] = ginv_calc(s);

    for (int l = 0; l < d_; l++) {
        for (int i = 0; i < k_; i++) layers[l * k_ + i] = i;
        for (int i = k_ - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = layers[l * k_ + i];
            layers[l * k_ + i] = layers[l * k_ + j];
            layers[l * k_ + j] = t;
        }
        for (int i = 0; i < k_; i++) S[l * k_ + i] = rint_(G_);
    }

    long long cost = eval_cost();
    double T0 = 0.02 * (double)cost;
    if (T0 < 2.0) T0 = 2.0;
    const double T1 = 0.3;
    clock_t c0 = clock();

    while (cost > 0) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (el >= limit) break;
        double T = T0 * pow(T1 / T0, el / limit);
        double x = rdbl();
        if (k_ >= 2 && x < 0.2) {
            int l = rint_(d_);
            int i1 = rint_(k_);
            int i2 = rint_(k_ - 1);
            if (i2 >= i1) i2++;
            int *L = layers + l * k_;
            int t = L[i1]; L[i1] = L[i2]; L[i2] = t;
            long long nc = eval_cost();
            long long delta = nc - cost;
            if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
                cost = nc;
            } else {
                t = L[i1]; L[i1] = L[i2]; L[i2] = t;
            }
        } else {
            int l = rint_(d_);
            int i = rint_(k_);
            if (rint_(2) == 0) {
                for (int tries = 0; tries < 40; tries++) {
                    int v = rint_(N_);
                    if (__builtin_popcountll(cur[v]) < 2 * k_) {
                        int bl = v / G_;
                        if (bl < k_) {
                            i = bl;
                        } else {
                            int j = bl - k_;
                            for (int t2 = 0; t2 < k_; t2++)
                                if (layers[l * k_ + t2] == j) { i = t2; break; }
                        }
                        break;
                    }
                }
            }
            int idx = l * k_ + i;
            int old = S[idx];
            int nw = rint_(G_);
            if (nw == old) continue;
            S[idx] = nw;
            long long nc = eval_cost();
            long long delta = nc - cost;
            if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
                cost = nc;
            } else {
                S[idx] = old;
            }
        }
    }

    if (cost != 0) {
        printf("0 0\n");
        return 0;
    }
    build_nbr();
    int d = d_;
    long long M = (long long)k_ * G_ * d_;
    printf("%d %lld\n", N_, M);
    for (int v = 0; v < k_ * G_; v++)
        for (int l = 0; l < d; l++)
            printf("%d %d\n", v, nbr[(size_t)v * d + l]);
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


_K_CHOICES = (1, 2, 3, 4, 6)
_K2_CHOICES = (1, 1, 2, 2, 2, 3, 4, 4, 5, 6, 8, 9, 10, 12)


def _sample_group(target, rng):
    """Return (m, k2, r) with Z_m x| Z_k2 of order m*k2 >= target, or None."""
    for _ in range(60):
        k2 = rng.choice(_K2_CHOICES)
        m = max(2, -(-target // k2)) + rng.randrange(0, 3)
        valid_r = [r for r in range(1, m)
                   if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
        if valid_r:
            return m, k2, rng.choice(valid_r)
    return None


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

    # Exact constructions. The D = 3 calibration case returns immediately.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best
        if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(*lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass

    # Voltage-lift search in C, climbing over group orders.
    lift_end = t0 + max(0.5, min(time_limit - 8.0, 0.85 * time_limit))
    span = max(0.5, lift_end - time.monotonic())
    per_trial = max(1.5, min(5.0, span / 8.0))

    trials = {k: 0 for k in _K_CHOICES}
    wins = {k: 0 for k in _K_CHOICES}

    def pick_k():
        if rng.random() < 0.25:
            return rng.choice(_K_CHOICES)
        return max(_K_CHOICES,
                   key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.05 * rng.random())

    fails = 0
    while fails < 4:
        remaining = lift_end - time.monotonic()
        if remaining < 0.8:
            break
        k = pick_k()
        base = best[0] // (2 * k)
        target = base + 1 + rng.randrange(0, base // 24 + 2)
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        if 2 * k * m * k2 <= best[0]:
            continue
        budget = min(remaining, per_trial)
        trials[k] += 1
        try:
            out = lib.run_c(C_SOURCE,
                            [d, D, m, k2, r, k, rng.randrange(1, 1 << 30), f"{budget:.2f}"],
                            timeout=budget + 3.0)
            n, e = lib.parse_graph_text(out)
        except Exception:
            fails += 1
            continue
        if n > best[0] and lib.is_valid(n, e, d, D):
            wins[k] += 1
            best = (n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
