import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing over bi-Cayley voltage lifts.
#
# Model: group G = Z_m x| Z_k2 (element a*k2+b, product (a,b)(c,d) = (a + r^b c, b+d)).
# Base has k vertices per side. Each of the d layers is a permutation layer_l
# from left base vertices to right base vertices, with a voltage S[l][i] in G.
# Dart (l, i) joins (L,i,g) to (R, layer_l(i), g*S[l][i]). The lift is d-regular
# and bipartite on 2*k*G vertices. Left multiplication by G is an automorphism,
# so the distance check only needs BFS from the 2k block identities. Those are
# run in parallel with one bitmask per vertex (bit b = block b).
# Cost = unreached (block, vertex) pairs + PEN * duplicate darts.
# Output: the first zero-cost lift, or "0 0".
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;
typedef uint32_t u32;

static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int n) { return (int)(rnd() % (u64)n); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int d_, D_, k_, m_, k2_, r_, G_, N_, NB_;
static int *pw_, *mulT_, *layers_, *S_, *nbr_;
static u32 *bufA_, *bufB_;
static const long long PEN_ = 100;

static int mulf(int x, int y) {
    int a = x / k2_, b = x % k2_, c = y / k2_, e = y % k2_;
    int ac = (int)(((long long)a + (long long)pw_[b] * c) % m_);
    return ac * k2_ + (b + e) % k2_;
}

static void rebuild_layer(int l) {
    for (int i = 0; i < k_; i++) {
        int j = layers_[l * k_ + i];
        int s = S_[l * k_ + i];
        for (int g = 0; g < G_; g++) {
            int a = i * G_ + g;
            int b = (k_ + j) * G_ + mulT_[(long)g * G_ + s];
            nbr_[a * d_ + l] = b;
            nbr_[b * d_ + l] = a;
        }
    }
}

static int dupes(void) {
    int dup = 0;
    for (int i = 0; i < k_; i++) {
        for (int l = 0; l < d_; l++) {
            int j = layers_[l * k_ + i], s = S_[l * k_ + i];
            for (int l2 = 0; l2 < l; l2++) {
                if (layers_[l2 * k_ + i] == j && S_[l2 * k_ + i] == s) { dup++; break; }
            }
        }
    }
    return dup;
}

static long long base_cost(void) {
    u32 *cur = bufA_, *nxt = bufB_;
    int N = N_;
    for (int v = 0; v < N; v++) cur[v] = 0;
    for (int b = 0; b < NB_; b++) cur[(long)b * G_] = 1u << b;
    for (int t = 0; t < D_; t++) {
        for (int v = 0; v < N; v++) {
            u32 x = cur[v];
            const int *nb = nbr_ + (long)v * d_;
            for (int l = 0; l < d_; l++) x |= cur[nb[l]];
            nxt[v] = x;
        }
        u32 *tmp = cur; cur = nxt; nxt = tmp;
    }
    long long s = 0;
    for (int v = 0; v < N; v++) s += __builtin_popcount(cur[v]);
    return (long long)NB_ * N - s;
}

static void emit(void) {
    int L = k_ * G_;
    printf("%d %d\n", N_, L * d_);
    for (int v = 0; v < L; v++)
        for (int l = 0; l < d_; l++)
            printf("%d %d\n", v, nbr_[v * d_ + l]);
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
    r_ = atoi(argv[8]);
    if (d_ < 1 || D_ < 1 || k_ < 1 || k_ > 16 || m_ < 1 || k2_ < 1) { printf("0 0\n"); return 0; }
    G_ = m_ * k2_;
    if (G_ > 2500) { printf("0 0\n"); return 0; }
    N_ = 2 * k_ * G_;
    NB_ = 2 * k_;

    pw_ = malloc(sizeof(int) * (size_t)k2_);
    if (!pw_) { printf("0 0\n"); return 0; }
    pw_[0] = 1 % m_;
    for (int b = 1; b < k2_; b++) pw_[b] = (int)((long long)pw_[b - 1] * r_ % m_);
    if (k2_ > 1 && (int)((long long)pw_[k2_ - 1] * r_ % m_) != 1 % m_) { printf("0 0\n"); return 0; }

    mulT_ = malloc(sizeof(int) * (size_t)G_ * G_);
    layers_ = malloc(sizeof(int) * (size_t)d_ * k_);
    S_ = malloc(sizeof(int) * (size_t)d_ * k_);
    nbr_ = malloc(sizeof(int) * (size_t)N_ * d_);
    bufA_ = malloc(sizeof(u32) * (size_t)N_);
    bufB_ = malloc(sizeof(u32) * (size_t)N_);
    if (!mulT_ || !layers_ || !S_ || !nbr_ || !bufA_ || !bufB_) { printf("0 0\n"); return 0; }

    for (int x = 0; x < G_; x++)
        for (int y = 0; y < G_; y++)
            mulT_[(long)x * G_ + y] = mulf(x, y);

    for (int l = 0; l < d_; l++) {
        for (int i = 0; i < k_; i++) layers_[l * k_ + i] = i;
        for (int i = k_ - 1; i >= 1; i--) {
            int j = rint_(i + 1);
            int t = layers_[l * k_ + i]; layers_[l * k_ + i] = layers_[l * k_ + j]; layers_[l * k_ + j] = t;
        }
    }
    for (int idx = 0; idx < d_ * k_; idx++) S_[idx] = rint_(G_);
    for (int l = 0; l < d_; l++) rebuild_layer(l);

    long long cost = base_cost() + PEN_ * dupes();
    if (cost == 0) { emit(); return 0; }

    const double T0 = 0.05 * N_, T1 = 0.001 * N_;
    clock_t c0 = clock();
    while (1) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (el >= limit) break;
        double T = T0 * pow(T1 / T0, el / limit);

        int l = rint_(d_);
        int *Lp = layers_ + l * k_;
        int *Sp = S_ + l * k_;
        int kind, i1 = 0, i2 = 0, i = 0, oldS = 0;
        if (k_ >= 2 && rdbl() < 0.3) {
            kind = 1;
            i1 = rint_(k_);
            i2 = rint_(k_ - 1);
            if (i2 >= i1) i2++;
            int t = Lp[i1]; Lp[i1] = Lp[i2]; Lp[i2] = t;
        } else {
            kind = 2;
            i = rint_(k_);
            oldS = Sp[i];
            int ns = rint_(G_);
            if (ns == oldS) continue;
            Sp[i] = ns;
        }
        rebuild_layer(l);
        long long nc = base_cost() + PEN_ * dupes();
        long long delta = nc - cost;
        if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
            cost = nc;
            if (cost == 0) { emit(); return 0; }
        } else {
            if (kind == 1) { int t = Lp[i1]; Lp[i1] = Lp[i2]; Lp[i2] = t; }
            else Sp[i] = oldS;
            rebuild_layer(l);
        }
    }
    printf("0 0\n");
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


def _group_for(target_G, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target_G (r = 1 gives the direct product)."""
    k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 8, 9, 10, 12, 16])
    m = max(2, -(-target_G // k2))
    if k2 == 1 or m <= 2:
        return m, k2, 1
    for _ in range(200):
        c = rng.randrange(2, m)
        if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
            return m, k2, c
    return m, k2, 1


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    deadline = t0 + max(2.0, time_limit - 6.0)
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

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        if D == 3 and d >= 5 and lib.is_prime_power(d - 2):
            try:
                consider(*lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass
        if D == 3 and lib.is_prime_power(d - 1):
            return best  # exact optimum (calibration case)

    # Main phase: voltage-lift annealing in C over Z_m x| Z_k2 with k base vertices per side.
    KS = (1, 2, 2, 3, 3, 4)
    step = max(4, best[0] // 8)
    while True:
        remaining = deadline - time.monotonic()
        if remaining < 2.0:
            break
        k = rng.choice(KS)
        target_n = best[0] + 2 + rng.randrange(0, step)
        while -(-target_n // (2 * k)) > 2400 and k < 16:
            k += 1
        target_G = -(-target_n // (2 * k))
        if target_G > 2400:
            break
        m, k2, r = _group_for(target_G, rng)
        slice_s = min(remaining - 1.0, 6.0 + 6.0 * rng.random())
        if slice_s < 1.0:
            break
        try:
            out = lib.run_c(C_SOURCE,
                            [d, D, rng.randrange(1, 1 << 30), f"{slice_s:.2f}", k, m, k2, r],
                            timeout=slice_s + 15.0)
            n, e = lib.parse_graph_text(out)
        except Exception:
            step = max(2, step // 2)
            continue
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
            step = max(4, best[0] // 8)
        else:
            step = max(2, step // 2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
