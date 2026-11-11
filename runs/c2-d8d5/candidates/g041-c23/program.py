import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bi-Cayley lift search over the semidirect product Z_m x| Z_k2.
#
# The base graph has k vertices on each side (blocks A_0..A_{k-1}, B_0..B_{k-1}).
# Each of the d layers is a perfect matching of blocks (a permutation) with a
# group element (voltage) per block. Vertex (block, g) is adjacent to
# (block', g*s), so the lift is d-regular and bipartite.
#
# Left multiplication by any group element is an automorphism that fixes each
# block. Hence the distance from (i, g) to (j, h) equals the distance from
# (i, 1) to (j, g^-1 h), and the whole graph has diameter <= D iff the BFS ball
# of each of the 2k source vertices (i, 1) covers every vertex within D steps.
# That makes the cost evaluation 2k BFS runs instead of N bitset expansions.
#
# Cost = total unreached (source, vertex) pairs + PEN * duplicate darts.
# Moves: change one voltage, or swap two block targets within a layer.
# The first zero-cost lift is printed and the program exits.
# ----------------------------------------------------------------------------

C_LIFT = r"""
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

#define PEN 1000LL

static int d_, D_, k_, G_, N_, m_, k2_, r_;
static int *mulT, *invT, *lay, *vol, *nbr, *dist, *que;

static void build_group(void) {
    G_ = m_ * k2_;
    int *pw = malloc(sizeof(int) * (size_t)k2_);
    pw[0] = 1 % m_;
    for (int t = 1; t < k2_; t++) pw[t] = (int)(((long long)pw[t - 1] * r_) % m_);
    mulT = malloc(sizeof(int) * (size_t)G_ * (size_t)G_);
    invT = malloc(sizeof(int) * (size_t)G_);
    for (int x = 0; x < G_; x++) {
        int a = x / k2_, b = x % k2_;
        for (int y = 0; y < G_; y++) {
            int c = y / k2_, e = y % k2_;
            long long aa = (a + (long long)pw[b] * c) % m_;
            mulT[(size_t)x * G_ + y] = (int)(aa * k2_ + (b + e) % k2_);
        }
    }
    for (int x = 0; x < G_; x++) invT[x] = -1;
    for (int x = 0; x < G_; x++)
        for (int y = 0; y < G_; y++)
            if (mulT[(size_t)x * G_ + y] == 0) invT[x] = y;
    free(pw);
}

/* Block i (A side) dart l goes to block k+j with voltage s: (i,g) ~ (k+j, g*s). */
static void build_nbr(void) {
    const int k = k_, G = G_, d = d_;
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < k; i++) {
            const int j = lay[l * k + i];
            const int s = vol[l * k + i];
            const int si = invT[s];
            for (int g = 0; g < G; g++) {
                int u = i * G + g;
                int v = (k + j) * G + mulT[(size_t)g * G + s];
                nbr[(size_t)u * d + l] = v;
            }
            for (int h = 0; h < G; h++) {
                int v = (k + j) * G + h;
                int u = i * G + mulT[(size_t)h * G + si];
                nbr[(size_t)v * d + l] = u;
            }
        }
    }
}

/* Number of pairs of darts from the same block that would create a multi-edge. */
static long long dupcount(void) {
    long long c = 0;
    const int k = k_, d = d_;
    for (int i = 0; i < k; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (lay[l1 * k + i] == lay[l2 * k + i] && vol[l1 * k + i] == vol[l2 * k + i]) c++;
    return c;
}

static long long cost_eval(void) {
    const int N = N_, d = d_;
    long long tot = 0;
    for (int s = 0; s < 2 * k_; s++) {
        int src = s * G_;
        for (int v = 0; v < N; v++) dist[v] = -1;
        int h = 0, t = 0;
        que[t++] = src;
        dist[src] = 0;
        while (h < t) {
            int v = que[h++];
            if (dist[v] >= D_) continue;
            const int *p = nbr + (size_t)v * d;
            for (int l = 0; l < d; l++) {
                int u = p[l];
                if (dist[u] < 0) {
                    dist[u] = dist[v] + 1;
                    que[t++] = u;
                }
            }
        }
        tot += (long long)(N - t);
    }
    return tot + PEN * dupcount();
}

static void emit(void) {
    const int N = N_, d = d_;
    long long m = 0;
    for (int u = 0; u < N; u++)
        for (int l = 0; l < d; l++)
            if (nbr[(size_t)u * d + l] > u) m++;
    printf("%d %lld\n", N, m);
    for (int u = 0; u < N; u++)
        for (int l = 0; l < d; l++) {
            int v = nbr[(size_t)u * d + l];
            if (v > u) printf("%d %d\n", u, v);
        }
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
    if (d_ < 1 || D_ < 1 || k_ < 1 || m_ < 1 || k2_ < 1 || r_ < 0 ||
        (long long)m_ * k2_ > 2000) {
        printf("0 0\n");
        return 0;
    }
    build_group();
    for (int x = 0; x < G_; x++) {
        if (invT[x] < 0) { printf("0 0\n"); return 0; }
    }

    N_ = 2 * k_ * G_;
    lay = malloc(sizeof(int) * (size_t)d_ * k_);
    vol = malloc(sizeof(int) * (size_t)d_ * k_);
    nbr = malloc(sizeof(int) * (size_t)N_ * d_);
    dist = malloc(sizeof(int) * (size_t)N_);
    que = malloc(sizeof(int) * (size_t)N_);
    int *perm = malloc(sizeof(int) * (size_t)k_);
    if (!lay || !vol || !nbr || !dist || !que || !perm) { printf("0 0\n"); return 0; }

    for (int l = 0; l < d_; l++) {
        for (int i = 0; i < k_; i++) perm[i] = i;
        for (int i = k_ - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
        }
        for (int i = 0; i < k_; i++) {
            lay[l * k_ + i] = perm[i];
            vol[l * k_ + i] = rint_(G_);
        }
    }
    free(perm);

    build_nbr();
    long long cost = cost_eval();
    if (cost == 0) { emit(); return 0; }

    const double T0 = 0.1 * (double)N_ + 1.0, T1 = 0.5;
    double period = limit > 1.5 ? limit / 3.0 : limit;
    if (period <= 0.0) period = 1.0;
    clock_t c0 = clock();

    while (1) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (el >= limit) break;
        double ph = fmod(el, period) / period;
        double T = T0 * pow(T1 / T0, ph);

        if (k_ >= 2 && rdbl() < 0.4) {
            int l = rint_(d_);
            int i1 = rint_(k_), i2 = rint_(k_);
            if (i1 == i2) continue;
            int a = l * k_ + i1, b = l * k_ + i2;
            int t = lay[a]; lay[a] = lay[b]; lay[b] = t;
            build_nbr();
            long long nc = cost_eval();
            if (nc <= cost || rdbl() < exp(-(double)(nc - cost) / T)) {
                cost = nc;
                if (cost == 0) { emit(); return 0; }
            } else {
                t = lay[a]; lay[a] = lay[b]; lay[b] = t;
                build_nbr();
            }
        } else {
            int idx = rint_(d_ * k_);
            int oldv = vol[idx];
            int nv = rint_(G_);
            if (nv == oldv) continue;
            vol[idx] = nv;
            build_nbr();
            long long nc = cost_eval();
            if (nc <= cost || rdbl() < exp(-(double)(nc - cost) / T)) {
                cost = nc;
                if (cost == 0) { emit(); return 0; }
            } else {
                vol[idx] = oldv;
                build_nbr();
            }
        }
    }
    printf("0 0\n");
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions and glue.
# ----------------------------------------------------------------------------

_KS = (1, 2, 2, 3, 3, 4)
_K2_CHOICES = [1, 2, 2, 2, 3, 4, 4, 5, 6, 6, 8, 9, 10, 12]


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _sample_group(target, rng):
    """Return (m, k2, r) for the semidirect product Z_m x| Z_k2 with m*k2 >= target, or None."""
    for _ in range(100):
        k2 = rng.choice(_K2_CHOICES)
        m = max(2, -(-target // k2))
        if k2 == 1:
            return m, 1, 1
        if k2 == 2 and rng.random() < 0.4:
            r = m - 1
            if math.gcd(r, m) == 1 and pow(r, 2, m) == 1 % m:
                return m, 2, r
            continue
        for _ in range(80):
            c = rng.randrange(2, m) if m > 2 else 1
            if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                return m, k2, c
    return None


def _run_lift(d, D, k, m, k2, r, seed, seconds):
    """Run the C lift search; returns (n, edges), where n == 0 means nothing was found."""
    out = lib.run_c(C_LIFT, [d, D, seed, f"{seconds:.2f}", k, m, k2, r],
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

    # Exact construction for D = 3 (calibration case): return immediately.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    # Bi-Cayley lift search. Each attempt targets a group order just above the
    # current best base size; a success raises the bar for the next attempt.
    deadline = t0 + max(1.0, 0.88 * time_limit - 2.0)
    while True:
        remaining = deadline - time.monotonic()
        if remaining < 0.5:
            break
        k = rng.choice(_KS)
        base = best[0] // (2 * k)
        target = base + 1 + rng.randrange(0, max(2, base // 60))
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        G = m * k2
        if G > 2000 or 2 * k * G <= best[0]:
            continue
        slice_s = min(remaining, 4.0 + 6.0 * rng.random())
        if slice_s < 0.5:
            break
        try:
            n, e = _run_lift(d, D, k, m, k2, r, rng.randrange(1, 1 << 30), slice_s)
        except Exception:
            break  # C failure: keep the valid fallback
        if n > 0:
            consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
