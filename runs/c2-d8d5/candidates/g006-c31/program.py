import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing over bi-Cayley lifts of a semidirect product
# Z_m x| Z_k2 with k base vertices per side.
#
# Vertex (block, x) is index block*G + x, with G = m*k2 and element code a*k2+b.
# A-blocks are 0..k-1 and B-blocks are k..2k-1. Layer l joins A-block i to
# B-block lay[l][i] with voltage S[l][i]: (i, x) ~ (j, x*s). Left translation
# by any group element is an automorphism, so the ball of any vertex is a
# translate of the ball of its block's identity. The cost is therefore the
# number of vertices not within distance D of the 2k block identities, plus a
# penalty per duplicate (multi-)edge. Cost 0 gives a valid simple graph.
# ----------------------------------------------------------------------------

C_LIFT_SOURCE = r"""
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

static int d_, D_, k_, G_, m_, k2_, r_, N_;
static int *powr, *S, *lay, *nbr, *dist, *qq;

static long long powmod_ll(long long b, long long e, long long m) {
    long long res = 1 % m;
    b %= m;
    if (b < 0) b += m;
    while (e > 0) {
        if (e & 1) res = res * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return res;
}

static long long gcd_ll(long long a, long long b) {
    while (b) { long long t = a % b; a = b; b = t; }
    return a;
}

static int gmul(int x, int y) {
    int a = x / k2_, b = x - a * k2_;
    int c = y / k2_, dd = y - c * k2_;
    long long aa = ((long long)a + (long long)powr[b] * c) % m_;
    int e = b + dd;
    if (e >= k2_) e -= k2_;
    return (int)aa * k2_ + e;
}

static int ginv(int x) {
    int a = x / k2_, b = x - a * k2_;
    int nb = (k2_ - b) % k2_;
    long long t = (-((long long)powr[nb] * a)) % m_;
    if (t < 0) t += m_;
    return (int)t * k2_ + nb;
}

/* Recompute the layer-l neighbours of A-block i and of B-block lay[l][i]. */
static void refresh(int l, int i) {
    int j = lay[l * k_ + i];
    int s = S[l * k_ + i];
    int si = ginv(s);
    int ia = i * G_, jb = (k_ + j) * G_;
    for (int x = 0; x < G_; x++) {
        nbr[(ia + x) * d_ + l] = jb + gmul(x, s);
        nbr[(jb + x) * d_ + l] = ia + gmul(x, si);
    }
}

static int dupcount(void) {
    int c = 0;
    for (int i = 0; i < k_; i++)
        for (int l1 = 0; l1 < d_; l1++)
            for (int l2 = l1 + 1; l2 < d_; l2++)
                if (lay[l1 * k_ + i] == lay[l2 * k_ + i] && S[l1 * k_ + i] == S[l2 * k_ + i]) c++;
    return c;
}

/* Unreached vertices summed over the 2k block identities. */
static long long eval_cost(void) {
    int N = N_;
    long long cost = 0;
    for (int b = 0; b < 2 * k_; b++) {
        int src = b * G_;
        for (int v = 0; v < N; v++) dist[v] = -1;
        int h = 0, t = 0;
        qq[t++] = src;
        dist[src] = 0;
        while (h < t) {
            int v = qq[h++];
            int dv = dist[v];
            if (dv >= D_) continue;
            const int *nb = nbr + (size_t)v * d_;
            for (int l = 0; l < d_; l++) {
                int u = nb[l];
                if (dist[u] < 0) { dist[u] = dv + 1; qq[t++] = u; }
            }
        }
        cost += N - t;
    }
    return cost;
}

static long long total_cost(void) {
    return eval_cost() + (long long)N_ * (long long)dupcount();
}

int main(int argc, char **argv) {
    if (argc < 9) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    u64 seed = (u64)strtoull(argv[3], NULL, 10);
    rs ^= seed * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double limit = atof(argv[4]);
    k_ = atoi(argv[5]);
    m_ = atoi(argv[6]);
    k2_ = atoi(argv[7]);
    r_ = atoi(argv[8]);

    if (d_ < 1 || D_ < 1 || k_ < 1 || m_ < 2 || k2_ < 1 || k2_ > 1000000 || r_ < 0) {
        printf("0 0\n");
        return 0;
    }
    long long G = (long long)m_ * k2_;
    if (G > 1000000 || 2LL * k_ * G > 300000) { printf("0 0\n"); return 0; }
    if (gcd_ll(r_, m_) != 1 || powmod_ll(r_, k2_, m_) != 1 % m_) { printf("0 0\n"); return 0; }

    G_ = (int)G;
    N_ = 2 * k_ * G_;

    powr = malloc(sizeof(int) * (size_t)k2_);
    S = malloc(sizeof(int) * (size_t)d_ * k_);
    lay = malloc(sizeof(int) * (size_t)d_ * k_);
    nbr = malloc(sizeof(int) * (size_t)N_ * d_);
    dist = malloc(sizeof(int) * (size_t)N_);
    qq = malloc(sizeof(int) * (size_t)N_);
    int *perm = malloc(sizeof(int) * (size_t)k_);
    if (!powr || !S || !lay || !nbr || !dist || !qq || !perm) { printf("0 0\n"); return 0; }

    powr[0] = 1 % m_;
    for (int b = 1; b < k2_; b++) powr[b] = (int)((long long)powr[b - 1] * r_ % m_);

    for (int l = 0; l < d_; l++) {
        for (int i = 0; i < k_; i++) perm[i] = i;
        for (int i = k_ - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
        }
        for (int i = 0; i < k_; i++) lay[l * k_ + i] = perm[i];
        for (int i = 0; i < k_; i++) S[l * k_ + i] = rint_(G_);
    }
    for (int l = 0; l < d_; l++)
        for (int i = 0; i < k_; i++) refresh(l, i);

    clock_t c0 = clock();
    long long cur = total_cost();
    double c0f = (double)(cur > 0 ? cur : 1);
    double T0 = 0.05 * c0f;
    if (T0 < 2.0) T0 = 2.0;
    const double T1 = 0.3;
    double T = T0;
    long long it = 0;

    while (cur != 0) {
        if ((it & 15) == 0) {
            double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
            if (el >= limit) break;
            double frac = limit > 0 ? el / limit : 1.0;
            if (frac > 1.0) frac = 1.0;
            T = T0 * pow(T1 / T0, frac);
        }
        it++;

        if (k_ >= 2 && rdbl() < 0.2) {
            int l = rint_(d_);
            int i1 = rint_(k_);
            int i2 = rint_(k_ - 1);
            if (i2 >= i1) i2++;
            int *pa = &lay[l * k_ + i1], *pb = &lay[l * k_ + i2];
            int t = *pa; *pa = *pb; *pb = t;
            refresh(l, i1);
            refresh(l, i2);
            long long nc = total_cost();
            if (nc <= cur || rdbl() < exp(-(double)(nc - cur) / T)) {
                cur = nc;
            } else {
                t = *pa; *pa = *pb; *pb = t;
                refresh(l, i1);
                refresh(l, i2);
            }
        } else {
            int l = rint_(d_);
            int i = rint_(k_);
            int old = S[l * k_ + i];
            int nw = rint_(G_);
            if (nw == old) continue;
            S[l * k_ + i] = nw;
            refresh(l, i);
            long long nc = total_cost();
            if (nc <= cur || rdbl() < exp(-(double)(nc - cur) / T)) {
                cur = nc;
            } else {
                S[l * k_ + i] = old;
                refresh(l, i);
            }
        }
    }

    if (cur != 0) {
        printf("0 0\n");
        return 0;
    }

    long long M = (long long)k_ * G_ * d_;
    printf("%d %lld\n", N_, M);
    int A = k_ * G_;
    for (int v = 0; v < A; v++)
        for (int l = 0; l < d_; l++)
            printf("%d %d\n", v, nbr[v * d_ + l]);
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
            return True
        return False

    # Exact construction for D = 3 (calibration case): return immediately.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    # Bi-Cayley lift search in C, with a bandit over the base size k.
    search_end = t0 + min(0.9 * time_limit, max(0.5, 0.85 * time_limit - 2.0))
    ks = (1, 2, 3, 4, 5, 6)
    trials = {k: 0 for k in ks}
    wins = {k: 0 for k in ks}

    def pick_k():
        if rng.random() < 0.25:
            return rng.choice(ks)
        return max(ks, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while True:
        remaining = search_end - time.monotonic()
        if remaining < 1.0:
            break
        k = pick_k()
        base = best[0] // (2 * k)
        gmin = base + 1
        target = gmin + rng.randrange(0, max(2, gmin // 30 + 1))
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        if 2 * k * m * k2 <= best[0]:
            continue
        slice_s = min(remaining, 9.0)
        trials[k] += 1
        try:
            out = lib.run_c(C_LIFT_SOURCE,
                            [d, D, rng.randrange(1, 1 << 30), f"{slice_s:.2f}", k, m, k2, r],
                            timeout=slice_s + 15.0)
            n, e = lib.parse_graph_text(out)
        except Exception:
            continue
        if n > 0 and consider(n, e):
            wins[k] += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
