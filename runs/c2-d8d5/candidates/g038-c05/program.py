import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: voltage-lift annealer over Z_m x| Z_k2 (bi-Cayley lifts).
#
# Base graph: k left and k right vertices, d layers. Layer l sends left i to
# right lay[l][i] (a permutation per layer) with voltage S[l][i] in the group.
# The lift has vertices (block, x) for x in G, edges (i, x) -- (k+j, x*s).
#
# New idea: left multiplication by g is an automorphism of the lift, so every
# vertex of a block sees the same distance profile. The validity cost is
# therefore only 2k BFS runs from the base vertices (block, identity), each
# O(N*d), instead of a full bitset closure over all N vertices.
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

#define PEN 8

static int d_, D_, k_, G_, M_, K2_, NV;
static int *pw, *lay, *lin, *S, *iS, *nbr, *vstamp, *qu;
static int stamp_ = 0;

/* Element a*K2 + b of Z_M x| Z_K2 with (a,b)(c,e) = (a + r^b c, b + e). */
static int gmul(int x, int y) {
    int a = x / K2_, b = x % K2_;
    int c = y / K2_, e = y % K2_;
    int A = (int)(((long long)a + (long long)pw[b] * c) % M_);
    int B = (b + e) % K2_;
    return A * K2_ + B;
}

/* Inverse of (a,b) is (-r^(-b) a, -b). */
static int ginv(int x) {
    int a = x / K2_, b = x % K2_;
    int nb = (K2_ - b) % K2_;
    int ia = (int)((M_ - ((long long)pw[nb] * a) % M_) % M_);
    return ia * K2_ + nb;
}

static void rebuild(void) {
    const int d = d_, k = k_, G = G_;
    for (int idx = 0; idx < d * k; idx++) iS[idx] = ginv(S[idx]);
    for (int l = 0; l < d; l++)
        for (int i = 0; i < k; i++)
            lin[l * k + lay[l * k + i]] = i;
    for (int i = 0; i < k; i++)
        for (int x = 0; x < G; x++) {
            int *nb = nbr + (size_t)(i * G + x) * d;
            for (int l = 0; l < d; l++)
                nb[l] = (k + lay[l * k + i]) * G + gmul(x, S[l * k + i]);
        }
    for (int j = 0; j < k; j++)
        for (int y = 0; y < G; y++) {
            int *nb = nbr + (size_t)((k + j) * G + y) * d;
            for (int l = 0; l < d; l++) {
                int i = lin[l * k + j];
                nb[l] = i * G + gmul(y, iS[l * k + i]);
            }
        }
}

/* Number of vertices NOT within distance D_ of src. */
static long long far_from(int src) {
    stamp_++;
    int h = 0, t = 0;
    qu[t++] = src;
    vstamp[src] = stamp_;
    for (int depth = 0; depth < D_ && h < t; depth++) {
        int end = t;
        while (h < end) {
            int v = qu[h++];
            int *nb = nbr + (size_t)v * d_;
            for (int l = 0; l < d_; l++) {
                int u = nb[l];
                if (vstamp[u] != stamp_) { vstamp[u] = stamp_; qu[t++] = u; }
            }
        }
    }
    return (long long)NV - t;
}

/* Cost = far pairs from base vertices (scaled by symmetry) + duplicate penalty. */
static long long eval_cost(int *dup_out) {
    long long cost = 0;
    for (int b = 0; b < 2 * k_; b++) cost += far_from(b * G_);
    int dup = 0;
    for (int b = 0; b < 2 * k_; b++) {
        int *nb = nbr + (size_t)(b * G_) * d_;
        for (int l = 0; l < d_; l++)
            for (int m2 = l + 1; m2 < d_; m2++)
                if (nb[l] == nb[m2]) dup++;
    }
    *dup_out = dup;
    return cost + (long long)PEN * dup;
}

static void randomize(void) {
    int perm[64];
    for (int l = 0; l < d_; l++) {
        for (int i = 0; i < k_; i++) perm[i] = i;
        for (int i = k_ - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
        }
        for (int i = 0; i < k_; i++) lay[l * k_ + i] = perm[i];
    }
    for (int idx = 0; idx < d_ * k_; idx++) S[idx] = rint_(G_);
}

int main(int argc, char **argv) {
    if (argc < 9) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    u64 seed = strtoull(argv[3], NULL, 10);
    rs ^= seed * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double limit = atof(argv[4]);
    k_ = atoi(argv[5]);
    M_ = atoi(argv[6]);
    K2_ = atoi(argv[7]);
    int r = atoi(argv[8]);
    if (d_ < 1 || D_ < 1 || k_ < 1 || k_ > 64 || M_ < 2 || K2_ < 1 || r < 1 || r >= M_) {
        printf("0 0\n");
        return 0;
    }
    {
        int aa = r, bb = M_;
        while (bb) { int t = aa % bb; aa = bb; bb = t; }
        if (aa != 1) { printf("0 0\n"); return 0; }
    }
    G_ = M_ * K2_;
    NV = 2 * k_ * G_;
    pw = calloc(K2_, sizeof(int));
    pw[0] = 1 % M_;
    for (int t = 1; t < K2_; t++) pw[t] = (int)((long long)pw[t - 1] * r % M_);
    if ((long long)pw[K2_ - 1] * r % M_ != 1 % M_) { printf("0 0\n"); return 0; }

    int dk = d_ * k_;
    lay = calloc(dk, sizeof(int));
    lin = calloc(dk, sizeof(int));
    S = calloc(dk, sizeof(int));
    iS = calloc(dk, sizeof(int));
    nbr = calloc((size_t)NV * d_, sizeof(int));
    vstamp = calloc(NV, sizeof(int));
    qu = calloc(NV, sizeof(int));
    if (!pw || !lay || !lin || !S || !iS || !nbr || !vstamp || !qu) { printf("0 0\n"); return 0; }

    randomize();
    rebuild();
    int dup = 0;
    long long cost = eval_cost(&dup);
    long long bestc = cost;
    long long stagn = 0;

    const double T0 = 5.0, T1 = 0.2;
    clock_t c0 = clock();
    while (!(cost == 0 && dup == 0)) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (el >= limit) break;
        double T = T0 * pow(T1 / T0, el / limit);

        int l = rint_(d_);
        int kind = 1, i1 = 0, i2 = 0, oldv = 0;
        if (k_ >= 2 && rdbl() < 0.3) {
            kind = 0;
            i1 = rint_(k_);
            i2 = rint_(k_ - 1);
            if (i2 >= i1) i2++;
            int *a = &lay[l * k_ + i1], *b = &lay[l * k_ + i2];
            int tmp = *a; *a = *b; *b = tmp;
        } else {
            i1 = rint_(k_);
            oldv = S[l * k_ + i1];
            S[l * k_ + i1] = rint_(G_);
        }
        rebuild();
        int nd = 0;
        long long nc = eval_cost(&nd);
        long long delta = nc - cost;
        if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
            cost = nc;
            dup = nd;
            if (cost < bestc) { bestc = cost; stagn = 0; }
            else stagn++;
        } else {
            if (kind == 0) {
                int *a = &lay[l * k_ + i1], *b = &lay[l * k_ + i2];
                int tmp = *a; *a = *b; *b = tmp;
            } else {
                S[l * k_ + i1] = oldv;
            }
            rebuild();
            stagn++;
        }
        if (stagn > 60000) {
            randomize();
            rebuild();
            cost = eval_cost(&dup);
            bestc = cost;
            stagn = 0;
        }
    }

    if (cost == 0 && dup == 0) {
        rebuild();
        int m = k_ * G_ * d_;
        printf("%d %d\n", NV, m);
        for (int v = 0; v < k_ * G_; v++)
            for (int l = 0; l < d_; l++)
                printf("%d %d\n", v, nbr[(size_t)v * d_ + l]);
    } else {
        printf("0 0\n");
    }
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


def _group_for_order(G, rng):
    """Random (m, k2, r) with m * k2 = G, giving Z_m x| Z_k2 (r^k2 = 1 mod m, gcd(r, m) = 1), or None."""
    divs = [k2 for k2 in range(1, G + 1) if G % k2 == 0 and G // k2 >= 2]
    rng.shuffle(divs)
    for k2 in divs[:12]:
        m = G // k2
        if k2 == 1:
            return m, 1, 1
        for _ in range(40):
            r = rng.randrange(1, m)
            if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m:
                return m, k2, r
    return None


def _lift_in_c(d, D, k, m, k2, r, seconds, seed):
    """Run the C lift annealer; returns (n, edges), with (0, []) when it finds nothing."""
    out = lib.run_c(C_LIFT, [d, D, seed, f"{seconds:.2f}", k, m, k2, r],
                    timeout=seconds + 15.0)
    return lib.parse_graph_text(out)


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    deadline = t0 + max(1.0, time_limit - max(3.0, 0.08 * time_limit))
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

    # Bi-Cayley lift search in C, aiming just above the current best order.
    _KS = (1, 2, 2, 3, 4)
    while True:
        remaining = deadline - time.monotonic()
        if remaining < 2.0:
            break
        k = rng.choice(_KS)
        Gmin = best[0] // (2 * k) + 1
        G = Gmin + rng.randrange(0, 2 + Gmin // 150)
        grp = _group_for_order(G, rng)
        if grp is None:
            continue
        m, k2, r = grp
        budget = min(remaining, max(2.5, 0.2 * remaining))
        try:
            n, e = _lift_in_c(d, D, k, m, k2, r, budget, rng.randrange(1, 1 << 30))
        except RuntimeError:
            continue
        consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
