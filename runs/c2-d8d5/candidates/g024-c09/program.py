import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing over bi-Cayley lifts with cyclic-or-metacyclic
# voltage groups G = Z_m x| Z_t (element a*t+b, product (a,b)(c,e) = (a+r^b c, b+e)).
#
# Base graph: K "A" blocks and K "B" blocks. Layer l (of d layers) is a perfect
# matching A_i -> B_{perm[l][i]} with voltage volt[l][i] in G. The lift has
# 2*K*|G| vertices, block b vertex x is b*|G|+x, and every vertex has degree d.
# Left multiplication by G is an automorphism, so the diameter is decided by
# BFS from the 2K block representatives. Reach sets are kept as bitmasks over
# the 2K sources, so one evaluation costs about D*N*d word operations.
# Cost = unreached (source, vertex) pairs + PEN * duplicate darts.
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

static int d_, D_, K, GM, GT, GR, GG, NV;
static long long PEN;
static int rpw[64];
static int *perm, *pinv, *volt, *nbr;
static u64 *RA, *RB;

static inline int gmul(int x, int y) {
    int a = x / GT, b = x % GT, c = y / GT, e = y % GT;
    int a2 = (int)((a + (long long)rpw[b] * c) % GM);
    int b2 = (b + e) % GT;
    return a2 * GT + b2;
}

static inline int ginv(int x) {
    int a = x / GT, b = x % GT;
    int nb = (GT - b) % GT;
    long long v = ((long long)rpw[nb] * a) % GM;
    int a2 = (int)((GM - v) % GM);
    return a2 * GT + nb;
}

static void build_nbr(void) {
    for (int l = 0; l < d_; l++) {
        for (int i = 0; i < K; i++) {
            int j = perm[l * K + i], s = volt[l * K + i];
            for (int x = 0; x < GG; x++) {
                int A = i * GG + x;
                nbr[(size_t)A * d_ + l] = (K + j) * GG + gmul(x, s);
            }
        }
        for (int j = 0; j < K; j++) {
            int i = pinv[l * K + j];
            int s = volt[l * K + i];
            int si = ginv(s);
            for (int y = 0; y < GG; y++) {
                int B = (K + j) * GG + y;
                nbr[(size_t)B * d_ + l] = i * GG + gmul(y, si);
            }
        }
    }
}

static long long dups(void) {
    long long c = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < d_; l1++)
            for (int l2 = l1 + 1; l2 < d_; l2++)
                if (perm[l1 * K + i] == perm[l2 * K + i] && volt[l1 * K + i] == volt[l2 * K + i]) c++;
    return c;
}

static long long evalcost(void) {
    build_nbr();
    u64 *cur = RA, *nxt = RB;
    for (int v = 0; v < NV; v++) cur[v] = 0;
    for (int b = 0; b < 2 * K; b++) cur[(size_t)b * GG] |= 1ULL << b;
    for (int it = 0; it < D_; it++) {
        int changed = 0;
        for (int v = 0; v < NV; v++) {
            u64 x = cur[v];
            const int *nb = nbr + (size_t)v * d_;
            for (int l = 0; l < d_; l++) x |= cur[nb[l]];
            nxt[v] = x;
            if (x != cur[v]) changed = 1;
        }
        u64 *tp = cur; cur = nxt; nxt = tp;
        if (!changed) break;
    }
    long long unr = 0;
    for (int b = 0; b < 2 * K; b++) {
        long long cnt = 0;
        for (int v = 0; v < NV; v++) cnt += (long long)((cur[v] >> b) & 1ULL);
        unr += NV - cnt;
    }
    return unr + PEN * dups();
}

int main(int argc, char **argv) {
    if (argc < 9) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double secs = atof(argv[4]);
    K = atoi(argv[5]);
    GM = atoi(argv[6]);
    GT = atoi(argv[7]);
    GR = atoi(argv[8]);
    if (d_ < 1 || D_ < 1 || K < 1 || K > 32 || GM < 1 || GT < 1 || GT > 64) { printf("0 0\n"); return 0; }
    GG = GM * GT;
    if (GG > 200000) { printf("0 0\n"); return 0; }
    NV = 2 * K * GG;
    if (NV > 400000) { printf("0 0\n"); return 0; }
    rpw[0] = 1 % GM;
    for (int b = 1; b < GT; b++) rpw[b] = (int)(((long long)rpw[b - 1] * GR) % GM);
    if (GT > 1 && (((long long)rpw[GT - 1] * GR) % GM) != 1 % GM) { printf("0 0\n"); return 0; }

    perm = malloc(sizeof(int) * (size_t)d_ * K);
    pinv = malloc(sizeof(int) * (size_t)d_ * K);
    volt = malloc(sizeof(int) * (size_t)d_ * K);
    nbr = malloc(sizeof(int) * (size_t)NV * d_);
    RA = malloc(sizeof(u64) * (size_t)NV);
    RB = malloc(sizeof(u64) * (size_t)NV);
    if (!perm || !pinv || !volt || !nbr || !RA || !RB) { printf("0 0\n"); return 0; }

    PEN = NV;
    for (int l = 0; l < d_; l++) {
        int *p = perm + l * K;
        for (int i = 0; i < K; i++) p[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = p[i]; p[i] = p[j]; p[j] = t;
        }
        for (int i = 0; i < K; i++) pinv[l * K + p[i]] = i;
        for (int i = 0; i < K; i++) volt[l * K + i] = rint_(GG);
    }

    long long cost = evalcost();
    long long cost0 = cost > 0 ? cost : 1;
    double Tm0 = 0.05 * (double)cost0 + 2.0, Tm1 = 0.3;
    clock_t c0 = clock();

    while (cost > 0) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (el >= secs) break;
        double Tm = Tm0 * pow(Tm1 / Tm0, el / secs);
        int l = rint_(d_);
        int kind = (K >= 2 && rdbl() < 0.35) ? 1 : 0;
        int idx = 0, oldv = 0, i1 = 0, i2 = 0;
        if (kind == 0) {
            idx = l * K + rint_(K);
            int nvv = rint_(GG);
            if (nvv == volt[idx]) continue;
            oldv = volt[idx];
            volt[idx] = nvv;
        } else {
            i1 = rint_(K);
            i2 = rint_(K - 1);
            if (i2 >= i1) i2++;
            int *p = perm + l * K;
            int t = p[i1]; p[i1] = p[i2]; p[i2] = t;
            pinv[l * K + p[i1]] = i1;
            pinv[l * K + p[i2]] = i2;
        }
        long long nc = evalcost();
        long long delta = nc - cost;
        if (delta <= 0 || rdbl() < exp(-(double)delta / Tm)) {
            cost = nc;
        } else if (kind == 0) {
            volt[idx] = oldv;
        } else {
            int *p = perm + l * K;
            int t = p[i1]; p[i1] = p[i2]; p[i2] = t;
            pinv[l * K + p[i1]] = i1;
            pinv[l * K + p[i2]] = i2;
        }
    }

    cost = evalcost();
    if (cost != 0) { printf("0 0\n"); return 0; }
    int A = K * GG;
    printf("%d %d\n", NV, A * d_);
    for (int v = 0; v < A; v++)
        for (int l = 0; l < d_; l++)
            printf("%d %d\n", v, nbr[(size_t)v * d_ + l]);
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
    """Return (m, t, r) describing Z_m x| Z_t with m*t >= target (r = 1 when t = 1)."""
    t = rng.choice([1, 1, 1, 2, 2, 3, 4, 5, 6, 8])
    m = max(2, -(-target // t))
    if t == 1:
        return m, 1, 1
    for _ in range(80):
        r = rng.randrange(1, m)
        if math.gcd(r, m) == 1 and pow(r, t, m) == 1 % m:
            return m, t, r
    return max(2, -(-target)), 1, 1


def _run_lift(d, D, k, m, t, r, seed, secs):
    """Run the C lift annealer; returns (n, edges), with n = 0 on failure."""
    out = lib.run_c(C_SOURCE, [d, D, seed, f"{secs:.2f}", k, m, t, r],
                    stdin_graph=None, timeout=secs + 20.0)
    return lib.parse_graph_text(out)


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}, diameter 2

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

    end = t0 + time_limit - max(2.0, 0.08 * time_limit)

    if d >= 3 and time.monotonic() < end - 1.0:
        trials = {k: 0 for k in _KS}
        wins = {k: 0 for k in _KS}
        frac = 0.08  # target gap above the current best, as a fraction of best

        def pick_k():
            if rng.random() < 0.25:
                return rng.choice(_KS)
            return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.03 * rng.random())

        while True:
            remaining = end - time.monotonic()
            if remaining < 1.0:
                break
            k = pick_k()
            gap = max(2, int(round(frac * best[0])))
            target_G = -(-(best[0] + gap) // (2 * k))
            m, t, r = _sample_group(max(2, target_G), rng)
            G = m * t
            if 2 * k * G <= best[0]:
                continue
            secs = min(remaining - 0.5, max(1.5, min(6.0, remaining / 3.0)))
            trials[k] += 1
            before = best[0]
            try:
                n, e = _run_lift(d, D, k, m, t, r, rng.randrange(1, 1 << 30), secs)
            except Exception:
                break
            if n > 0:
                consider(n, e)
            if best[0] > before:
                wins[k] += 1
                frac = min(0.1, frac * 1.2)
            else:
                frac = max(0.002, frac * 0.6)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
