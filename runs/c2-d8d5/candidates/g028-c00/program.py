import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing over voltage lifts of bipartite base graphs.
#
# Vertices are A-blocks 0..K-1 and B-blocks K..2K-1, each a copy of the group
# G = Z_M x| Z_K2 (element a*K2+b). The base graph is d-regular: for each layer
# l there is a permutation P[l][i] of the blocks, and A-block i is joined to
# B-block P[l][i] with voltage S[l][i]. Edge (i,x)--(j, x*s). The search
# changes one voltage or swaps two blocks inside one layer, and minimises the
# number of ordered pairs at distance > D (bitset ball expansion) plus a
# penalty for repeated darts. The program stops at the first lift of
# diameter <= D and prints it.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

#define NV_MAX 8000
#define PEN 64LL

static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int n) { return (int)(rnd() % (u64)n); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int d_, D_, K_, M_, K2_, R_, G_, NV, W;
static int *pw, *S, *P, *Pinv, *nbr, *invT;
static u64 *bufA, *bufB;

static int gcd_(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }

static int gmul(int x, int y) {
    int a = x / K2_, b = x % K2_, c = y / K2_, e = y % K2_;
    int ca = (int)((a + (long long)pw[b] * c) % M_);
    return ca * K2_ + (b + e) % K2_;
}

static int ginv(int x) {
    int a = x / K2_, b = x % K2_;
    int nb = (K2_ - b) % K2_;
    int ca = (int)((M_ - ((long long)pw[nb] * a) % M_) % M_);
    return ca * K2_ + nb;
}

static void build_nbr(void) {
    for (int l = 0; l < d_; l++)
        for (int i = 0; i < K_; i++)
            Pinv[l * K_ + P[l * K_ + i]] = i;
    for (int i = 0; i < K_; i++)
        for (int x = 0; x < G_; x++) {
            int v = i * G_ + x;
            for (int l = 0; l < d_; l++) {
                int j = P[l * K_ + i];
                int s = S[l * K_ + i];
                nbr[v * d_ + l] = (K_ + j) * G_ + gmul(x, s);
            }
        }
    for (int j = 0; j < K_; j++)
        for (int y = 0; y < G_; y++) {
            int v = (K_ + j) * G_ + y;
            for (int l = 0; l < d_; l++) {
                int i = Pinv[l * K_ + j];
                int s = S[l * K_ + i];
                int x = gmul(y, invT[s]);
                nbr[v * d_ + l] = i * G_ + x;
            }
        }
}

/* Ordered pairs at distance > D_. Zero means the lift has diameter <= D_. */
static long long unreached(void) {
    W = (NV + 63) / 64;
    u64 *cur = bufA, *alt = bufB;
    memset(cur, 0, sizeof(u64) * (size_t)NV * (size_t)W);
    for (int v = 0; v < NV; v++) cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int it = 0; it < D_; it++) {
        int changed = 0;
        for (int v = 0; v < NV; v++) {
            u64 *x = alt + (size_t)v * W;
            const u64 *r = cur + (size_t)v * W;
            for (int w = 0; w < W; w++) x[w] = r[w];
            for (int l = 0; l < d_; l++) {
                const u64 *q = cur + (size_t)nbr[v * d_ + l] * W;
                for (int w = 0; w < W; w++) x[w] |= q[w];
            }
            for (int w = 0; w < W; w++) if (x[w] != r[w]) changed = 1;
        }
        u64 *t = cur; cur = alt; alt = t;
        if (!changed) break;
    }
    long long cnt = 0;
    for (int v = 0; v < NV; v++) {
        const u64 *r = cur + (size_t)v * W;
        for (int w = 0; w < W; w++) cnt += __builtin_popcountll(r[w]);
    }
    return (long long)NV * NV - cnt;
}

/* Number of darts that repeat an earlier (block, voltage) pair for the same A-block. */
static int dup_count(void) {
    int dup = 0;
    for (int i = 0; i < K_; i++)
        for (int l = 0; l < d_; l++) {
            int seen = 0;
            for (int l2 = 0; l2 < l; l2++)
                if (P[l2 * K_ + i] == P[l * K_ + i] && S[l2 * K_ + i] == S[l * K_ + i]) { seen = 1; break; }
            dup += seen;
        }
    return dup;
}

int main(int argc, char **argv) {
    if (argc < 9) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double limit = atof(argv[4]);
    K_ = atoi(argv[5]);
    M_ = atoi(argv[6]);
    K2_ = atoi(argv[7]);
    R_ = atoi(argv[8]);

    if (d_ < 1 || D_ < 1 || K_ < 1 || M_ < 1 || K2_ < 1) { printf("0 0\n"); return 0; }
    if ((long long)K_ * M_ * K2_ > 4000) { printf("0 0\n"); return 0; }
    G_ = M_ * K2_;
    NV = 2 * K_ * G_;
    if (NV > NV_MAX) { printf("0 0\n"); return 0; }
    if (gcd_(R_ % M_, M_) != 1) { printf("0 0\n"); return 0; }

    pw = malloc(sizeof(int) * (size_t)K2_);
    pw[0] = 1 % M_;
    for (int b = 1; b < K2_; b++) pw[b] = (int)((long long)pw[b - 1] * R_ % M_);
    if ((long long)pw[K2_ - 1] * R_ % M_ != 1 % M_) { printf("0 0\n"); return 0; }

    S = malloc(sizeof(int) * (size_t)K_ * d_);
    P = malloc(sizeof(int) * (size_t)K_ * d_);
    Pinv = malloc(sizeof(int) * (size_t)K_ * d_);
    nbr = malloc(sizeof(int) * (size_t)NV * d_);
    invT = malloc(sizeof(int) * (size_t)G_);
    W = (NV + 63) / 64;
    bufA = malloc(sizeof(u64) * (size_t)NV * W);
    bufB = malloc(sizeof(u64) * (size_t)NV * W);
    if (!pw || !S || !P || !Pinv || !nbr || !invT || !bufA || !bufB) { printf("0 0\n"); return 0; }

    for (int s = 0; s < G_; s++) invT[s] = ginv(s);

    for (int l = 0; l < d_; l++) {
        for (int i = 0; i < K_; i++) P[l * K_ + i] = i;
        for (int i = K_ - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = P[l * K_ + i]; P[l * K_ + i] = P[l * K_ + j]; P[l * K_ + j] = t;
        }
    }
    for (int idx = 0; idx < K_ * d_; idx++) S[idx] = rint_(G_);

    build_nbr();
    long long un = unreached();
    int dup = dup_count();
    long long cost = un + PEN * dup;
    int found = (un == 0);

    clock_t c0 = clock();
    const double T0 = 30.0, T1 = 0.3;
    while (!found) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (el >= limit) break;
        double T = T0 * pow(T1 / T0, el / limit);

        int kind, idx1 = 0, idx2 = 0, oldv = 0;
        if (K_ >= 2 && rint_(10) >= 6) {
            int l = rint_(d_);
            int i1 = rint_(K_);
            int i2 = rint_(K_ - 1);
            if (i2 >= i1) i2++;
            idx1 = l * K_ + i1;
            idx2 = l * K_ + i2;
            int t = P[idx1]; P[idx1] = P[idx2]; P[idx2] = t;
            kind = 1;
        } else {
            idx1 = rint_(d_) * K_ + rint_(K_);
            int nw = rint_(G_);
            if (nw == S[idx1]) continue;
            oldv = S[idx1];
            S[idx1] = nw;
            kind = 0;
        }

        build_nbr();
        un = unreached();
        dup = dup_count();
        long long c2 = un + PEN * dup;
        if (un == 0 || c2 <= cost || rdbl() < exp(-(double)(c2 - cost) / T)) {
            cost = c2;
            if (un == 0) found = 1;
        } else {
            if (kind == 1) {
                int t = P[idx1]; P[idx1] = P[idx2]; P[idx2] = t;
            } else {
                S[idx1] = oldv;
            }
        }
    }

    if (!found) { printf("0 0\n"); return 0; }

    /* nbr matches the accepted state. Emit each edge once, from the A side. */
    int NA = K_ * G_;
    int *eu = malloc(sizeof(int) * (size_t)NA * d_);
    int *ev = malloc(sizeof(int) * (size_t)NA * d_);
    if (!eu || !ev) { printf("0 0\n"); return 0; }
    int m = 0;
    for (int v = 0; v < NA; v++)
        for (int l = 0; l < d_; l++) {
            int u = nbr[v * d_ + l];
            int dupe = 0;
            for (int l2 = 0; l2 < l; l2++)
                if (nbr[v * d_ + l2] == u) { dupe = 1; break; }
            if (!dupe) { eu[m] = v; ev[m] = u; m++; }
        }
    printf("%d %d\n", NV, m);
    for (int i = 0; i < m; i++) printf("%d %d\n", eu[i], ev[i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions and glue.
# ----------------------------------------------------------------------------

_KS = (1, 2, 3, 4, 6, 8)


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo and Lopez graph for degree d = q + 2 with q a prime power, else None."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        return lib.araujo_lopez_graph(q)
    return None


def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target, or None."""
    for _ in range(300):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 8, 9, 10, 12, 16])
        m = max(2, -(-target // k2))
        if k2 == 1:
            return m, 1, 1
        r = None
        for _ in range(80):
            c = rng.randrange(2, m) if m > 2 else 1
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

    exact = False
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            exact = (D == 3 and lib.is_prime_power(d - 1))
        if D == 3:
            try:
                ar = _araujo(d)
                if ar is not None:
                    consider(ar[0], ar[1])
            except Exception:
                pass
    if exact:
        return best

    # Hard stop with margin before the per-case limit.
    hard_end = t0 + 0.85 * time_limit - 2.0

    # Warm up (compile and cache the C program) on a trivial instance.
    try:
        lib.run_c(C_SOURCE, [1, 1, 1, "0.01", 1, 1, 1, 1], timeout=30.0)
    except Exception:
        pass

    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.25:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.05 * rng.random())

    # Climb: each C run looks for a valid lift just above the current best order.
    while True:
        remaining = hard_end - time.monotonic()
        if remaining < 1.5:
            break
        k = pick_k()
        base = best[0] // (2 * k)
        target = max(2, base + 1 + rng.randrange(0, base // 16 + 2))
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        order = 2 * k * m * k2
        if order <= best[0] or order > 8000:
            continue
        trials[k] += 1
        slice_s = min(remaining, 12.0)
        try:
            out = lib.run_c(C_SOURCE,
                            [d, D, rng.randrange(1, 1 << 30), f"{slice_s:.2f}", k, m, k2, r],
                            timeout=slice_s + 10.0)
            n, e = lib.parse_graph_text(out)
        except Exception:
            continue
        before = best[0]
        consider(n, e)
        if best[0] > before:
            wins[k] += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
