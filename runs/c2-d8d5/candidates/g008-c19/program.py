import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# New engine: C search for bi-Cayley lifts over semidirect products
# Z_m x| Z_k2 (element a*k2+b, product (a,b)(c,e) = (a + r^b c, b + e)).
#
# Base graph: k A-blocks and k B-blocks, each a copy of G = m*k2 vertices.
# Layer l (l < d) is a permutation lay[l] matching A-block i to B-block lay[l][i]
# with voltage sv[l][i]: vertex (i,g) joins (k+j, g*s). Every vertex then has
# degree exactly d, provided no two darts coincide.
#
# Search: simulated annealing over permutations and voltages. The cost counts
# (block, vertex) pairs that are not reached within distance D. Left
# multiplication by the group is an automorphism, so checking the block
# identities as targets from every vertex is equivalent to checking the full
# diameter. Each evaluation is therefore a bitmask ball expansion over 2k bits
# per vertex, which is much cheaper than a full bitset BFS. The search stops at
# the first zero-cost state, and Python then grows the target order.
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

#define MAXD 16
#define MAXK 8
#define MAXN 32768
#define PEN 1000

static int d_, D_, k_, m_, k2_, r_, G_, N_;
static int pw_[64];
static int lay[MAXD][MAXK];
static int sv[MAXD][MAXK];
static int nb[MAXD][MAXN];
static uint32_t BA[MAXN], BB[MAXN], RCUR[MAXN], RCAND[MAXN];
static int BADL[MAXN];

static int pc32(uint32_t x) { int c = 0; while (x) { x &= x - 1; c++; } return c; }

static int gmul(int x, int y) {
    int a = x / k2_, b = x % k2_;
    int c = y / k2_, e = y % k2_;
    return ((a + pw_[b] * c) % m_) * k2_ + (b + e) % k2_;
}

static int ginv(int x) {
    int a = x / k2_, b = x % k2_;
    int nbb = (k2_ - b) % k2_;
    int t = (int)(((long long)pw_[nbb] * a) % m_);
    int na = (m_ - t) % m_;
    return na * k2_ + nbb;
}

/* Writes the darts of (layer l, A-block i) in both directions. */
static void set_dart(int l, int i) {
    int j = lay[l][i], s = sv[l][i];
    int A = i * G_, B = (k_ + j) * G_;
    int si = ginv(s);
    for (int g = 0; g < G_; g++) {
        nb[l][A + g] = B + gmul(g, s);
        nb[l][B + g] = A + gmul(g, si);
    }
}

/* Number of duplicated darts (same A-block, same B-block, same voltage). */
static int dup_count(void) {
    int c = 0;
    for (int i = 0; i < k_; i++)
        for (int l = 0; l < d_; l++)
            for (int l2 = l + 1; l2 < d_; l2++)
                if (lay[l][i] == lay[l2][i] && sv[l][i] == sv[l2][i]) c++;
    return c;
}

/* Cost = unreached (vertex, identity-of-block) pairs + penalty for duplicates.
   Zero iff the lift has diameter <= D_. The reach masks are written to out. */
static long long evalcost(uint32_t *out) {
    int N = N_, K2 = 2 * k_, G = G_;
    uint32_t *cur = BA, *nxt = BB;
    for (int v = 0; v < N; v++) cur[v] = 0;
    for (int b = 0; b < K2; b++) cur[b * G] = 1u << b;
    for (int it = 0; it < D_; it++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint32_t x = cur[v];
            for (int l = 0; l < d_; l++) x |= cur[nb[l][v]];
            nxt[v] = x;
            if (x != cur[v]) changed = 1;
        }
        uint32_t *t = cur; cur = nxt; nxt = t;
        if (!changed) break;
    }
    memcpy(out, cur, sizeof(uint32_t) * (size_t)N);
    long long tot = 0;
    for (int v = 0; v < N; v++) tot += K2 - pc32(cur[v]);
    tot += (long long)PEN * dup_count();
    return tot;
}

int main(int argc, char **argv) {
    if (argc < 9) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    u64 seed = strtoull(argv[3], NULL, 10);
    double limit = atof(argv[4]);
    k_ = atoi(argv[5]);
    m_ = atoi(argv[6]);
    k2_ = atoi(argv[7]);
    r_ = atoi(argv[8]);
    if (d_ < 1 || d_ > MAXD || D_ < 1 || k_ < 1 || k_ > MAXK ||
        m_ < 1 || m_ > MAXN || k2_ < 1 || k2_ > 64) {
        printf("0 0\n");
        return 0;
    }
    G_ = m_ * k2_;
    N_ = 2 * k_ * G_;
    if (N_ > MAXN) { printf("0 0\n"); return 0; }

    r_ = ((r_ % m_) + m_) % m_;
    pw_[0] = 1 % m_;
    for (int b = 1; b < k2_; b++) pw_[b] = (int)((long long)pw_[b - 1] * r_ % m_);
    if ((long long)pw_[k2_ - 1] * r_ % m_ != 1 % m_) { printf("0 0\n"); return 0; }

    rs ^= seed * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int t = 0; t < 10; t++) rnd();

    for (int l = 0; l < d_; l++) {
        for (int i = 0; i < k_; i++) lay[l][i] = i;
        for (int i = k_ - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = lay[l][i]; lay[l][i] = lay[l][j]; lay[l][j] = t;
        }
        for (int i = 0; i < k_; i++) sv[l][i] = rint_(G_);
        for (int i = 0; i < k_; i++) set_dart(l, i);
    }

    long long cost = evalcost(RCUR);
    const double T0 = 10.0, T1 = 0.2;
    const int cycles = 5;
    uint32_t full = (1u << (2 * k_)) - 1;
    clock_t c0 = clock();

    while (cost > 0) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (el >= limit) break;
        double ph = fmod(el / limit * cycles, 1.0);
        double T = T0 * pow(T1 / T0, ph);

        if (k_ >= 2 && rdbl() < 0.25) {
            /* Swap two A-blocks' B-targets within one layer. */
            int l = rint_(d_);
            int i1 = rint_(k_), i2 = rint_(k_ - 1);
            if (i2 >= i1) i2++;
            int t = lay[l][i1]; lay[l][i1] = lay[l][i2]; lay[l][i2] = t;
            set_dart(l, i1); set_dart(l, i2);
            long long nc = evalcost(RCAND);
            if (nc <= cost || rdbl() < exp(-(double)(nc - cost) / T)) {
                cost = nc;
                memcpy(RCUR, RCAND, sizeof(uint32_t) * (size_t)N_);
            } else {
                t = lay[l][i1]; lay[l][i1] = lay[l][i2]; lay[l][i2] = t;
                set_dart(l, i1); set_dart(l, i2);
            }
        } else {
            /* Change one voltage, biased toward blocks with unreached pairs. */
            int nbad = 0;
            if (rdbl() < 0.4) {
                for (int v = 0; v < N_; v++) if (RCUR[v] != full) BADL[nbad++] = v;
            }
            int l, i = -1;
            if (nbad > 0) {
                int u = BADL[rint_(nbad)];
                int blk = u / G_;
                l = rint_(d_);
                if (blk < k_) i = blk;
                else {
                    int j = blk - k_;
                    for (int q = 0; q < k_; q++) if (lay[l][q] == j) { i = q; break; }
                }
            } else {
                l = rint_(d_);
                i = rint_(k_);
            }
            if (i < 0) continue;
            int old = sv[l][i];
            int nw = rint_(G_);
            if (nw == old) continue;
            sv[l][i] = nw;
            set_dart(l, i);
            long long nc = evalcost(RCAND);
            if (nc <= cost || rdbl() < exp(-(double)(nc - cost) / T)) {
                cost = nc;
                memcpy(RCUR, RCAND, sizeof(uint32_t) * (size_t)N_);
            } else {
                sv[l][i] = old;
                set_dart(l, i);
            }
        }
    }

    if (cost != 0) { printf("0 0\n"); return 0; }
    long long M = (long long)d_ * k_ * G_;
    printf("%d %lld\n", N_, M);
    for (int l = 0; l < d_; l++)
        for (int i = 0; i < k_; i++)
            for (int g = 0; g < G_; g++)
                printf("%d %d\n", i * G_ + g, (k_ + lay[l][i]) * G_ + gmul(g, sv[l][i]));
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions and glue.
# ----------------------------------------------------------------------------

_KS = (1, 2, 3, 4, 5)


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


def _lift_in_c(d, D, k, m, k2, r, seconds, seed):
    """Run the C lift annealer for one (k, group) pair; returns (n, edges) or (0, [])."""
    out = lib.run_c(C_LIFT, [d, D, seed, f"{seconds:.2f}", k, m, k2, r],
                    timeout=seconds + 15.0)
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

    # Lift search in C, with a bandit over the base size k.
    lift_end = t0 + max(1.0, min(0.9 * time_limit, time_limit - 6.0))
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    failures = 0
    while failures < 3:
        remain = lift_end - time.monotonic()
        if remain < 1.0:
            break
        k = pick_k()
        base = best[0] // (2 * k)
        target = max(2, base + 1 + rng.randrange(0, max(2, base // 8 + 1)))
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        if 2 * k * m * k2 <= best[0]:
            continue
        slice_s = min(remain, max(1.5, min(8.0, remain / 4.0)))
        trials[k] += 1
        try:
            n, e = _lift_in_c(d, D, k, m, k2, r, slice_s, rng.randrange(1, 1 << 30))
        except Exception:
            failures += 1
            continue
        if n > 0:
            wins[k] += 1
            consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
