import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bi-Cayley (group-voltage) lift search over semidirect products
# Z_m x| Z_k2. The base graph has k vertices per side and d "layers", each a
# permutation of the k sides with an element of the group as voltage. Every
# vertex has degree exactly d. The lift is invariant under left translation
# by the group, so the diameter check only needs BFS from the k+k identity
# vertices. Reachability is held as a 2k-bit mask per vertex, so one
# evaluation is D rounds of OR over the neighbour lists. Cost is the number of
# unreached (source, vertex) pairs plus a penalty for duplicate darts.
# Zero cost means a valid graph. The engine keeps the largest valid lift
# found above the target size and grows the target as it succeeds.
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

#define MAXD 16
#define MAXK 16
#define NMAX 80000
#define MAXE 1000000
#define PEN 1000LL

static int d_, D_, kmax_;
static int k_, G_, m_, k2_, N_;
static int pw[64];
static int *nbr;
static int perm[MAXD * MAXK];
static int svol[MAXD * MAXK];
static u64 *bufA, *bufB, *fin;
static int *bestEu, *bestEv;
static int best_n = 0, best_m = 0;
static double limit_;
static clock_t c0_;

static int gcd_(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }

static long long powmod(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

/* Element a*k2+b of Z_m x| Z_k2 with (a,b)(c,e) = (a + r^b c, b + e). */
static int gmul(int x, int y) {
    int a = x / k2_, b = x % k2_;
    int c = y / k2_, e = y % k2_;
    int na = (int)((a + (long long)pw[b] * c) % m_);
    int nb = (b + e) % k2_;
    return na * k2_ + nb;
}

static int ginv(int x) {
    int a = x / k2_, b = x % k2_;
    int nb = (k2_ - b) % k2_;
    long long t = ((long long)pw[nb] * a) % m_;
    int na = (int)(((long long)m_ - t) % m_);
    return na * k2_ + nb;
}

/* Rewrite the neighbour lists of layer l. A block i at layer l joins B block
   perm[l][i] with voltage svol[l][i]: (A_i, x) ~ (B_j, x*s). */
static void setlayer(int l) {
    int k = k_, G = G_;
    for (int i = 0; i < k; i++) {
        int j = perm[l * MAXK + i], s = svol[l * MAXK + i];
        int ai = i * G, bj = (k + j) * G;
        int si = ginv(s);
        for (int x = 0; x < G; x++) {
            nbr[l * NMAX + ai + x] = bj + gmul(x, s);
            nbr[l * NMAX + bj + x] = ai + gmul(x, si);
        }
    }
}

/* Returns the number of unreached (source, vertex) pairs. Leaves the final masks in fin. */
static long long evalcost(void) {
    int N = N_, k = k_, G = G_, d = d_;
    u64 *cur = bufA, *nxt = bufB;
    int nsrc = 2 * k;
    for (int v = 0; v < N; v++) cur[v] = 0;
    for (int b = 0; b < nsrc; b++) cur[b * G] = 1ULL << b;
    for (int t = 0; t < D_; t++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            u64 x = cur[v];
            for (int l = 0; l < d; l++) x |= cur[nbr[l * NMAX + v]];
            nxt[v] = x;
            if (x != cur[v]) changed = 1;
        }
        u64 *tmp = cur; cur = nxt; nxt = tmp;
        if (!changed) break;
    }
    long long sum = 0;
    for (int v = 0; v < N; v++) sum += __builtin_popcountll(cur[v]);
    fin = cur;
    return (long long)nsrc * N - sum;
}

/* Number of repeated (block i, B block, voltage) darts, which would create multi-edges. */
static int dupcount(void) {
    int c = 0;
    for (int i = 0; i < k_; i++)
        for (int l1 = 0; l1 < d_; l1++)
            for (int l2 = l1 + 1; l2 < d_; l2++)
                if (perm[l1 * MAXK + i] == perm[l2 * MAXK + i] &&
                    svol[l1 * MAXK + i] == svol[l2 * MAXK + i])
                    c++;
    return c;
}

static int time_up(void) {
    return (double)(clock() - c0_) / CLOCKS_PER_SEC >= limit_;
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    limit_ = atof(argv[4]);
    int minN = argc > 5 ? atoi(argv[5]) : 0;
    kmax_ = argc > 6 ? atoi(argv[6]) : 6;
    if (kmax_ > MAXK) kmax_ = MAXK;
    if (d_ < 2 || d_ > MAXD || D_ < 2 || kmax_ < 1) { printf("0 0\n"); return 0; }

    nbr = malloc(sizeof(int) * MAXD * NMAX);
    bufA = malloc(sizeof(u64) * NMAX);
    bufB = malloc(sizeof(u64) * NMAX);
    bestEu = malloc(sizeof(int) * MAXE);
    bestEv = malloc(sizeof(int) * MAXE);
    if (!nbr || !bufA || !bufB || !bestEu || !bestEv) { printf("0 0\n"); return 0; }

    static const int K2S[13] = {1, 1, 1, 2, 2, 2, 3, 4, 5, 6, 8, 10, 12};
    const int ITERS = 4000;
    const double T1 = 0.2;
    c0_ = clock();

    while (!time_up()) {
        int cur = minN > best_n ? minN : best_n;
        int k = 1 + rint_(kmax_);
        int Gmin = cur / (2 * k) + 1;
        int Gt = Gmin + rint_(Gmin / 8 + 2);
        int k2 = K2S[rint_(13)];
        int m = (Gt + k2 - 1) / k2;
        if (m < 2) m = 2;
        if (k2 > 1 && m < 3) continue;

        int r = 1;
        if (k2 > 1) {
            r = -1;
            if (k2 == 2 && rint_(2) == 0) r = m - 1;
            for (int tr = 0; r < 0 && tr < 80; tr++) {
                int c = 2 + rint_(m - 2);
                if (gcd_(c, m) == 1 && powmod(c, k2, m) == 1 % m) r = c;
            }
            if (r < 0) continue;
        }

        m_ = m; k2_ = k2; G_ = m * k2; k_ = k; N_ = 2 * k * G_;
        if (N_ > NMAX) continue;
        pw[0] = 1 % m;
        for (int t = 1; t < k2; t++) pw[t] = (int)((long long)pw[t - 1] * r % m);

        for (int l = 0; l < d_; l++) {
            int p[MAXK];
            for (int i = 0; i < k; i++) p[i] = i;
            for (int i = k - 1; i > 0; i--) {
                int j = rint_(i + 1);
                int t = p[i]; p[i] = p[j]; p[j] = t;
            }
            for (int i = 0; i < k; i++) {
                perm[l * MAXK + i] = p[i];
                svol[l * MAXK + i] = rint_(G_);
            }
            setlayer(l);
        }

        long long cost = evalcost() + PEN * dupcount();
        long long cstart = cost > 0 ? cost : 1;
        double T0 = 0.05 * (double)cstart;
        if (T0 < 1.0) T0 = 1.0;
        int last_imp = 0;
        long long bestc = cost;
        u64 full = (1ULL << (2 * k)) - 1;

        for (int t = 0; t < ITERS && cost > 0; t++) {
            if ((t & 31) == 0 && time_up()) break;
            if (t - last_imp > 1200) break;
            double T = T0 * pow(T1 / T0, (double)t / ITERS);

            if (k >= 2 && rdbl() < 0.2) {
                int l = rint_(d_);
                int i1 = rint_(k), i2 = rint_(k - 1);
                if (i2 >= i1) i2++;
                int *p1 = &perm[l * MAXK + i1], *p2 = &perm[l * MAXK + i2];
                int tmp = *p1; *p1 = *p2; *p2 = tmp;
                setlayer(l);
                long long c2 = evalcost() + PEN * dupcount();
                if (c2 <= cost || rdbl() < exp(-(double)(c2 - cost) / T)) {
                    cost = c2;
                    if (cost < bestc) { bestc = cost; last_imp = t; }
                } else {
                    tmp = *p1; *p1 = *p2; *p2 = tmp;
                    setlayer(l);
                }
                continue;
            }

            int l = rint_(d_), i = rint_(k);
            if (rdbl() < 0.5) {
                int v = -1;
                for (int tr = 0; tr < 30; tr++) {
                    int w = rint_(N_);
                    if (fin[w] != full) { v = w; break; }
                }
                if (v >= 0) {
                    int b = v / G_;
                    if (b < k) {
                        i = b;
                    } else {
                        int j = b - k;
                        l = rint_(d_);
                        for (int ii = 0; ii < k; ii++)
                            if (perm[l * MAXK + ii] == j) { i = ii; break; }
                    }
                }
            }
            int old = svol[l * MAXK + i];
            int nw = rint_(G_);
            if (nw == old) continue;
            svol[l * MAXK + i] = nw;
            setlayer(l);
            long long c2 = evalcost() + PEN * dupcount();
            if (c2 <= cost || rdbl() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
                if (cost < bestc) { bestc = cost; last_imp = t; }
            } else {
                svol[l * MAXK + i] = old;
                setlayer(l);
            }
        }

        if (cost == 0 && N_ > best_n && (long long)k_ * G_ * d_ <= MAXE) {
            int mc = 0;
            for (int v = 0; v < k_ * G_; v++)
                for (int l = 0; l < d_; l++) {
                    bestEu[mc] = v;
                    bestEv[mc] = nbr[l * NMAX + v];
                    mc++;
                }
            best_n = N_;
            best_m = mc;
        }
    }

    if (best_n == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", best_n, best_m);
    for (int i = 0; i < best_m; i++) printf("%d %d\n", bestEu[i], bestEv[i]);
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


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    if not lib.is_valid(best[0], best[1], d, D):
        best = (1, [])

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact construction for D = 3 (calibration case): return immediately when optimal.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    # K_{d,d} is already optimal for D = 2.
    if D == 2 or d > 16:
        return best

    # Group-voltage lift search in C, leaving a margin for compile and overhead.
    remaining = time_limit - (time.monotonic() - t0) - 6.0
    if remaining >= 2.0:
        try:
            out = lib.run_c(
                C_SOURCE,
                [d, D, rng.randrange(1, 1 << 30), f"{remaining:.2f}", best[0], 6],
                timeout=remaining + 5.0,
            )
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass  # keep the valid fallback

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
