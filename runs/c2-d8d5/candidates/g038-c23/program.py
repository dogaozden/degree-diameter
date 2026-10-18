import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing over bi-Cayley lifts.
#
# The graph is a lift of a bipartite base with k vertices per side over the
# semidirect product G = Z_m x| Z_k2 (element a*k2+b, product (a,b)(c,e) =
# (a + r^b c, b + e)). Side A vertex i and side B vertex j are joined by darts
# with voltages s: (i,x) ~ (k+j, x*s). Each layer l is a permutation sig_l of
# the k base vertices, with one voltage per A vertex, so the lift is d-regular.
#
# Left multiplication by G is an automorphism group acting semiregularly on
# each fibre, so distances from (b,x) to (c,y) equal distances from (b,e) to
# (c, x^-1 y). Only 2k BFS runs (one per base vertex) are needed per cost
# evaluation. The cost is the number of unreached pairs plus a penalty per
# duplicate dart; zero means a valid simple d-regular bipartite graph with
# diameter <= D. Moves change one voltage or swap two entries in a layer.
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

static int M_, K2_, K_, D_, d_, G_, NV_;
static long long pw_[64];
static int *mulT, *invT, *sig, *S, *nbr, *dist, *qu;

static int gmul_raw(int x, int y) {
    int a = x / K2_, b = x % K2_, c = y / K2_, e = y % K2_;
    long long aa = ((long long)a + pw_[b] * (long long)c) % M_;
    return (int)(aa * K2_ + (b + e) % K2_);
}

static void build_nbr(void) {
    for (int l = 0; l < d_; l++) {
        for (int i = 0; i < K_; i++) {
            int j = sig[l * K_ + i];
            int s = S[l * K_ + i];
            int si = invT[s];
            for (int x = 0; x < G_; x++) {
                nbr[(size_t)(i * G_ + x) * d_ + l] = (K_ + j) * G_ + mulT[x * G_ + s];
                nbr[(size_t)((K_ + j) * G_ + x) * d_ + l] = i * G_ + mulT[x * G_ + si];
            }
        }
    }
}

static int dupcount(void) {
    int c = 0;
    for (int i = 0; i < K_; i++)
        for (int l = 0; l < d_; l++)
            for (int l2 = l + 1; l2 < d_; l2++)
                if (sig[l * K_ + i] == sig[l2 * K_ + i] && S[l * K_ + i] == S[l2 * K_ + i])
                    c++;
    return c;
}

static long long unreached(void) {
    long long tot = 0;
    for (int b = 0; b < 2 * K_; b++) {
        for (int v = 0; v < NV_; v++) dist[v] = -1;
        int src = b * G_;
        int h = 0, t = 0;
        qu[t++] = src;
        dist[src] = 0;
        while (h < t) {
            int v = qu[h++];
            if (dist[v] >= D_) continue;
            const int *nb = nbr + (size_t)v * d_;
            for (int l = 0; l < d_; l++) {
                int u = nb[l];
                if (dist[u] < 0) { dist[u] = dist[v] + 1; qu[t++] = u; }
            }
        }
        tot += NV_ - t;
    }
    return tot;
}

static long long total_cost(void) {
    return unreached() + 30LL * (long long)dupcount();
}

static void output_graph(void) {
    long long m = (long long)K_ * G_ * d_;
    printf("%d %lld\n", NV_, m);
    for (int i = 0; i < K_; i++)
        for (int x = 0; x < G_; x++) {
            int v = i * G_ + x;
            for (int l = 0; l < d_; l++)
                printf("%d %d\n", v, nbr[(size_t)v * d_ + l]);
        }
}

int main(int argc, char **argv) {
    if (argc < 9) { printf("0 0\n"); return 0; }
    M_ = atoi(argv[1]);
    K2_ = atoi(argv[2]);
    long long R = atoll(argv[3]);
    K_ = atoi(argv[4]);
    d_ = atoi(argv[5]);
    D_ = atoi(argv[6]);
    double limit = atof(argv[7]);
    rs ^= (u64)strtoull(argv[8], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;

    if (M_ < 1 || K2_ < 1 || K2_ > 64 || K_ < 1 || K_ > 64 || d_ < 1 || d_ > 64 || D_ < 1) {
        printf("0 0\n");
        return 0;
    }
    G_ = M_ * K2_;
    if (G_ > 2000) { printf("0 0\n"); return 0; }
    NV_ = 2 * K_ * G_;
    if (NV_ > 40000) { printf("0 0\n"); return 0; }

    long long rr = ((R % M_) + M_) % M_;
    pw_[0] = 1 % M_;
    for (int t = 1; t < K2_; t++) pw_[t] = (pw_[t - 1] * rr) % M_;
    if ((pw_[K2_ - 1] * rr) % M_ != 1 % M_) { printf("0 0\n"); return 0; }

    mulT = malloc(sizeof(int) * (size_t)G_ * G_);
    invT = malloc(sizeof(int) * (size_t)G_);
    sig = malloc(sizeof(int) * (size_t)d_ * K_);
    S = malloc(sizeof(int) * (size_t)d_ * K_);
    nbr = malloc(sizeof(int) * (size_t)NV_ * d_);
    dist = malloc(sizeof(int) * (size_t)NV_);
    qu = malloc(sizeof(int) * (size_t)NV_);
    if (!mulT || !invT || !sig || !S || !nbr || !dist || !qu) { printf("0 0\n"); return 0; }

    for (int x = 0; x < G_; x++)
        for (int y = 0; y < G_; y++)
            mulT[x * G_ + y] = gmul_raw(x, y);
    for (int x = 0; x < G_; x++) {
        invT[x] = -1;
        for (int y = 0; y < G_; y++)
            if (mulT[x * G_ + y] == 0) { invT[x] = y; break; }
        if (invT[x] < 0) { printf("0 0\n"); return 0; }
    }

    for (int l = 0; l < d_; l++) {
        for (int i = 0; i < K_; i++) sig[l * K_ + i] = i;
        for (int i = K_ - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = sig[l * K_ + i];
            sig[l * K_ + i] = sig[l * K_ + j];
            sig[l * K_ + j] = t;
        }
    }
    for (int i = 0; i < d_ * K_; i++) S[i] = rint_(G_);

    clock_t start = clock();
    build_nbr();
    long long cur = total_cost();
    if (cur == 0) { output_graph(); return 0; }

    const double T0 = 50.0, T1 = 0.5;
    while (1) {
        double el = (double)(clock() - start) / CLOCKS_PER_SEC;
        if (el >= limit) break;
        double T = T0 * pow(T1 / T0, el / limit);

        int kind = 0, idx = -1, oldv = 0, l = -1, i1 = -1, i2 = -1;
        if (K_ < 2 || rdbl() < 0.6) {
            idx = rint_(d_ * K_);
            oldv = S[idx];
            int nv = rint_(G_);
            if (nv == oldv) continue;
            S[idx] = nv;
            kind = 0;
        } else {
            l = rint_(d_);
            i1 = rint_(K_);
            i2 = rint_(K_);
            if (i1 == i2) continue;
            int t = sig[l * K_ + i1];
            sig[l * K_ + i1] = sig[l * K_ + i2];
            sig[l * K_ + i2] = t;
            kind = 1;
        }

        build_nbr();
        long long nc = total_cost();
        long long delta = nc - cur;
        if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
            cur = nc;
            if (cur == 0) { output_graph(); return 0; }
        } else {
            if (kind == 0) {
                S[idx] = oldv;
            } else {
                int t = sig[l * K_ + i1];
                sig[l * K_ + i1] = sig[l * K_ + i2];
                sig[l * K_ + i2] = t;
            }
            build_nbr();
        }
    }
    printf("0 0\n");
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python glue: constructions, group sampling, and budgeted C lift searches.
# ----------------------------------------------------------------------------

_KS = (1, 2, 3, 4, 5, 6, 7, 8)
_GMAX = 2000


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


def _run_lift(m, k2, r, k, d, D, seconds, seed):
    """Run the C lift annealer; return (n, edges) if it found a valid lift, else None."""
    out = lib.run_c(C_SOURCE, [m, k2, r, k, d, D, f"{seconds:.2f}", seed],
                    stdin_graph=None, timeout=seconds + 15.0)
    n, edges = lib.parse_graph_text(out)
    if n <= 0 or not edges:
        return None
    return n, edges


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

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best  # exact Moore-type construction; calibration case

    fallback = best

    # Bi-Cayley lift search in C, with a bandit over base sizes k.
    lift_end = t0 + max(1.0, 0.85 * time_limit - 2.0)
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.25:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while True:
        remaining = lift_end - time.monotonic()
        if remaining < 1.0:
            break
        k = pick_k()
        base = best[0] // (2 * k)
        target = max(2, base + 1 + rng.randrange(0, max(2, base // 16 + 1)))
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        G = m * k2
        if G > _GMAX or 2 * k * G <= best[0]:
            continue
        seconds = min(remaining - 0.5, 5.0)
        trials[k] += 1
        try:
            res = _run_lift(m, k2, r, k, d, D, seconds, rng.randrange(1, 1 << 30))
        except Exception:
            res = None
        if res is not None:
            wins[k] += 1
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        return fallback
    return best
