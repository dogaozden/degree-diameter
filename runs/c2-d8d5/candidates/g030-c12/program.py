import time

import lib


# ----------------------------------------------------------------------------
# Bold change: bi-Cayley lift search in C over semidirect products Z_m x| Z_k2.
#
# A lift has 2k base vertices (k left, k right) and d "layers". Layer l sends
# left base i to right base sig[l][i] with voltage vol[l][i] in the group G.
# Each layer is a permutation, so every vertex has degree d. Left multiplication
# by G is an automorphism, so the diameter test only needs BFS from the 2k
# block representatives (b, identity). Simple-graph condition: for each left i,
# the pairs (sig[l][i], vol[l][i]) are distinct over l, which is penalised.
#
# Annealing moves: change one voltage, or swap two right targets within a
# layer. The search climbs: once a valid lift of order N is found, it looks for
# a valid lift with more vertices. Python checks every output with lib.is_valid.
# ----------------------------------------------------------------------------

LIFT_C = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXG 3000
#define MAXK 4
#define PEN 6

typedef uint64_t u64;
static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int n) { return (int)(rnd() % (u64)n); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int d_, D_, k_, G_;
static int *MT = NULL, *IV = NULL;
static int *sig, *vol, *pinv;
static int *dist_, *queue_;
static int nbuf[256];
static int *bestE = NULL;
static int bestM = 0, bestN = 0, found = 0;

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

static long long gcdll(long long a, long long b) {
    while (b) { long long t = a % b; a = b; b = t; }
    return a;
}

/* Semidirect product Z_m x| Z_k2 with r^k2 = 1 mod m. Element (a,b) is coded a*k2+b.
   (a,b)*(c,d) = (a + r^b c, b + d). Identity is code 0. */
static void build_group(int m, int k2, long long r) {
    G_ = m * k2;
    int *pw = malloc(sizeof(int) * (size_t)k2);
    pw[0] = 1 % m;
    for (int t = 1; t < k2; t++) pw[t] = (int)((long long)pw[t - 1] * r % m);
    free(MT);
    free(IV);
    MT = malloc(sizeof(int) * (size_t)G_ * G_);
    IV = malloc(sizeof(int) * (size_t)G_);
    for (int x = 0; x < G_; x++) {
        int a = x / k2, b = x % k2;
        int nb = (k2 - b) % k2;
        long long na = (m - ((long long)pw[nb] * a) % m) % m;
        IV[x] = (int)(na * k2 + nb);
        for (int y = 0; y < G_; y++) {
            int c = y / k2, dd = y % k2;
            long long ra = (a + (long long)pw[b] * c) % m;
            MT[(size_t)x * G_ + y] = (int)(ra * k2 + (b + dd) % k2);
        }
    }
    free(pw);
}

static const int K2S[] = {1, 2, 2, 3, 4, 4, 5, 6, 6, 8, 8, 9, 10, 12, 12, 16, 18, 20, 24, 30, 36};

static int sample_group(int need, int k, int *pm, int *pk2, long long *pr) {
    int k2 = K2S[rint_((int)(sizeof(K2S) / sizeof(K2S[0])))];
    int Gmin = (need + 2 * k - 1) / (2 * k);
    int m = (Gmin + k2 - 1) / k2 + rint_(3);
    if (m < 2) m = 2;
    if (m * k2 > MAXG) return 0;
    long long r = 1;
    if (k2 > 1 && m >= 3) {
        int ok = 0;
        for (int t = 0; t < 300 && !ok; t++) {
            long long c = 2 + rint_(m - 2);
            if (gcdll(c, m) == 1 && powmod(c, k2, m) == 1 % m) { r = c; ok = 1; }
        }
        if (!ok) return 0;
    }
    *pm = m;
    *pk2 = k2;
    *pr = r;
    return 1;
}

/* Neighbours of lift vertex v = block*G + g. Left blocks are 0..k-1, right are k..2k-1. */
static int nbrs_of(int v, int *out) {
    int k = k_, G = G_, d = d_;
    if (v < k * G) {
        int b = v / G, g = v % G;
        for (int l = 0; l < d; l++) {
            int j = sig[l * k + b], s = vol[l * k + b];
            out[l] = (k + j) * G + MT[(size_t)g * G + s];
        }
    } else {
        int j = v / G - k, h = v % G;
        for (int l = 0; l < d; l++) {
            int i = pinv[l * k + j];
            int s = vol[l * k + i];
            out[l] = i * G + MT[(size_t)h * G + IV[s]];
        }
    }
    return d;
}

/* Returns the number of (block representative, vertex) pairs at distance > D_.
   Zero for all representatives means the lift has diameter <= D_.
   dupOut counts repeated (target, voltage) pairs from the same left base vertex. */
static long long evaluate(long long *dupOut) {
    int k = k_, d = d_, G = G_, N = 2 * k * G;
    long long dup = 0;
    for (int i = 0; i < k; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (sig[l1 * k + i] == sig[l2 * k + i] && vol[l1 * k + i] == vol[l2 * k + i]) dup++;
    long long un = 0;
    for (int b = 0; b < 2 * k; b++) {
        for (int x = 0; x < N; x++) dist_[x] = -1;
        int src = b * G;
        int h = 0, t = 0;
        queue_[t++] = src;
        dist_[src] = 0;
        while (h < t) {
            int v = queue_[h++];
            if (dist_[v] >= D_) continue;
            nbrs_of(v, nbuf);
            for (int q = 0; q < d; q++) {
                int u = nbuf[q];
                if (dist_[u] < 0) {
                    dist_[u] = dist_[v] + 1;
                    queue_[t++] = u;
                }
            }
        }
        un += N - t;
    }
    *dupOut = dup;
    return un;
}

static void do_swap(int l, int i1, int i2) {
    int k = k_;
    int *s = sig + l * k;
    int t = s[i1];
    s[i1] = s[i2];
    s[i2] = t;
    pinv[l * k + s[i1]] = i1;
    pinv[l * k + s[i2]] = i2;
}

static int anneal(long long maxIter, double clock_end) {
    int k = k_, d = d_, G = G_;
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < k; i++) sig[l * k + i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = sig[l * k + i];
            sig[l * k + i] = sig[l * k + j];
            sig[l * k + j] = t;
        }
        for (int i = 0; i < k; i++) {
            pinv[l * k + sig[l * k + i]] = i;
            vol[l * k + i] = rint_(G);
        }
    }
    long long dup;
    long long un = evaluate(&dup);
    long long cost = un + PEN * dup;
    const double T0 = 2.0, T1 = 0.05;
    for (long long it = 0; it < maxIter; it++) {
        if ((it & 63) == 0 && (double)clock() / CLOCKS_PER_SEC >= clock_end) return 0;
        if (cost == 0) return 1;
        double T = T0 * pow(T1 / T0, (double)it / (double)maxIter);
        if (k >= 2 && (rnd() & 1)) {
            int l = rint_(d);
            int i1 = rint_(k), i2 = rint_(k - 1);
            if (i2 >= i1) i2++;
            do_swap(l, i1, i2);
            long long dp2;
            long long u2 = evaluate(&dp2);
            long long c2 = u2 + PEN * dp2;
            long long dl = c2 - cost;
            if (dl <= 0 || rdbl() < exp(-(double)dl / T)) cost = c2;
            else do_swap(l, i1, i2);
        } else {
            int idx = rint_(d * k);
            int old = vol[idx];
            int nv = rint_(G);
            if (nv == old) continue;
            vol[idx] = nv;
            long long dp2;
            long long u2 = evaluate(&dp2);
            long long c2 = u2 + PEN * dp2;
            long long dl = c2 - cost;
            if (dl <= 0 || rdbl() < exp(-(double)dl / T)) cost = c2;
            else vol[idx] = old;
        }
    }
    return cost == 0;
}

static void record(void) {
    int k = k_, G = G_, d = d_;
    int N = 2 * k * G;
    int *E = malloc(sizeof(int) * 2 * (size_t)k * G * d);
    int m = 0;
    for (int v = 0; v < k * G; v++) {
        nbrs_of(v, nbuf);
        for (int q = 0; q < d; q++) {
            E[2 * m] = v;
            E[2 * m + 1] = nbuf[q];
            m++;
        }
    }
    free(bestE);
    bestE = E;
    bestM = m;
    bestN = N;
    found = 1;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double tl = atof(argv[4]);
    int need0 = argc > 5 ? atoi(argv[5]) : 0;
    if (d_ < 1 || d_ > 200 || D_ < 1) {
        printf("0 0\n");
        return 0;
    }
    sig = malloc(sizeof(int) * MAXK * d_);
    vol = malloc(sizeof(int) * MAXK * d_);
    pinv = malloc(sizeof(int) * MAXK * d_);
    dist_ = malloc(sizeof(int) * 2 * MAXK * MAXG);
    queue_ = malloc(sizeof(int) * 2 * MAXK * MAXG);
    if (!sig || !vol || !pinv || !dist_ || !queue_) {
        printf("0 0\n");
        return 0;
    }
    bestN = need0;
    double end = tl;
    while ((double)clock() / CLOCKS_PER_SEC < end) {
        int need = bestN + 1;
        if (need > 2 * MAXK * MAXG) break;
        int k = 1 + rint_(MAXK);
        int m, k2;
        long long r;
        if (!sample_group(need, k, &m, &k2, &r)) continue;
        build_group(m, k2, r);
        k_ = k;
        if (anneal(30000, end)) record();
    }
    if (!found) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", bestN, bestM);
    for (int i = 0; i < bestM; i++) printf("%d %d\n", bestE[2 * i], bestE[2 * i + 1]);
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


def _lift_search(d, D, seed, seconds, need_n):
    """Run the C lift annealer; returns (n, edges), possibly (0, [])."""
    out = lib.run_c(LIFT_C, [d, D, seed, f"{seconds:.2f}", need_n],
                    stdin_graph=None, timeout=seconds + 20.0)
    return lib.parse_graph_text(out)


def build(d, D, seed, time_limit):
    t0 = time.monotonic()

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    if not lib.is_valid(best[0], best[1], d, D):
        best = (1, [])

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact or known constructions for D = 3.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best
        if D == 3 and d >= 5 and lib.is_prime_power(d - 2):
            try:
                an, ae = lib.araujo_lopez_graph(d - 2)
                consider(an, ae)
            except Exception:
                pass  # keep the valid fallback

    # Main search: C lift annealer that climbs above the current best order.
    budget = max(1.0, min(0.8 * time_limit, time_limit - 10.0))
    budget -= time.monotonic() - t0
    if budget >= 1.0:
        try:
            n_, e_ = _lift_search(d, D, int(seed), budget, best[0])
            consider(n_, e_)
        except Exception:
            pass  # keep the valid fallback

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
        if not lib.is_valid(best[0], best[1], d, D):
            best = (1, [])
    return best
