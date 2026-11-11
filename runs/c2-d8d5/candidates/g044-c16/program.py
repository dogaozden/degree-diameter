import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: voltage annealer for bi-Cayley lifts over Z_m x| Z_k2.
#
# Graph: base has K vertices per side. The group G = Z_m x| Z_k2 has element
# a*k2+b with (a,b)(c,e) = (a + r^b c, b+e). For each layer l (0..d-1) and
# base vertex i, the dart (i, lay[l][i], S[l][i]) joins A(i,g) to B(j,g*s)
# for all g. Each layer is a permutation, so every vertex has degree d.
#
# New routine: left multiplication by G is an automorphism of every lift, so
# dist((i,g),(j,t)) = dist((i,e),(j,g^-1 t)). The diameter test therefore only
# needs BFS from the 2K block identities (i,e), each in O(N d) time. The state
# is annealed with the number of unreached (source, vertex) pairs plus a penalty
# for repeated darts. The first zero-cost state is printed and the program exits.
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

static int d_, D_, K_, G_;
static int *mt, *ginv, *lay, *ilay, *S, *nbt, *vis, *que;
static int *bk_lay, *bk_ilay, *bk_S;
static int stamp = 0;

/* Neighbour of vertex v in layer l. A-block i is vertices i*G..i*G+G-1,
   B-block j is vertices (K+j)*G..(K+j)*G+G-1. */
static int nb_of(int v, int l) {
    int K = K_, G = G_;
    int KG = K * G;
    if (v < KG) {
        int i = v / G, g = v - i * G;
        int j = lay[l * K + i];
        int s = S[l * K + i];
        return (K + j) * G + mt[g * G + s];
    } else {
        int w = v - KG;
        int j = w / G, t = w - j * G;
        int i = ilay[l * K + j];
        int s = S[l * K + i];
        return i * G + mt[t * G + ginv[s]];
    }
}

static void rebuild_layer(int l) {
    int N = 2 * K_ * G_, d = d_;
    for (int v = 0; v < N; v++) nbt[v * d + l] = nb_of(v, l);
}

/* Returns the number of unreached (source, vertex) pairs; writes the dart-repeat count. */
static long long evaluate(long long *dupout) {
    int K = K_, G = G_, d = d_;
    int N = 2 * K * G;
    long long dup = 0;
    for (int l = 0; l < d; l++)
        for (int i = 0; i < K; i++) {
            int j = lay[l * K + i], s = S[l * K + i];
            for (int l2 = 0; l2 < l; l2++)
                if (lay[l2 * K + i] == j && S[l2 * K + i] == s) { dup++; break; }
        }
    *dupout = dup;
    if (stamp > 1000000000) { memset(vis, 0, sizeof(int) * (size_t)N); stamp = 0; }
    long long cost = 0;
    for (int a = 0; a < 2 * K; a++) {
        stamp++;
        int h = 0, t = 0;
        int src = a * G;
        que[t++] = src;
        vis[src] = stamp;
        int lvl = 0;
        while (h < t && t < N && lvl < D_) {
            int end = t;
            while (h < end) {
                int v = que[h++];
                const int *row = nbt + (size_t)v * d;
                for (int l = 0; l < d; l++) {
                    int u = row[l];
                    if (vis[u] != stamp) { vis[u] = stamp; que[t++] = u; }
                }
            }
            lvl++;
        }
        cost += N - t;
    }
    return cost;
}

static void output_graph(void) {
    int K = K_, G = G_, d = d_;
    int N = 2 * K * G;
    long long m = (long long)K * G * d;
    printf("%d %lld\n", N, m);
    for (int v = 0; v < K * G; v++)
        for (int l = 0; l < d; l++)
            printf("%d %d\n", v, nbt[v * d + l]);
}

int main(int argc, char **argv) {
    if (argc < 9) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double limit = atof(argv[4]);
    int K = atoi(argv[5]), m = atoi(argv[6]), k2 = atoi(argv[7]);
    long long R = atoll(argv[8]);
    int d = d_;
    K_ = K;
    if (d < 1 || D_ < 1 || K < 1 || m < 1 || k2 < 1 || limit <= 0) { printf("0 0\n"); return 0; }
    long long Gll = (long long)m * k2;
    if (Gll > 1500) { printf("0 0\n"); return 0; }
    int G = (int)Gll;
    G_ = G;

    /* powers r^b mod m for b < k2; r^k2 must be 1 mod m */
    long long *pw = malloc(sizeof(long long) * (size_t)k2);
    if (!pw) { printf("0 0\n"); return 0; }
    long long p = 1 % m;
    long long rm = R % m;
    for (int b = 0; b < k2; b++) { pw[b] = p; p = (p * rm) % m; }
    if (p != 1 % m) { printf("0 0\n"); return 0; }

    mt = malloc(sizeof(int) * (size_t)G * (size_t)G);
    ginv = malloc(sizeof(int) * (size_t)G);
    if (!mt || !ginv) { printf("0 0\n"); return 0; }
    for (int x = 0; x < G; x++) {
        int a = x / k2, b = x % k2;
        for (int y = 0; y < G; y++) {
            int c = y / k2, e = y % k2;
            long long aa = ((long long)a + pw[b] * (long long)c) % m;
            mt[x * G + y] = (int)(aa * k2 + (b + e) % k2);
        }
    }
    for (int x = 0; x < G; x++) {
        ginv[x] = -1;
        for (int y = 0; y < G; y++)
            if (mt[x * G + y] == 0) { ginv[x] = y; break; }
        if (ginv[x] < 0) { printf("0 0\n"); return 0; }
    }

    int KG = K * G;
    int N = 2 * KG;
    lay = malloc(sizeof(int) * (size_t)d * K);
    ilay = malloc(sizeof(int) * (size_t)d * K);
    S = malloc(sizeof(int) * (size_t)d * K);
    bk_lay = malloc(sizeof(int) * (size_t)d * K);
    bk_ilay = malloc(sizeof(int) * (size_t)d * K);
    bk_S = malloc(sizeof(int) * (size_t)d * K);
    vis = calloc((size_t)N, sizeof(int));
    que = malloc(sizeof(int) * (size_t)N);
    nbt = malloc(sizeof(int) * (size_t)N * d);
    if (!lay || !ilay || !S || !bk_lay || !bk_ilay || !bk_S || !vis || !que || !nbt) {
        printf("0 0\n");
        return 0;
    }
    size_t sz = sizeof(int) * (size_t)d * K;

    for (int l = 0; l < d; l++) {
        for (int i = 0; i < K; i++) lay[l * K + i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int tmp = lay[l * K + i]; lay[l * K + i] = lay[l * K + j]; lay[l * K + j] = tmp;
        }
        for (int i = 0; i < K; i++) ilay[l * K + lay[l * K + i]] = i;
        for (int i = 0; i < K; i++) S[l * K + i] = rint_(G);
    }
    for (int l = 0; l < d; l++) rebuild_layer(l);

    long long dup = 0;
    long long pen = 8;
    long long ev = evaluate(&dup);
    long long cur = ev + pen * dup;
    if (cur == 0) { output_graph(); return 0; }

    long long c0 = cur > 1 ? cur : 1;
    double T0 = 0.05 * (double)c0;
    if (T0 < 2.0) T0 = 2.0;
    double T1 = 0.3;

    clock_t st = clock();
    while (1) {
        double el = (double)(clock() - st) / CLOCKS_PER_SEC;
        if (el >= limit) break;
        double frac = el / limit;
        double T = T0 * pow(T1 / T0, frac);

        memcpy(bk_lay, lay, sz);
        memcpy(bk_ilay, ilay, sz);
        memcpy(bk_S, S, sz);
        int aff1 = -1, aff2 = -1;

        double x = rdbl();
        if (x < 0.6) {
            int l = rint_(d), i = rint_(K);
            int nv = rint_(G);
            if (nv == S[l * K + i]) continue;
            S[l * K + i] = nv;
            aff1 = l;
        } else if (x < 0.8 && K >= 2) {
            int l = rint_(d);
            int i1 = rint_(K), i2 = rint_(K - 1);
            if (i2 >= i1) i2++;
            int j1 = lay[l * K + i1], j2 = lay[l * K + i2];
            lay[l * K + i1] = j2;
            lay[l * K + i2] = j1;
            ilay[l * K + j2] = i1;
            ilay[l * K + j1] = i2;
            aff1 = l;
        } else if (d >= 2) {
            int l1 = rint_(d), l2 = rint_(d - 1);
            if (l2 >= l1) l2++;
            int i = rint_(K);
            int tmp = S[l1 * K + i]; S[l1 * K + i] = S[l2 * K + i]; S[l2 * K + i] = tmp;
            aff1 = l1;
            aff2 = l2;
        } else {
            continue;
        }

        if (aff1 >= 0) rebuild_layer(aff1);
        if (aff2 >= 0) rebuild_layer(aff2);

        long long nd = 0;
        long long e2 = evaluate(&nd);
        long long nc = e2 + pen * nd;
        long long delta = nc - cur;
        if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
            cur = nc;
            if (cur == 0) { output_graph(); return 0; }
        } else {
            memcpy(lay, bk_lay, sz);
            memcpy(ilay, bk_ilay, sz);
            memcpy(S, bk_S, sz);
            if (aff1 >= 0) rebuild_layer(aff1);
            if (aff2 >= 0) rebuild_layer(aff2);
        }
    }
    printf("0 0\n");
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions and glue.
# ----------------------------------------------------------------------------

_KS = (2, 3, 4, 5, 6, 8, 10)
_K2S = (1, 1, 1, 2, 2, 3, 4, 5, 6, 8, 10)
_GCAP = 1500


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target and r^k2 = 1 mod m, or None."""
    for _ in range(100):
        k2 = rng.choice(_K2S)
        m = max(2, -(-target // k2))
        if k2 == 1:
            return m, 1, 1
        cands = [c for c in range(2, m)
                 if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m]
        if cands:
            return m, k2, rng.choice(cands)
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

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best
    if D == 2:
        return best

    # Voltage-lift search: the C engine anneals lifts over Z_m x| Z_k2 and
    # stops at the first valid one. The target order is raised after each success.
    end = t0 + max(0.3, 0.9 * time_limit - 1.0)
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}
    fails = 0
    while fails < 400:
        remaining = end - time.monotonic()
        if remaining < 1.5:
            break
        if rng.random() < 0.25:
            k = rng.choice(_KS)
        else:
            k = max(_KS, key=lambda kk: (wins[kk] + 1) / (trials[kk] + 2)
                    + 0.05 * rng.random())
        target_n = best[0] + 2 + rng.choice((0, 0, 2, 2 * k))
        target_G = max(2, -(-target_n // (2 * k)))
        g = _sample_group(target_G, rng)
        if g is None:
            fails += 1
            continue
        m, k2, r = g
        if m * k2 > _GCAP:
            fails += 1
            continue
        slice_s = min(remaining - 1.0, max(3.0, 0.35 * remaining))
        if slice_s < 1.0:
            break
        trials[k] += 1
        try:
            out = lib.run_c(C_SOURCE,
                            [d, D, rng.randrange(1, 1 << 30), f"{slice_s:.2f}", k, m, k2, r],
                            timeout=slice_s + 15.0)
            n2, e2 = lib.parse_graph_text(out)
        except Exception as exc:
            if "timeout" in str(exc).lower():
                fails += 1
                continue
            break  # compile or runtime failure: keep the fallback
        if n2 > 0 and consider(n2, e2):
            wins[k] += 1
        else:
            fails += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
