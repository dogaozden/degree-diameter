import time

import lib


# ----------------------------------------------------------------------------
# New construction: cyclic voltage lifts of small bipartite base multigraphs.
#
# A base graph has K blocks per side and is d-regular: layer l is a perfect
# matching given by a permutation perm[l] (A-block i -> B-block perm[l][i]),
# carrying a voltage S[l][i] in Z_M. The lift has 2*K*M vertices (block b,
# offset g) = b*M + g, and A-block i joins (i,g) to (K+j, g+S) for each layer.
# Since Z_M acts transitively within each block, the diameter check needs only
# one BFS per block (2K BFS runs), which makes a C annealer over voltages and
# layer permutations fast. Parallel darts with equal voltage are penalised.
# The ladder raises M for a fixed K whenever a lift is found, and rotates K
# over 2..10 when an attempt fails.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXK 12
#define MAXD 16
#define MAXM 4096
#define MAXV (2 * MAXK * MAXM)
#define PEN 50

typedef uint64_t u64;
static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int n) { return (int)(rnd() % (u64)n); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int d_, D_, K, M;
static int perm[MAXD][MAXK], invp[MAXD][MAXK], S[MAXD][MAXK];
static int nbr[MAXV * MAXD];
static int vis[MAXV], dd[MAXV], que[MAXV];
static int stamp = 0;
static int bestN = 0, bestK = 0, bestM = 0;
static int bestPerm[MAXD][MAXK], bestS[MAXD][MAXK];

static void rebuild_inv(void) {
    for (int l = 0; l < d_; l++)
        for (int i = 0; i < K; i++)
            invp[l][perm[l][i]] = i;
}

static void build_nbr(void) {
    for (int b = 0; b < K; b++)
        for (int g = 0; g < M; g++) {
            int v = b * M + g;
            for (int l = 0; l < d_; l++) {
                int j = perm[l][b];
                nbr[(size_t)v * d_ + l] = (K + j) * M + (g + S[l][b]) % M;
            }
        }
    for (int j = 0; j < K; j++)
        for (int h = 0; h < M; h++) {
            int v = (K + j) * M + h;
            for (int l = 0; l < d_; l++) {
                int i = invp[l][j];
                int g = ((h - S[l][i]) % M + M) % M;
                nbr[(size_t)v * d_ + l] = i * M + g;
            }
        }
}

/* Cost = unreached (source, vertex) pairs over the 2K block sources, plus a
   penalty per duplicate dart. Zero means the lift is a valid simple graph. */
static long long cost_fn(void) {
    int N = 2 * K * M;
    long long tot = 0;
    for (int i = 0; i < K; i++)
        for (int l = 0; l < d_; l++)
            for (int q = l + 1; q < d_; q++)
                if (perm[l][i] == perm[q][i] && S[l][i] == S[q][i]) tot += PEN;
    for (int s = 0; s < 2 * K; s++) {
        int src = s * M;
        stamp++;
        int h = 0, t = 0, cnt = 1;
        que[t++] = src;
        vis[src] = stamp;
        dd[src] = 0;
        while (h < t) {
            int v = que[h++];
            if (dd[v] >= D_) continue;
            const int *nb = nbr + (size_t)v * d_;
            for (int l = 0; l < d_; l++) {
                int w = nb[l];
                if (vis[w] != stamp) {
                    vis[w] = stamp;
                    dd[w] = dd[v] + 1;
                    que[t++] = w;
                    cnt++;
                }
            }
        }
        tot += N - cnt;
    }
    return tot;
}

static void randomize(void) {
    for (int l = 0; l < d_; l++) {
        for (int i = 0; i < K; i++) perm[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = perm[l][i]; perm[l][i] = perm[l][j]; perm[l][j] = t;
        }
        for (int i = 0; i < K; i++) S[l][i] = rint_(M);
    }
    rebuild_inv();
}

static int anneal(double budget) {
    rebuild_inv();
    build_nbr();
    long long cur = cost_fn();
    clock_t c0 = clock();
    double T = 5.0;
    long long it = 0;
    while (cur > 0) {
        if ((it & 31) == 0) {
            double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
            if (el >= budget) return 0;
            double frac = el / budget;
            T = 5.0 * pow(0.04, frac);
        }
        it++;
        if (rdbl() < 0.85) {
            int l = rint_(d_), i = rint_(K);
            int old = S[l][i];
            int nv = rint_(M);
            if (nv == old) continue;
            S[l][i] = nv;
            build_nbr();
            long long nc = cost_fn();
            if (nc <= cur || rdbl() < exp(-(double)(nc - cur) / T)) {
                cur = nc;
            } else {
                S[l][i] = old;
                build_nbr();
            }
        } else {
            if (K < 2) continue;
            int l = rint_(d_), i1 = rint_(K), i2 = rint_(K - 1);
            if (i2 >= i1) i2++;
            int a = perm[l][i1], b = perm[l][i2];
            perm[l][i1] = b; perm[l][i2] = a;
            invp[l][a] = i2; invp[l][b] = i1;
            build_nbr();
            long long nc = cost_fn();
            if (nc <= cur || rdbl() < exp(-(double)(nc - cur) / T)) {
                cur = nc;
            } else {
                perm[l][i1] = a; perm[l][i2] = b;
                invp[l][a] = i1; invp[l][b] = i2;
                build_nbr();
            }
        }
    }
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double limit = atof(argv[4]);
    if (d_ < 1 || d_ > MAXD || D_ < 1) { printf("0 0\n"); return 0; }

    static const int Ks[] = {2, 3, 4, 5, 6, 7, 8, 9, 10};
    const int nK = 9;
    int idx = 0;
    double attempt = limit / 20.0;
    if (attempt < 0.5) attempt = 0.5;
    if (attempt > 5.0) attempt = 5.0;

    clock_t start = clock();
    while (1) {
        double el = (double)(clock() - start) / CLOCKS_PER_SEC;
        double remain = limit - el;
        if (remain < 0.3) break;
        double budget = attempt < remain ? attempt : remain;

        K = Ks[idx];
        int Mt = bestN / (2 * K) + 1;
        if (Mt < 2) Mt = 2;
        if (Mt > MAXM) break;
        M = Mt;
        randomize();
        if (anneal(budget)) {
            bestN = 2 * K * M;
            bestK = K;
            bestM = M;
            memcpy(bestPerm, perm, sizeof(perm));
            memcpy(bestS, S, sizeof(S));
        } else {
            idx = (idx + 1) % nK;
        }
    }

    if (bestN == 0) { printf("0 0\n"); return 0; }

    K = bestK; M = bestM;
    memcpy(perm, bestPerm, sizeof(perm));
    memcpy(S, bestS, sizeof(S));
    rebuild_inv();
    build_nbr();
    int cnt = 0;
    for (int v = 0; v < K * M; v++) cnt += d_;
    printf("%d %d\n", bestN, cnt);
    for (int v = 0; v < K * M; v++)
        for (int l = 0; l < d_; l++)
            printf("%d %d\n", v, nbr[(size_t)v * d_ + l]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python glue and the exact projective-plane construction for D = 3.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for every D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best  # exact Moore-type record, calibration case

    # Main search: C voltage-lift annealer, leaving a margin for compile time.
    budget = time_limit - (time.monotonic() - t0) - 6.0
    if budget >= 1.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                            stdin_graph=None, timeout=budget + 20.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass  # keep the valid fallback

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
