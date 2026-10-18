import time

import lib


C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

/* Growth-and-repair search for d-regular bipartite graphs with diameter <= D.
   Start from K_{d,d}. Each step inserts vertex pairs (a', b') that keep
   regularity, then repairs diameter defects by simulated annealing on
   degree-preserving edge swaps. Cost = ordered pairs at distance > D. */

typedef uint64_t u64;

#define MAXD 32
#define MAXN 2048
#define MAXW ((2 * MAXN + 63) / 64)

static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int n) { return (int)(rnd() % (u64)n); }
static double rndu(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}
static int popc(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int d_, D_, N_, W_;
static int adjA[MAXN * MAXD], adjB[MAXN * MAXD];   /* A a -> B b, B b -> A a */
static int sA[MAXN * MAXD], sB[MAXN * MAXD];      /* last valid state */
static int sN;
static int bestA[MAXN * MAXD];
static int bestN = 0;
static u64 RA[MAXN * MAXW], RB[MAXN * MAXW], TA[MAXN * MAXW], TB[MAXN * MAXW];
static u64 *rA = RA, *rB = RB, *tA = TA, *tB = TB;

/* Bit index: A vertex a -> a, B vertex b -> N + b. */
static long long evalcost(void) {
    int N = N_, W = W_, d = d_;
    memset(rA, 0, sizeof(u64) * (size_t)N * W);
    memset(rB, 0, sizeof(u64) * (size_t)N * W);
    for (int a = 0; a < N; a++) {
        int id = a;
        rA[(size_t)a * W + id / 64] |= 1ULL << (id % 64);
    }
    for (int b = 0; b < N; b++) {
        int id = N + b;
        rB[(size_t)b * W + id / 64] |= 1ULL << (id % 64);
    }
    for (int t = 0; t < D_; t++) {
        for (int a = 0; a < N; a++) {
            u64 *dst = tA + (size_t)a * W;
            const u64 *self = rA + (size_t)a * W;
            for (int w = 0; w < W; w++) dst[w] = self[w];
            for (int j = 0; j < d; j++) {
                const u64 *src = rB + (size_t)adjA[a * d + j] * W;
                for (int w = 0; w < W; w++) dst[w] |= src[w];
            }
        }
        for (int b = 0; b < N; b++) {
            u64 *dst = tB + (size_t)b * W;
            const u64 *self = rB + (size_t)b * W;
            for (int w = 0; w < W; w++) dst[w] = self[w];
            for (int j = 0; j < d; j++) {
                const u64 *src = rA + (size_t)adjB[b * d + j] * W;
                for (int w = 0; w < W; w++) dst[w] |= src[w];
            }
        }
        u64 *s1 = rA; rA = tA; tA = s1;
        u64 *s2 = rB; rB = tB; tB = s2;
    }
    long long pop = 0;
    for (size_t i = 0; i < (size_t)N * W; i++) pop += popc(rA[i]) + popc(rB[i]);
    return 4LL * N * N - pop;
}

static int insert_pair(void) {
    int N = N_, d = d_;
    if (N + 1 > MAXN) return 0;
    int xs[MAXD], ys[MAXD], sl[MAXD];
    int ok = 0;
    for (int tr = 0; tr < 200 && !ok; tr++) {
        int k = 0, guard = 0;
        while (k < d && guard < 100000) {
            guard++;
            int x = rndi(N), dup = 0;
            for (int q = 0; q < k; q++) if (xs[q] == x) { dup = 1; break; }
            if (dup) continue;
            int j = rndi(d);
            int y = adjA[x * d + j], dy = 0;
            for (int q = 0; q < k; q++) if (ys[q] == y) { dy = 1; break; }
            if (dy) continue;
            xs[k] = x; ys[k] = y; sl[k] = j; k++;
        }
        if (k == d) ok = 1;
    }
    if (!ok) return 0;
    int an = N, bn = N;   /* new A and new B vertex indices */
    for (int k = 0; k < d; k++) {
        int x = xs[k], y = ys[k], j = sl[k];
        adjA[x * d + j] = bn;
        for (int jj = 0; jj < d; jj++)
            if (adjB[y * d + jj] == x) { adjB[y * d + jj] = an; break; }
        adjA[an * d + k] = y;
        adjB[bn * d + k] = x;
    }
    N_ = N + 1;
    return 1;
}

static int sw_a1, sw_a2, sw_j1, sw_j2, sw_b1, sw_b2;

static int do_swap(void) {
    int N = N_, d = d_;
    int a1 = rndi(N), a2 = rndi(N - 1);
    if (a2 >= a1) a2++;
    int j1 = rndi(d), j2 = rndi(d);
    int b1 = adjA[a1 * d + j1], b2 = adjA[a2 * d + j2];
    if (b1 == b2) return 0;
    for (int j = 0; j < d; j++) {
        if (adjA[a1 * d + j] == b2) return 0;
        if (adjA[a2 * d + j] == b1) return 0;
    }
    adjA[a1 * d + j1] = b2;
    adjA[a2 * d + j2] = b1;
    for (int j = 0; j < d; j++) if (adjB[b1 * d + j] == a1) { adjB[b1 * d + j] = a2; break; }
    for (int j = 0; j < d; j++) if (adjB[b2 * d + j] == a2) { adjB[b2 * d + j] = a1; break; }
    sw_a1 = a1; sw_a2 = a2; sw_j1 = j1; sw_j2 = j2; sw_b1 = b1; sw_b2 = b2;
    return 1;
}

static void undo_swap(void) {
    int d = d_;
    int a1 = sw_a1, a2 = sw_a2, j1 = sw_j1, j2 = sw_j2, b1 = sw_b1, b2 = sw_b2;
    adjA[a1 * d + j1] = b1;
    adjA[a2 * d + j2] = b2;
    for (int j = 0; j < d; j++) if (adjB[b1 * d + j] == a2) { adjB[b1 * d + j] = a1; break; }
    for (int j = 0; j < d; j++) if (adjB[b2 * d + j] == a1) { adjB[b2 * d + j] = a2; break; }
}

static int repair(double tend, int iters) {
    long long cost = evalcost();
    if (cost == 0) return 1;
    double c0 = (double)cost;
    for (int t = 0; t < iters; t++) {
        if ((t & 31) == 0 && now() > tend) break;
        if (!do_swap()) continue;
        long long c2 = evalcost();
        double temp = 0.02 * c0 * (1.0 - (double)t / iters);
        if (temp < 0.3) temp = 0.3;
        if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
            if (cost == 0) return 1;
        } else {
            undo_swap();
        }
    }
    return cost == 0;
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    if (d_ < 3 || D_ < 3 || d_ > MAXD) { printf("0 0\n"); return 0; }
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    double tend = now() + tl;
    int d = d_;
    N_ = d;
    W_ = (2 * N_ + 63) / 64;
    for (int a = 0; a < d; a++)
        for (int j = 0; j < d; j++) {
            adjA[a * d + j] = j;
            adjB[a * d + j] = j;
        }
    bestN = N_;
    memcpy(bestA, adjA, sizeof(int) * (size_t)N_ * d);

    int fails = 0;
    while (now() < tend) {
        sN = N_;
        memcpy(sA, adjA, sizeof(int) * (size_t)N_ * d);
        memcpy(sB, adjB, sizeof(int) * (size_t)N_ * d);
        int s = 1 + N_ / 64;
        int grown = 0;
        for (int q = 0; q < s; q++) {
            if (insert_pair()) grown++;
            else break;
        }
        if (!grown) { fails++; continue; }
        W_ = (2 * N_ + 63) / 64;
        int iters = 600 + 200 * (fails < 20 ? fails : 20);
        if (repair(tend, iters)) {
            fails = 0;
            if (N_ > bestN) {
                bestN = N_;
                memcpy(bestA, adjA, sizeof(int) * (size_t)N_ * d);
            }
        } else {
            fails++;
            N_ = sN;
            memcpy(adjA, sA, sizeof(int) * (size_t)N_ * d);
            memcpy(adjB, sB, sizeof(int) * (size_t)N_ * d);
            W_ = (2 * N_ + 63) / 64;
        }
    }

    int N = bestN;
    printf("%d %d\n", 2 * N, N * d);
    for (int a = 0; a < N; a++)
        for (int j = 0; j < d; j++)
            printf("%d %d\n", a, N + bestA[a * d + j]);
    return 0;
}
'''


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best  # exact optimum

    if d < 3 or D < 3:
        return best

    # New construction: grow a d-regular bipartite graph from K_{d,d} by
    # inserting vertex pairs, then repair diameter defects with annealed swaps.
    budget = max(0.5, min(0.9 * time_limit, time_limit - 6.0))
    elapsed = time.monotonic() - start
    budget = max(0.5, min(budget, time_limit - elapsed - 4.0))
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                        timeout=budget + 3.0)
        n, e = lib.parse_graph_text(out)
        if n > 0:
            consider(n, e)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
