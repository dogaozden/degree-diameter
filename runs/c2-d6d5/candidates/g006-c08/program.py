import time

import lib


C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

/* Engine: bipartite Haar-type graphs H(G,S) over semidirect groups G = Z_m x| Z_k2.
   A_x ~ B_y iff y = x*s for some s in S (|S| = d, so the graph is d-regular, order 2|G|).
   Left translation is an automorphism, so the diameter test reduces to two BFS runs,
   from A_0 and from B_0. Search over S by simulated annealing; no voltage lifts of a
   multi-vertex base are used. */

typedef uint64_t u64;
#define GMAX 1100
#define MAXD 16

static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int n) { return (int)(rnd() % (u64)n); }
static double rndu(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}
static int gcd_i(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }
static long long powmod(long long b, int e, long long m) {
    long long r = 1 % m; b %= m;
    while (e > 0) { if (e & 1) r = r * b % m; b = b * b % m; e >>= 1; }
    return r;
}

static int d_, D_, G_;
static int MT[GMAX * GMAX];
static int INV[GMAX];
static int S[MAXD];
static int inS[GMAX];
static int nbr[2 * GMAX * MAXD];
static int dist_[2 * GMAX];
static int qu[2 * GMAX];

static int build_group(int m, int k2, int r) {
    int G = m * k2;
    if (G > GMAX || G < 2) return 0;
    G_ = G;
    int pw[64];
    pw[0] = 1 % m;
    for (int t = 1; t < k2; t++) pw[t] = (int)((long long)pw[t - 1] * r % m);
    for (int x = 0; x < G; x++) {
        int a = x / k2, b = x % k2;
        for (int y = 0; y < G; y++) {
            int c = y / k2, e = y % k2;
            int aa = (int)((a + (long long)pw[b] * c) % m);
            MT[x * G + y] = aa * k2 + (b + e) % k2;
        }
    }
    for (int x = 0; x < G; x++) {
        INV[x] = -1;
        for (int y = 0; y < G; y++)
            if (MT[x * G + y] == 0) { INV[x] = y; break; }
        if (INV[x] < 0) return 0;
    }
    return 1;
}

static void build_adj(void) {
    int G = G_, d = d_;
    for (int x = 0; x < G; x++)
        for (int j = 0; j < d; j++) {
            nbr[x * d + j] = G + MT[x * G + S[j]];                 /* A_x -> B_{x s} */
            nbr[(G + x) * d + j] = MT[x * G + INV[S[j]]];          /* B_x -> A_{x s^-1} */
        }
}

static int bfs_bad(int src) {
    int N = 2 * G_, d = d_;
    for (int v = 0; v < N; v++) dist_[v] = -1;
    int h = 0, t = 0;
    dist_[src] = 0;
    qu[t++] = src;
    while (h < t) {
        int v = qu[h++];
        if (dist_[v] >= D_) continue;
        for (int j = 0; j < d; j++) {
            int u = nbr[v * d + j];
            if (dist_[u] < 0) { dist_[u] = dist_[v] + 1; qu[t++] = u; }
        }
    }
    return N - t;
}

static long long cost_of(void) {
    build_adj();
    return (long long)bfs_bad(0) + (long long)bfs_bad(G_);
}

static int anneal(double tend, int iters) {
    int G = G_, d = d_;
    for (int x = 0; x < G; x++) inS[x] = 0;
    for (int j = 0; j < d; j++) {
        int e;
        do e = rndi(G); while (inS[e]);
        inS[e] = 1;
        S[j] = e;
    }
    long long cost = cost_of();
    for (int it = 0; it < iters && cost > 0; it++) {
        if ((it & 255) == 0 && now() > tend) break;
        double T = 2.0 * (1.0 - (double)it / iters) + 0.05;
        int j = rndi(d);
        int e;
        do e = rndi(G); while (inS[e]);
        int old = S[j];
        inS[old] = 0; inS[e] = 1; S[j] = e;
        long long c2 = cost_of();
        if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / T)) {
            cost = c2;
        } else {
            inS[e] = 0; inS[old] = 1; S[j] = old;
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
    int minG = argc > 5 ? atoi(argv[5]) : 20;
    if (d_ < 3 || D_ < 3 || d_ > MAXD) { printf("0 0\n"); return 0; }
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    double tend = now() + tl;
    double slice = tl / 12.0;
    if (slice < 1.0) slice = 1.0;
    static const int K2s[10] = {1, 2, 3, 4, 5, 6, 7, 8, 10, 12};

    int bestN = 0, bM = 0, bK = 0, bR = 0;
    int bestS[MAXD];
    int minGroup = minG;
    if (minGroup < d_ + 1) minGroup = d_ + 1;

    while (now() < tend) {
        if (minGroup > GMAX) break;
        int k2 = K2s[rndi(10)];
        int Gt = minGroup + rndi(minGroup / 25 + 2);
        int m = (Gt + k2 - 1) / k2;
        if (m < 2) m = 2;
        if (m * k2 > GMAX) continue;
        int cand[GMAX];
        int nc = 0;
        for (int r = 1; r < m; r++)
            if (gcd_i(r, m) == 1 && powmod(r, k2, m) == 1 % m) cand[nc++] = r;
        if (nc == 0) continue;
        int r = cand[rndi(nc)];
        if (!build_group(m, k2, r)) continue;
        if (G_ < d_ + 1) continue;
        double gend = now() + slice;
        if (gend > tend) gend = tend;
        if (anneal(gend, 8000)) {
            int G = G_;
            if (2 * G > bestN) {
                bestN = 2 * G;
                bM = m; bK = k2; bR = r;
                memcpy(bestS, S, sizeof S);
            }
            minGroup = G + 1;
        }
    }

    if (bestN == 0) { printf("0 0\n"); return 0; }
    build_group(bM, bK, bR);
    memcpy(S, bestS, sizeof S);
    build_adj();
    int G = G_, d = d_;
    printf("%d %d\n", 2 * G, G * d);
    for (int x = 0; x < G; x++)
        for (int j = 0; j < d; j++)
            printf("%d %d\n", x, G + MT[x * G + S[j]]);
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

    # Leave a margin for compilation and process start-up.
    budget = max(0.5, min(0.8 * time_limit, time_limit - 10.0))
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), 20],
                        timeout=budget + 6.0)
        n, e = lib.parse_graph_text(out)
        if n > 0:
            consider(n, e)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
