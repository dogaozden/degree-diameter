import time

import lib


# ---------------------------------------------------------------------------
# New construction: bipartite Cayley-double graphs (vertex-transitive).
# Vertices (x, 0) and (x, 1) for x in a group G; (x, 0) ~ (x*s, 1) for s in S,
# |S| = d. Left multiplication is an automorphism, so the diameter test only
# needs BFS from (e,0) and (e,1). Search: group choice (semidirect products
# Z_m x| Z_k), then simulated annealing over the connection set S.
# ---------------------------------------------------------------------------
C_CAY = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

#define GMAX 1200
#define MAXD 12

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
static int INV_[GMAX];
static int S_[MAXD];
static int dist_[2 * GMAX];
static int q_[2 * GMAX];
static int bestG = 0, bestEc = 0;
static int bestE[GMAX * MAXD * 2];

/* Group Z_m x| Z_k2, (a,b)(c,e) = (a + r^b c, b + e), element a*k2+b, identity 0. */
static int build_group(int m, int k2, int r) {
    int G = m * k2;
    if (G > GMAX || G < 2 || k2 > 16) return 0;
    G_ = G;
    int pwr[16];
    pwr[0] = 1 % m;
    for (int t = 1; t < k2; t++) pwr[t] = (int)((long long)pwr[t - 1] * r % m);
    for (int x = 0; x < G; x++) {
        int a = x / k2, b = x % k2;
        for (int y = 0; y < G; y++) {
            int c = y / k2, e = y % k2;
            int aa = (int)((a + (long long)pwr[b] * c) % m);
            MT[x * G + y] = aa * k2 + (b + e) % k2;
        }
    }
    for (int x = 0; x < G; x++)
        for (int y = 0; y < G; y++)
            if (MT[x * G + y] == 0) INV_[x] = y;
    return 1;
}

/* Bounded BFS from (e,0) and (e,1); cost = unreached vertices summed over both sources. */
static long long cost_of(void) {
    int G = G_, d = d_;
    long long bad = 0;
    for (int src = 0; src < 2; src++) {
        for (int v = 0; v < 2 * G; v++) dist_[v] = -1;
        int s0 = src * G;
        int h = 0, t = 0;
        dist_[s0] = 0;
        q_[t++] = s0;
        while (h < t) {
            int v = q_[h++];
            if (dist_[v] >= D_) continue;
            int x = v % G;
            if (v < G) {
                for (int j = 0; j < d; j++) {
                    int w = G + MT[x * G + S_[j]];
                    if (dist_[w] < 0) { dist_[w] = dist_[v] + 1; q_[t++] = w; }
                }
            } else {
                for (int j = 0; j < d; j++) {
                    int w = MT[x * G + INV_[S_[j]]];
                    if (dist_[w] < 0) { dist_[w] = dist_[v] + 1; q_[t++] = w; }
                }
            }
        }
        bad += 2LL * G - t;
    }
    return bad;
}

static void record(int G) {
    int d = d_;
    bestG = G;
    bestEc = G * d;
    int p = 0;
    for (int x = 0; x < G; x++)
        for (int j = 0; j < d; j++) {
            bestE[2 * p] = x;
            bestE[2 * p + 1] = G + MT[x * G + S_[j]];
            p++;
        }
}

/* Anneal the connection set S (distinct elements) on the current group. */
static int anneal(double tend, int iters) {
    int G = G_, d = d_;
    for (int j = 0; j < d; j++) {
        int c, ok;
        do {
            c = rndi(G);
            ok = 1;
            for (int t = 0; t < j; t++) if (S_[t] == c) { ok = 0; break; }
        } while (!ok);
        S_[j] = c;
    }
    long long cur = cost_of();
    if (cur == 0) return 1;
    for (int t = 0; t < iters; t++) {
        if ((t & 255) == 0 && now() > tend) break;
        double T = 1.5 * (1.0 - (double)t / iters) + 0.05;
        int j = rndi(d);
        int c = rndi(G), ok = 1;
        for (int u = 0; u < d; u++) if (S_[u] == c) { ok = 0; break; }
        if (!ok) continue;
        int old = S_[j];
        S_[j] = c;
        long long nc = cost_of();
        if (nc <= cur || rndu() < exp(-(double)(nc - cur) / T)) {
            cur = nc;
            if (cur == 0) return 1;
        } else {
            S_[j] = old;
        }
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 6) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    int minN = atoi(argv[5]);
    if (d_ < 3 || d_ > MAXD || D_ < 2) { printf("0 0\n"); return 0; }
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    double tend = now() + tl;
    static const int K2s[8] = {1, 1, 2, 2, 3, 4, 5, 6};
    static int cand[GMAX + 5];
    int minG = minN / 2;
    if (minG < 3) minG = 3;
    int fails = 0;

    while (now() < tend) {
        if (minG > GMAX) break;
        int G = minG + rndi(minG / 20 + 2);
        if (G > GMAX) G = GMAX;
        int k2 = K2s[rndi(8)];
        if (G % k2) k2 = 1;
        int m = G / k2;
        if (m < 2) continue;
        int nc = 0;
        for (int r = 1; r < m; r++)
            if (gcd_i(r, m) == 1 && powmod(r, k2, m) == 1 % m) cand[nc++] = r;
        if (nc == 0) continue;
        int r = cand[rndi(nc)];
        if (!build_group(m, k2, r)) continue;

        int ok = anneal(tend, 20000);
        if (ok) {
            record(G_);
            fails = 0;
            minG = G_ + G_ / 40 + 1;
        } else {
            fails++;
            if (fails >= 10) {
                fails = 0;
                int nm = minG * 95 / 100;
                int lo = bestG + 1;
                if (lo < 3) lo = 3;
                minG = nm > lo ? nm : lo;
            }
        }
    }

    if (bestG == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", 2 * bestG, bestEc);
    for (int p = 0; p < bestEc; p++) printf("%d %d\n", bestE[2 * p], bestE[2 * p + 1]);
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

    if D == 2 or d < 3:
        return best

    pg = _best_pg(d) if D >= 3 else None
    if pg is not None:
        consider(pg[0], pg[1])
        if D == 3 and lib.is_prime_power(d - 1):
            return best  # exact optimum

    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    try:
        out = lib.run_c(C_CAY, [d, D, seed, round(budget, 2), best_n + 1],
                        timeout=budget + 6.0)
        n, e = lib.parse_graph_text(out)
        if n > 0:
            consider(n, e)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
