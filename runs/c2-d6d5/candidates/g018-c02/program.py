import time

import lib


# ---------------------------------------------------------------------------
# Bi-Cayley search. A bipartite graph on A = G and B = G, with A_g ~ B_{g*s}
# for s in S (|S| = d), over a finite group G = Z_m x| Z_k. Left
# multiplication is an automorphism, so the graph is vertex-transitive on
# each side. Diameter <= D then holds iff BFS from A_1 and from B_1 reaches
# everything within D steps, which makes each evaluation O(|G| d).
# Search: pick random groups of order near the target and anneal over S.
# ---------------------------------------------------------------------------
C_BICAYLEY = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

#define MAXD 16
#define GMAX 1200

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
static int S_[MAXD];
static int dist_[2 * GMAX];
static int que_[2 * GMAX];
static int pwr_[64];
static char inS_[GMAX];
static int cand_[GMAX];
static int bestE[GMAX * MAXD * 2];
static int bestG = 0, bestCount = 0;

/* Group element (a, b) is coded a*k + b, with (a,b)(c,e) = (a + r^b c, b + e). */
static void build_group(int m, int k, int r) {
    int G = m * k;
    G_ = G;
    pwr_[0] = 1 % m;
    for (int t = 1; t < k; t++) pwr_[t] = (int)((long long)pwr_[t - 1] * r % m);
    for (int x = 0; x < G; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < G; y++) {
            int c = y / k, e = y % k;
            int aa = (int)((a + (long long)pwr_[b] * c) % m);
            MT[x * G + y] = aa * k + (b + e) % k;
        }
    }
    for (int x = 0; x < G; x++)
        for (int y = 0; y < G; y++)
            if (MT[x * G + y] == 0) { INV[x] = y; break; }
}

/* Returns the total number of (source, vertex) pairs at distance > D_, for
   sources A_1 (vertex 0) and B_1 (vertex G). Zero iff the diameter is <= D_. */
static long long cost_eval(void) {
    int G = G_, N = 2 * G, d = d_, D = D_;
    long long tot = 0;
    for (int s = 0; s < 2; s++) {
        int src = (s == 0) ? 0 : G;
        for (int v = 0; v < N; v++) dist_[v] = -1;
        int qh = 0, qt = 0, reached = 1;
        dist_[src] = 0;
        que_[qt++] = src;
        while (qh < qt) {
            int v = que_[qh++];
            int dv = dist_[v];
            if (dv >= D) continue;
            if (v < G) {
                for (int j = 0; j < d; j++) {
                    int w = G + MT[v * G + S_[j]];
                    if (dist_[w] < 0) { dist_[w] = dv + 1; que_[qt++] = w; reached++; }
                }
            } else {
                int h = v - G;
                for (int j = 0; j < d; j++) {
                    int w = MT[h * G + INV[S_[j]]];
                    if (dist_[w] < 0) { dist_[w] = dv + 1; que_[qt++] = w; reached++; }
                }
            }
        }
        tot += N - reached;
    }
    return tot;
}

/* Simulated annealing over the connection set S (d distinct group elements). */
static int search_group(double tend, int iters) {
    int G = G_, d = d_;
    memset(inS_, 0, (size_t)G);
    for (int j = 0; j < d;) {
        int x = rndi(G);
        if (!inS_[x]) { inS_[x] = 1; S_[j++] = x; }
    }
    long long cost = cost_eval();
    if (cost == 0) return 1;
    double T0 = 2.0;
    for (int t = 0; t < iters; t++) {
        if ((t & 255) == 0 && now() > tend) break;
        double T = T0 * (1.0 - (double)t / (double)iters) + 0.2;
        int j = rndi(d);
        int x = rndi(G);
        if (inS_[x]) continue;
        int old = S_[j];
        S_[j] = x; inS_[x] = 1; inS_[old] = 0;
        long long c2 = cost_eval();
        if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / T)) {
            cost = c2;
            if (cost == 0) return 1;
        } else {
            S_[j] = old; inS_[x] = 0; inS_[old] = 1;
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
    int Gmin = (minN + 1) / 2;   /* the graph has 2G vertices */
    if (Gmin < d_ + 1) Gmin = d_ + 1;
    static const int Ks[12] = {1, 1, 2, 2, 2, 3, 3, 4, 4, 5, 6, 8};

    while (now() < tend) {
        int k = Ks[rndi(12)];
        int target = Gmin + rndi(6);
        int m = (target + k - 1) / k;
        if (m < 2) m = 2;
        if (m * k > GMAX) continue;
        int nc = 0;
        for (int r = 1; r < m; r++)
            if (gcd_i(r, m) == 1 && powmod(r, k, m) == 1 % m) cand_[nc++] = r;
        if (nc == 0) continue;
        int r = cand_[rndi(nc)];
        build_group(m, k, r);
        if (G_ < d_ + 1) continue;
        int ok = search_group(tend, 10000);
        if (ok) {
            int G = G_;
            for (int g = 0; g < G; g++)
                for (int j = 0; j < d_; j++) {
                    int p = g * d_ + j;
                    bestE[2 * p] = g;
                    bestE[2 * p + 1] = G + MT[g * G + S_[j]];
                }
            bestG = G;
            bestCount = G * d_;
            Gmin = G + 1;
        }
    }

    if (bestG == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", 2 * bestG, bestCount);
    for (int p = 0; p < bestCount; p++) printf("%d %d\n", bestE[2 * p], bestE[2 * p + 1]);
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

    # Safe fallback: K_{d,d}, which has diameter 2.
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

    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            n, e = lib.araujo_lopez_graph(d - 2)
            consider(n, e)
        except Exception:
            pass

    if d < 3 or D < 2:
        return best

    # Bi-Cayley search over groups of order near the target. It gets most of the
    # budget, leaving a margin for process startup and the final check.
    budget = max(0.5, min(0.8 * time_limit, time_limit - 8.0))
    try:
        out = lib.run_c(C_BICAYLEY, [d, D, seed, round(budget, 2), best_n + 1],
                        timeout=budget + 6.0)
        n, e = lib.parse_graph_text(out)
        if n > 0:
            consider(n, e)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
