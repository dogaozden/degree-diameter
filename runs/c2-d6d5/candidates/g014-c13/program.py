import time

import lib


C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

#define GMAX 1200
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

/* Bi-Cayley (Haar) graph of a finite group G:
   A_g ~ B_{g*s} for s in S, |S| = d. Vertex-transitive under left
   multiplication, so the diameter is checked by BFS from A_0 and B_0 only. */

static int d_, D_, G_;
static int MT[GMAX * GMAX];
static int INV[GMAX];
static int S[MAXD];
static char inS[GMAX];
static int nbA[GMAX * MAXD];   /* A_g -> B index (G + h) */
static int nbB[GMAX * MAXD];   /* B_h -> A index */
static int distv[2 * GMAX];
static int qv[2 * GMAX];
static int bestE[GMAX * MAXD * 2];
static int bestG = 0;
static int candbuf[GMAX];

/* Group Z_m x|_r Z_k2 with (a,b)(c,e) = (a + r^b c, b + e), element a*k2+b. */
static int build_group(int m, int k2, int r) {
    int G = m * k2;
    if (G > GMAX || G < 2) return 0;
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
            if (MT[x * G + y] == 0) { INV[x] = y; break; }
    return 1;
}

static void set_slot(int idx) {
    int G = G_, d = d_;
    int s = S[idx];
    for (int g = 0; g < G; g++) {
        nbA[g * d + idx] = G + MT[g * G + s];
        nbB[g * d + idx] = MT[g * G + INV[s]];
    }
}

static int bfs_bad(int src) {
    int G = G_, d = d_, N = 2 * G_;
    for (int i = 0; i < N; i++) distv[i] = -1;
    int h = 0, t = 0, reached = 1;
    qv[t++] = src;
    distv[src] = 0;
    while (h < t) {
        int v = qv[h++];
        int dv = distv[v];
        if (dv >= D_) continue;
        const int *nb = (v < G) ? &nbA[v * d] : &nbB[(v - G) * d];
        for (int j = 0; j < d; j++) {
            int w = nb[j];
            if (distv[w] < 0) {
                distv[w] = dv + 1;
                qv[t++] = w;
                reached++;
            }
        }
    }
    return N - reached;
}

static int evalc(void) { return bfs_bad(0) + bfs_bad(G_); }

/* Simulated annealing over connection sets S in the current group. */
static int try_group(double tend, int iters) {
    int G = G_, d = d_;
    memset(inS, 0, sizeof(char) * (size_t)G);
    for (int t = 0; t < d; t++) {
        int e;
        do { e = rndi(G); } while (inS[e]);
        S[t] = e;
        inS[e] = 1;
    }
    for (int t = 0; t < d; t++) set_slot(t);
    int cost = evalc();
    for (int it = 0; it < iters && cost > 0; it++) {
        if ((it & 127) == 0 && now() > tend) break;
        double temp = 1.5 * (1.0 - (double)it / iters) + 0.1;
        int idx = rndi(d);
        int e = rndi(G);
        if (inS[e]) continue;
        int old = S[idx];
        inS[old] = 0;
        inS[e] = 1;
        S[idx] = e;
        set_slot(idx);
        int c2 = evalc();
        if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
        } else {
            inS[e] = 0;
            inS[old] = 1;
            S[idx] = old;
            set_slot(idx);
        }
    }
    return cost == 0;
}

static void save_edges(void) {
    int G = G_, d = d_, p = 0;
    for (int g = 0; g < G; g++)
        for (int t = 0; t < d; t++) {
            bestE[2 * p] = g;
            bestE[2 * p + 1] = G + MT[g * G + S[t]];
            p++;
        }
}

int main(int argc, char **argv) {
    if (argc < 6) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    int minN = atoi(argv[5]);
    if (d_ < 3 || D_ < 3 || d_ > MAXD) { printf("0 0\n"); return 0; }
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    double tend = now() + tl;
    static const int K2s[11] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12};
    int Gmin = (minN + 1) / 2;
    if (Gmin < d_) Gmin = d_;
    if (Gmin < 2) Gmin = 2;

    while (now() < tend && Gmin <= GMAX) {
        int k2 = K2s[rndi(11)];
        int G0 = Gmin + rndi(3);
        int m = (G0 + k2 - 1) / k2;
        if (m < 2) m = 2;
        if (m * k2 > GMAX) continue;
        int nc = 0;
        for (int r = 1; r < m; r++)
            if (gcd_i(r, m) == 1 && powmod(r, k2, m) == 1 % m) candbuf[nc++] = r;
        if (nc == 0) continue;
        int r = candbuf[rndi(nc)];
        if (!build_group(m, k2, r)) continue;
        int G = G_;
        int ok = 0;
        for (int rep = 0; rep < 3 && !ok && now() < tend; rep++)
            ok = try_group(tend, 6000);
        if (ok) {
            save_edges();
            bestG = G;
            Gmin = G + 1;
        }
    }

    if (bestG == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", 2 * bestG, bestG * d_);
    for (int p = 0; p < bestG * d_; p++)
        printf("%d %d\n", bestE[2 * p], bestE[2 * p + 1]);
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

    budget = max(0.5, min(0.8 * time_limit, time_limit - 8.0))
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), best_n + 1],
                        timeout=budget + 6.0)
        n, e = lib.parse_graph_text(out)
        if n > 0:
            consider(n, e)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
