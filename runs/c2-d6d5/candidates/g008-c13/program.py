import lib


C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

#define MAXD 32
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
static long long powmod(long long b, long long e, long long m) {
    long long r = 1 % m; b %= m;
    while (e > 0) { if (e & 1) r = r * b % m; b = b * b % m; e >>= 1; }
    return r;
}

/* Haar-type bipartite graph over a group G = Z_m x| Z_k:
   A_g ~ B_{g s} for s in S (|S| = d). Vertices: A_g = g, B_h = G + h.
   Left multiplication is an automorphism preserving both sides, so the
   diameter is <= D iff both A_e and B_e reach everything within D. */
static int d_, D_, G_;
static int *MT = NULL, *INV = NULL;
static int S[MAXD];
static int *dist = NULL, *que = NULL;
static int *bE = NULL, bEc = 0, bestG = 0;

static int build_group(int m, int k, int r) {
    int G = m * k;
    if (G > GMAX || G < d_ + 1) return 0;
    free(MT); free(INV);
    MT = malloc(sizeof(int) * (size_t)G * G);
    INV = malloc(sizeof(int) * (size_t)G);
    int *pw = malloc(sizeof(int) * (size_t)k);
    pw[0] = 1 % m;
    for (int t = 1; t < k; t++) pw[t] = (int)((long long)pw[t - 1] * r % m);
    for (int x = 0; x < G; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < G; y++) {
            int c = y / k, e = y % k;
            int aa = (int)((a + (long long)pw[b] * c) % m);
            MT[(size_t)x * G + y] = aa * k + (b + e) % k;
        }
    }
    for (int x = 0; x < G; x++)
        for (int y = 0; y < G; y++)
            if (MT[(size_t)x * G + y] == 0) { INV[x] = y; break; }
    free(pw);
    G_ = G;
    return 1;
}

/* Number of vertices NOT within distance D_ of src. */
static int unreached(int src) {
    int G = G_, d = d_, N = 2 * G;
    for (int v = 0; v < N; v++) dist[v] = -1;
    int h = 0, t = 0, seen = 1;
    dist[src] = 0;
    que[t++] = src;
    while (h < t) {
        int v = que[h++];
        if (dist[v] >= D_) continue;
        int nd = dist[v] + 1;
        if (v < G) {
            const int *row = MT + (size_t)v * G;
            for (int j = 0; j < d; j++) {
                int w = G + row[S[j]];
                if (dist[w] < 0) { dist[w] = nd; que[t++] = w; seen++; }
            }
        } else {
            const int *row = MT + (size_t)(v - G) * G;
            for (int j = 0; j < d; j++) {
                int w = row[INV[S[j]]];
                if (dist[w] < 0) { dist[w] = nd; que[t++] = w; seen++; }
            }
        }
    }
    return N - seen;
}

static long long evalcost(void) {
    return (long long)unreached(0) + (long long)unreached(G_);
}

static int search(double tend, long long iters) {
    int G = G_, d = d_;
    for (int i = 0; i < d; i++) {
        int x, ok;
        do {
            x = rndi(G); ok = 1;
            for (int j = 0; j < i; j++) if (S[j] == x) { ok = 0; break; }
        } while (!ok);
        S[i] = x;
    }
    long long cost = evalcost();
    for (long long t = 0; t < iters && cost > 0; t++) {
        if ((t & 127) == 0 && now() > tend) break;
        double T = 2.0 * (1.0 - (double)t / (double)iters) + 0.05;
        int i = rndi(d), x, ok;
        do {
            x = rndi(G); ok = 1;
            for (int j = 0; j < d; j++) if (S[j] == x) { ok = 0; break; }
        } while (!ok);
        int old = S[i];
        S[i] = x;
        long long c2 = evalcost();
        if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / T)) cost = c2;
        else S[i] = old;
    }
    return cost == 0;
}

static void store(void) {
    int G = G_, d = d_;
    free(bE);
    bE = malloc(sizeof(int) * 2 * (size_t)G * d);
    bEc = G * d;
    bestG = G;
    int p = 0;
    for (int g = 0; g < G; g++)
        for (int j = 0; j < d; j++) {
            bE[2 * p] = g;
            bE[2 * p + 1] = G + MT[(size_t)g * G + S[j]];
            p++;
        }
}

int main(int argc, char **argv) {
    if (argc < 6) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    int minG = atoi(argv[5]);
    if (d_ < 3 || D_ < 3 || d_ > MAXD) { printf("0 0\n"); return 0; }
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    dist = malloc(sizeof(int) * (2 * GMAX + 4));
    que = malloc(sizeof(int) * (2 * GMAX + 4));
    static int cand[GMAX + 5];
    static const int Ks[10] = {1, 1, 2, 2, 2, 3, 3, 4, 5, 6};

    double tend = now() + tl;
    if (minG < d_ + 1) minG = d_ + 1;

    while (now() < tend) {
        int lo = minG;
        if (lo > GMAX) break;
        int k = Ks[rndi(10)];
        int m = (lo + k - 1) / k + rndi(lo / 40 + 3);
        if (m < 2) m = 2;
        if (m * k > GMAX) { k = 1; m = lo; }
        int nc = 0;
        for (int r = 1; r < m; r++)
            if (gcd_i(r, m) == 1 && powmod(r, k, m) == 1 % m) cand[nc++] = r;
        if (nc == 0) continue;
        int r = cand[rndi(nc)];
        if (!build_group(m, k, r)) continue;

        double gend = now() + 4.0;
        if (gend > tend) gend = tend;
        int ok = 0;
        while (!ok && now() < gend) ok = search(gend, 40000);
        if (ok) {
            store();
            minG = G_ + 1;
        }
    }

    if (bestG == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", 2 * bestG, bEc);
    for (int p = 0; p < bEc; p++) printf("%d %d\n", bE[2 * p], bE[2 * p + 1]);
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

    if d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            consider(*lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass

    # Haar-type search over groups; the C engine takes a per-side group order lower bound.
    budget = max(0.5, time_limit - 6.0)
    min_side = best_n // 2 + 1
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), min_side],
                        timeout=budget + 3.0)
        n, e = lib.parse_graph_text(out)
        if n > 0:
            consider(n, e)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
