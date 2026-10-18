import time

import lib


# ---------------------------------------------------------------------------
# Bold construction: bipartite Cayley ("Haar-type") graphs over non-abelian
# groups G = Z_m x| Z_k2. Vertices a_x and b_y (x, y in G); a_x ~ b_{x s} for
# s in S, |S| = d. Left translations are automorphisms, so the diameter is
# certified by two BFS runs (from a_1 and b_1). Simulated annealing over S
# with the number of pairs at distance > D as the cost. The group order G is
# climbed one step at a time: success raises the target, failure lowers it.
# ---------------------------------------------------------------------------
C_CAY = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXG 1200
#define MAXDG 16
#define ITERS 20000

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int n) { return (int)(rnd() % (uint64_t)n); }
static double rndu(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}
static int gcd_i(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }
static long long powmod(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    if (b < 0) b += m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static int d_, D_, G_;
static int *MT = NULL;      /* MT[x*G+y] = index of x*y */
static int *INV = NULL;     /* INV[x] = index of x^{-1} */
static int *dist_ = NULL, *queue_ = NULL;
static int Sv[MAXDG], Si[MAXDG];
static int inS[MAXG];
static int bestG = 0, bestM = 0;
static int bE[MAXG * MAXDG * 2];

/* Group Z_m x| Z_k2 with (a,b)(c,e) = (a + r^b c, b + e); element a*k2+b. Identity index 0. */
static int build_group(int m, int k2, int r) {
    int G = m * k2;
    if (G > MAXG || G < 2) return 0;
    free(MT); free(INV); free(dist_); free(queue_);
    MT = malloc(sizeof(int) * (size_t)G * (size_t)G);
    INV = malloc(sizeof(int) * (size_t)G);
    dist_ = malloc(sizeof(int) * (size_t)(2 * G));
    queue_ = malloc(sizeof(int) * (size_t)(2 * G));
    int *pw = malloc(sizeof(int) * (size_t)k2);
    pw[0] = 1 % m;
    for (int t = 1; t < k2; t++) pw[t] = (int)((long long)pw[t - 1] * r % m);
    G_ = G;
    for (int x = 0; x < G; x++) {
        int a = x / k2, b = x % k2;
        for (int y = 0; y < G; y++) {
            int c = y / k2, e = y % k2;
            int aa = (int)((a + (long long)pw[b] * c) % m);
            MT[(size_t)x * G + y] = aa * k2 + (b + e) % k2;
        }
    }
    free(pw);
    for (int x = 0; x < G; x++) INV[x] = -1;
    for (int x = 0; x < G; x++)
        for (int y = 0; y < G; y++)
            if (MT[(size_t)x * G + y] == 0) { INV[x] = y; break; }
    for (int x = 0; x < G; x++)
        if (INV[x] < 0) return 0;
    return 1;
}

/* Choose a random semidirect product of order G (k2 <= 24, m >= 2). */
static int pick_group(int G) {
    int divs[64], nd = 0;
    for (int k2 = 1; k2 <= 24 && k2 <= G / 2; k2++)
        if (G % k2 == 0) divs[nd++] = k2;
    if (nd == 0) return 0;
    int k2 = divs[rndi(nd)];
    int m = G / k2;
    static int cand[MAXG];
    int nc = 0;
    for (int r = 1; r < m; r++)
        if (gcd_i(r, m) == 1 && powmod(r, k2, m) == 1 % m) cand[nc++] = r;
    if (nc == 0) return 0;
    int r = cand[rndi(nc)];
    return build_group(m, k2, r);
}

/* BFS up to depth D_ from src (A-vertices 0..G-1, B-vertices G..2G-1); returns count reached. */
static int bfs_count(int src) {
    int G = G_, d = d_, N = 2 * G;
    for (int v = 0; v < N; v++) dist_[v] = -1;
    int qh = 0, qt = 0;
    queue_[qt++] = src;
    dist_[src] = 0;
    while (qh < qt) {
        int v = queue_[qh++];
        int dv = dist_[v];
        if (dv >= D_) continue;
        if (v < G) {
            const int *row = MT + (size_t)v * G;
            for (int i = 0; i < d; i++) {
                int w = G + row[Sv[i]];
                if (dist_[w] < 0) { dist_[w] = dv + 1; queue_[qt++] = w; }
            }
        } else {
            const int *row = MT + (size_t)(v - G) * G;
            for (int i = 0; i < d; i++) {
                int w = row[Si[i]];
                if (dist_[w] < 0) { dist_[w] = dv + 1; queue_[qt++] = w; }
            }
        }
    }
    return qt;
}

/* Left translations are automorphisms, so BFS from a_1 and b_1 certify diameter D. */
static long long cost_of(void) {
    int G = G_;
    long long ca = (long long)(2 * G - bfs_count(0));
    long long cb = (long long)(2 * G - bfs_count(G));
    return ca + cb;
}

static void random_S(void) {
    int G = G_, d = d_;
    for (int x = 0; x < G; x++) inS[x] = 0;
    for (int i = 0; i < d; i++) {
        int t;
        do { t = rndi(G); } while (inS[t]);
        inS[t] = 1;
        Sv[i] = t;
        Si[i] = INV[t];
    }
}

static void save_best(void) {
    int G = G_, d = d_, p = 0;
    for (int x = 0; x < G; x++)
        for (int i = 0; i < d; i++) {
            bE[2 * p] = x;
            bE[2 * p + 1] = G + MT[(size_t)x * G + Sv[i]];
            p++;
        }
    bestG = G;
    bestM = p;
}

/* Annealing over S for the current group. Returns 1 if cost 0 (valid) was reached. */
static int sa_run(double tend) {
    int G = G_, d = d_;
    random_S();
    long long cost = cost_of();
    for (int t = 0; t < ITERS && cost > 0; t++) {
        if ((t & 255) == 0 && now() > tend) break;
        double frac = (double)t / (double)ITERS;
        double T = 0.25 + 2.5 * (1.0 - frac);
        int i = rndi(d);
        int nt;
        do { nt = rndi(G); } while (inS[nt]);
        int old = Sv[i];
        Sv[i] = nt;
        Si[i] = INV[nt];
        inS[old] = 0;
        inS[nt] = 1;
        long long c2 = cost_of();
        long long dl = c2 - cost;
        if (dl <= 0 || rndu() < exp(-(double)dl / T)) {
            cost = c2;
        } else {
            Sv[i] = old;
            Si[i] = INV[old];
            inS[nt] = 0;
            inS[old] = 1;
        }
    }
    return cost == 0;
}

int main(int argc, char **argv) {
    if (argc < 7) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    int gStart = atoi(argv[5]);
    int gFloor = atoi(argv[6]);
    if (d_ < 2 || d_ > MAXDG || D_ < 2) { printf("0 0\n"); return 0; }
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    double tend = now() + tl;
    double slice = tl / 8.0;
    if (slice < 1.0) slice = 1.0;
    if (gFloor < d_ + 1) gFloor = d_ + 1;
    if (gFloor > MAXG) gFloor = MAXG;
    int G = gStart;
    if (G < gFloor) G = gFloor;
    if (G > MAXG) G = MAXG;

    while (now() < tend) {
        double send = now() + slice;
        if (send > tend) send = tend;
        int found = 0;
        while (now() < send && !found) {
            if (!pick_group(G)) continue;
            if (sa_run(send)) found = 1;
        }
        if (found) {
            if (G > bestG) save_best();
            if (G < MAXG) G++;
        } else {
            if (G > gFloor) G--;
        }
    }

    if (bestG == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", 2 * bestG, bestM);
    for (int p = 0; p < bestM; p++) printf("%d %d\n", bE[2 * p], bE[2 * p + 1]);
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

    budget = max(0.5, min(0.85 * time_limit, time_limit - 7.0))
    remaining = budget - (time.monotonic() - start)
    if remaining < 2.0:
        return best

    moore = lib.moore_bound(d, D)
    g_start = max(d + 1, moore // 5, best_n // 2 + 1)
    g_floor = max(d + 1, moore // 10)
    g_start = min(g_start, 1100)
    g_floor = min(g_floor, g_start)

    try:
        out = lib.run_c(C_CAY, [d, D, seed, round(remaining - 1.0, 2), g_start, g_floor],
                        timeout=remaining + 4.0)
        n, e = lib.parse_graph_text(out)
        if n > 0:
            consider(n, e)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
