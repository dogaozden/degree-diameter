import time

import lib


C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

/* Bi-Cayley search. Vertices: A_g = g (0..G-1), B_x = G + x (G..2G-1).
   Edge A_g ~ B_{g*s} for s in S (|S| = d, distinct). Left translation by any h
   is an automorphism, so validity reduces to two BFS runs, from A_e and B_e. */

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
static int *MT = NULL;   /* MT[x*G+y] = x*y in the current group */
static int *INV = NULL;  /* inverses */
static int S[MAXD], Sinv[MAXD];
static int *vis = NULL, *qu = NULL;
static int stamp_ = 0;
static int *bE = NULL;
static int bestG = 0;
static int divs[GMAX + 1];

/* Group Z_m x|_r Z_k2, element a*k2+b, (a,b)(c,e) = (a + r^b c, b + e). */
static int build_group(int m, int k2, int r) {
    int G = m * k2;
    if (G < 1 || G > GMAX) return 0;
    int *pwr = malloc(sizeof(int) * (size_t)k2);
    pwr[0] = 1 % m;
    for (int t = 1; t < k2; t++) pwr[t] = (int)((long long)pwr[t - 1] * r % m);
    free(MT); free(INV);
    MT = malloc(sizeof(int) * (size_t)G * G);
    INV = malloc(sizeof(int) * (size_t)G);
    G_ = G;
    for (int x = 0; x < G; x++) {
        int a = x / k2, b = x % k2;
        for (int y = 0; y < G; y++) {
            int c = y / k2, e = y % k2;
            int aa = (int)((a + (long long)pwr[b] * c) % m);
            MT[x * G + y] = aa * k2 + (b + e) % k2;
        }
    }
    for (int x = 0; x < G; x++) {
        INV[x] = 0;
        for (int y = 0; y < G; y++)
            if (MT[x * G + y] == 0) { INV[x] = y; break; }
    }
    free(pwr);
    return 1;
}

static void choose_group(int G) {
    int nd = 0;
    for (int k = 1; k <= G; k++) if (G % k == 0) divs[nd++] = k;
    for (int att = 0; att < 300; att++) {
        int k2 = divs[rndi(nd)];
        int m = G / k2;
        if (m == 1) { build_group(1, k2, 0); return; }
        int r = (rndi(2) == 0) ? 1 : 1 + rndi(m - 1);
        if (gcd_i(r, m) != 1) continue;
        if (powmod(r, k2, m) != 1 % m) continue;
        build_group(m, k2, r);
        return;
    }
    build_group(G, 1, 1);
}

static void set_s(int j, int val) {
    S[j] = val;
    Sinv[j] = INV[val];
}

/* Number of vertices within distance D_ of src. */
static int bfs(int src) {
    int G = G_, d = d_, D = D_;
    stamp_++;
    int head = 0, tail = 0;
    qu[tail++] = src;
    vis[src] = stamp_;
    for (int dep = 0; dep < D && head < tail; dep++) {
        int end = tail;
        while (head < end) {
            int v = qu[head++];
            if (v < G) {
                const int *row = MT + (size_t)v * G;
                for (int j = 0; j < d; j++) {
                    int w = G + row[S[j]];
                    if (vis[w] != stamp_) { vis[w] = stamp_; qu[tail++] = w; }
                }
            } else {
                const int *row = MT + (size_t)(v - G) * G;
                for (int j = 0; j < d; j++) {
                    int w = row[Sinv[j]];
                    if (vis[w] != stamp_) { vis[w] = stamp_; qu[tail++] = w; }
                }
            }
        }
    }
    return tail;
}

/* Number of (vertex, source) unreached pairs over the two representatives. */
static int cost_of(void) {
    int T = 2 * G_;
    return (T - bfs(0)) + (T - bfs(G_));
}

static void store_graph(void) {
    int G = G_, d = d_;
    free(bE);
    bE = malloc(sizeof(int) * 2 * (size_t)G * d);
    int p = 0;
    for (int g = 0; g < G; g++)
        for (int j = 0; j < d; j++) {
            bE[2 * p] = g;
            bE[2 * p + 1] = G + MT[g * G + S[j]];
            p++;
        }
    bestG = G;
}

int main(int argc, char **argv) {
    if (argc < 6) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    int minN = atoi(argv[5]);
    if (d_ < 3 || D_ < 2 || d_ > MAXD) { printf("0 0\n"); return 0; }
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    vis = malloc(sizeof(int) * (2 * GMAX + 5));
    qu = malloc(sizeof(int) * (2 * GMAX + 5));
    for (int i = 0; i < 2 * GMAX + 5; i++) vis[i] = 0;

    double tend = now() + tl;
    int G = (minN + 1) / 2;
    if (G < d_ + 1) G = d_ + 1;
    if (G > GMAX) G = GMAX;
    int lo = 0, hi = 0;   /* lo: largest success so far; hi: smallest failure so far */
    const int R = 25, ITERS = 20000;

    while (now() < tend) {
        int ok = 0;
        for (int rep = 0; rep < R && now() < tend && !ok; rep++) {
            choose_group(G);
            for (int j = 0; j < d_; j++) {
                int v, dup;
                do {
                    v = rndi(G);
                    dup = 0;
                    for (int i = 0; i < j; i++) if (S[i] == v) dup = 1;
                } while (dup);
                set_s(j, v);
            }
            int cost = cost_of();
            for (int t = 0; t < ITERS && cost > 0; t++) {
                if ((t & 255) == 0 && now() > tend) break;
                int j = rndi(d_);
                int v = rndi(G);
                int dup = 0;
                for (int i = 0; i < d_; i++) if (S[i] == v) dup = 1;
                if (dup) continue;
                int old = S[j], oldi = Sinv[j];
                set_s(j, v);
                int c2 = cost_of();
                double T = 2.0 * (1.0 - (double)t / ITERS) + 0.05;
                if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / T)) {
                    cost = c2;
                } else {
                    S[j] = old; Sinv[j] = oldi;
                }
            }
            if (cost == 0) {
                ok = 1;
                store_graph();
            }
        }
        if (now() >= tend) break;

        int next;
        if (ok) {
            lo = G;
            if (lo >= GMAX) break;
            if (hi == 0) next = G + G / 12 + 1;
            else if (hi - lo <= 1) next = hi;
            else next = (lo + hi) / 2;
        } else {
            if (hi == 0 || G < hi) hi = G;
            if (lo == 0) {
                next = G - G / 12 - 1;
                if (next < d_ + 1) next = d_ + 1;
            } else if (hi - lo <= 1) {
                next = hi;
            } else {
                next = (lo + hi) / 2;
            }
        }
        if (next > GMAX) next = GMAX;
        if (next < d_ + 1) next = d_ + 1;
        G = next;
    }

    if (bestG == 0) { printf("0 0\n"); return 0; }
    int n = 2 * bestG, m = bestG * d_;
    printf("%d %d\n", n, m);
    for (int p = 0; p < m; p++) printf("%d %d\n", bE[2 * p], bE[2 * p + 1]);
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

    budget = max(1.0, min(0.85 * time_limit, time_limit - 8.0))
    minN = max(2 * d + 2, lib.moore_bound(d, D) // 3)
    try:
        out = lib.run_c(C_SOURCE, [d, D, int(seed) & 0xFFFFFFFFFFFF, round(budget, 2), minN],
                        timeout=budget + 8.0)
        n, e = lib.parse_graph_text(out)
        if n > 0:
            consider(n, e)
    except Exception:
        pass

    _ = time.monotonic() - start
    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
