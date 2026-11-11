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

#define MAXD 16
#define GMAX 1600

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

/* Haar-type bipartite graph over a group H of order G:
   A_x ~ B_{x s} for s in S (|S| = d). Vertices 0..G-1 are A, G..2G-1 are B.
   Left multiplication is an automorphism, so only BFS from A_e and B_e is needed. */
static int d_, D_, G_;
static int *MT = NULL, *INV = NULL;
static int *vis = NULL, *qb = NULL, *dep = NULL;
static int stamp_ = 0;
static int *bE = NULL;
static int bEc = 0, bestN = 0;

/* Group Z_m x| Z_k2 with (a,b)(c,e) = (a + r^b c, b + e). Element a*k2+b. */
static int build_group(int m, int k2, int r) {
    int G = m * k2;
    if (G > GMAX || G < 2) return 0;
    G_ = G;
    free(MT); free(INV);
    MT = malloc(sizeof(int) * (size_t)G * G);
    INV = malloc(sizeof(int) * (size_t)G);
    int *pw = malloc(sizeof(int) * (size_t)k2);
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
    for (int x = 0; x < G; x++) INV[x] = -1;
    for (int x = 0; x < G; x++)
        for (int y = 0; y < G; y++)
            if (MT[x * G + y] == 0) INV[x] = y;
    free(pw);
    return 1;
}

/* Number of vertices within distance D_ of source (0 = A_e, 1 = B_e). */
static int bfs_count(int src, const int *S, int d, int D) {
    int G = G_;
    int st = ++stamp_;
    int head = 0, tail = 0;
    int s0 = src ? G : 0;
    vis[s0] = st; dep[s0] = 0; qb[tail++] = s0;
    int cnt = 1;
    while (head < tail) {
        int v = qb[head++];
        int dv = dep[v];
        if (dv >= D) continue;
        if (v < G) {
            const int *row = MT + (size_t)v * G;
            for (int j = 0; j < d; j++) {
                int w = G + row[S[j]];
                if (vis[w] != st) { vis[w] = st; dep[w] = dv + 1; qb[tail++] = w; cnt++; }
            }
        } else {
            const int *row = MT + (size_t)(v - G) * G;
            for (int j = 0; j < d; j++) {
                int w = row[INV[S[j]]];
                if (vis[w] != st) { vis[w] = st; dep[w] = dv + 1; qb[tail++] = w; cnt++; }
            }
        }
    }
    return cnt;
}

static long long evalc(const int *S, int d) {
    int G = G_;
    long long ca = bfs_count(0, S, d, D_);
    long long cb = bfs_count(1, S, d, D_);
    return (2LL * G - ca) + (2LL * G - cb);
}

/* Annealing over the connection set S (d distinct group elements).
   Returns 1 when the Haar graph has diameter <= D_. */
static int anneal(int *S, int d, double tend, int iters) {
    int G = G_;
    if (d > G) return 0;
    for (int j = 0; j < d; j++) {
        int x;
        for (;;) {
            x = rndi(G);
            int dup = 0;
            for (int i = 0; i < j; i++) if (S[i] == x) { dup = 1; break; }
            if (!dup) break;
        }
        S[j] = x;
    }
    long long cost = evalc(S, d);
    double c0 = (double)(cost > 0 ? cost : 1);
    for (int t = 0; t < iters && cost != 0; t++) {
        if ((t & 127) == 0 && now() > tend) break;
        double T = 0.3 * c0 * (1.0 - (double)t / iters) + 0.05;
        int j = rndi(d);
        int nw = rndi(G);
        int dup = 0;
        for (int i = 0; i < d; i++) if (S[i] == nw) { dup = 1; break; }
        if (dup) continue;
        int old = S[j];
        S[j] = nw;
        long long c2 = evalc(S, d);
        if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / T)) {
            cost = c2;
        } else {
            S[j] = old;
        }
    }
    return cost == 0;
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
    vis = calloc(2 * GMAX + 8, sizeof(int));
    qb = calloc(2 * GMAX + 8, sizeof(int));
    dep = calloc(2 * GMAX + 8, sizeof(int));

    /* Target: 2G vertices, so G >= minN/2. */
    int Gmin = (minN + 1) / 2;
    if (Gmin < d_ + 1) Gmin = d_ + 1;
    if (Gmin < 2) Gmin = 2;

    double slice = tl / 12.0;
    if (slice < 1.0) slice = 1.0;

    while (now() < tend && Gmin <= GMAX) {
        int G = Gmin + rndi(Gmin / 30 + 3);
        if (G > GMAX) G = GMAX;

        static int divs[GMAX + 1];
        int nd = 0;
        for (int k2 = 1; k2 <= G / 2; k2++)
            if (G % k2 == 0) divs[nd++] = k2;
        if (nd == 0) break;
        int k2 = divs[rndi(nd)];
        int m = G / k2;

        static int cand[GMAX + 1];
        int nc = 0;
        for (int r = 1; r < m; r++)
            if (gcd_i(r, m) == 1 && powmod(r, k2, m) == 1 % m) cand[nc++] = r;
        if (nc == 0) continue;
        int r = cand[rndi(nc)];
        if (!build_group(m, k2, r)) continue;

        double gend = now() + slice;
        if (gend > tend) gend = tend;
        int S[MAXD];
        int ok = 0;
        while (now() < gend && !ok) ok = anneal(S, d_, gend, 4000);

        if (ok) {
            int d = d_;
            free(bE);
            bE = malloc(sizeof(int) * 2 * (size_t)G * (size_t)d);
            int p = 0;
            for (int x = 0; x < G; x++)
                for (int j = 0; j < d; j++) {
                    bE[2 * p] = x;
                    bE[2 * p + 1] = G + MT[x * G + S[j]];
                    p++;
                }
            bEc = G * d;
            bestN = 2 * G;
            Gmin = G + 1;
        }
    }

    if (bestN == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", bestN, bEc);
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

    # Search for Haar graphs over non-abelian groups, starting well above the
    # PG fallback so the annealer begins near the record scale.
    moore = lib.moore_bound(d, D)
    budget = max(0.5, min(0.8 * time_limit, time_limit - 10.0))
    minN = max(best_n + 1, int(0.4 * moore))
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), minN],
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
