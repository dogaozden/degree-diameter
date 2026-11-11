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
#define GMAX 1200
#define ITERS 40000
#define PAT 8000
#define MAXTRY 2

/* Cayley-type bipartite search. Group H (order G), connection set S (|S| = d).
   Graph: A_x ~ B_{x s} for s in S, on 2G vertices (A_x = x, B_y = G + y).
   Left translation is an automorphism, so every pair type reduces to a BFS
   from A_e (covers A-A and A-B pairs) or from B_e (covers B-B pairs).
   Cost = number of vertices unreached within D from A_e plus from B_e.

   Scheduling: candidate groups are visited in ascending order of order G.
   Each candidate gets at most MAXTRY annealing attempts, then the scheduler
   moves on, so a hopeless group cannot absorb the whole budget. Once a
   candidate succeeds, every group of order <= the new best is skipped. */

static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int n) { return (int)(rnd() % (u64)n); }
static double rndu(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }
static int gcd_i(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }
static long long powmod(long long b, long long e, long long m) {
    long long r = 1 % m; b %= m;
    while (e > 0) { if (e & 1) r = r * b % m; b = b * b % m; e >>= 1; }
    return r;
}

static int d_, D_, G;
static uint16_t MT[GMAX * GMAX];
static int INV[GMAX];
static int S[MAXD];
static int distA[2 * GMAX], que[2 * GMAX];

static int *bestE = NULL;
static int bestG = 0;

typedef struct { int G, m, k, r; } Cand;
static Cand *cand = NULL;
static int ncand = 0;
static int *attempts = NULL;

static int cmpc(const void *a, const void *b) {
    const Cand *x = a, *y = b;
    return (x->G > y->G) - (x->G < y->G);
}

static void gen_cands(int minG) {
    int cap = 400000;
    cand = malloc(sizeof(Cand) * (size_t)cap);
    ncand = 0;
    for (int m = 1; m <= GMAX; m++) {
        for (int k = 1; m * k <= GMAX; k++) {
            int G2 = m * k;
            if (G2 < minG || G2 < d_) continue;
            if (m == 1) {
                if (ncand < cap) { cand[ncand].G = G2; cand[ncand].m = 1; cand[ncand].k = k; cand[ncand].r = 0; ncand++; }
                continue;
            }
            for (int r = 1; r < m; r++) {
                if (gcd_i(r, m) != 1) continue;
                if (powmod(r, k, m) != 1 % m) continue;
                if (ncand < cap) { cand[ncand].G = G2; cand[ncand].m = m; cand[ncand].k = k; cand[ncand].r = r; ncand++; }
            }
        }
    }
    qsort(cand, (size_t)ncand, sizeof(Cand), cmpc);
}

/* Semidirect product Z_m x| Z_k: (a,b)(c,e) = (a + r^b c, b + e), element coded a*k + b. */
static int build_group(int m, int k, int r) {
    G = m * k;
    if (G > GMAX || G < 1) return 0;
    int *pw = malloc(sizeof(int) * (size_t)k);
    pw[0] = 1 % m;
    for (int t = 1; t < k; t++) pw[t] = (int)((long long)pw[t - 1] * r % m);
    for (int x = 0; x < G; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < G; y++) {
            int c = y / k, e = y % k;
            int aa = (int)(((long long)a + (long long)pw[b] * c) % m);
            MT[x * G + y] = (uint16_t)(aa * k + (b + e) % k);
        }
    }
    for (int x = 0; x < G; x++)
        for (int y = 0; y < G; y++)
            if (MT[x * G + y] == 0) { INV[x] = y; break; }
    free(pw);
    return 1;
}

static int inset(int x, int n) {
    for (int q = 0; q < n; q++) if (S[q] == x) return 1;
    return 0;
}

static int bfs_unreached(int src) {
    int N = 2 * G;
    for (int i = 0; i < N; i++) distA[i] = -1;
    int qh = 0, qt = 0;
    distA[src] = 0;
    que[qt++] = src;
    while (qh < qt) {
        int v = que[qh++];
        int dv = distA[v];
        if (dv >= D_) continue;
        if (v < G) {
            const uint16_t *row = MT + (size_t)v * G;
            for (int j = 0; j < d_; j++) {
                int w = G + (int)row[S[j]];
                if (distA[w] < 0) { distA[w] = dv + 1; que[qt++] = w; }
            }
        } else {
            const uint16_t *row = MT + (size_t)(v - G) * G;
            for (int j = 0; j < d_; j++) {
                int w = (int)row[INV[S[j]]];
                if (distA[w] < 0) { distA[w] = dv + 1; que[qt++] = w; }
            }
        }
    }
    return N - qt;
}

static long long evalc(void) {
    return (long long)bfs_unreached(0) + (long long)bfs_unreached(G);
}

static int anneal(double tend) {
    int d = d_;
    if (G < d) return 0;
    for (int j = 0; j < d; j++) {
        do { S[j] = rndi(G); } while (inset(S[j], j));
    }
    long long cost = evalc(), best = cost;
    int last = 0;
    for (int t = 0; t < ITERS; t++) {
        if (cost == 0) break;
        if (t - last > PAT) break;
        if ((t & 255) == 0 && now() > tend) break;
        int j = rndi(d);
        int nw = rndi(G);
        if (inset(nw, d)) continue;
        int old = S[j];
        S[j] = nw;
        long long c2 = evalc();
        double temp = 3.0 * (1.0 - (double)t / ITERS) + 0.05;
        if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
            if (cost < best) { best = cost; last = t; }
        } else {
            S[j] = old;
        }
    }
    return cost == 0;
}

static void store_best(void) {
    int E = G * d_;
    free(bestE);
    bestE = malloc(sizeof(int) * 2 * (size_t)E);
    int p = 0;
    for (int x = 0; x < G; x++)
        for (int j = 0; j < d_; j++) {
            bestE[2 * p] = x;
            bestE[2 * p + 1] = G + (int)MT[x * G + S[j]];
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
    int minG = atoi(argv[5]);
    if (d_ < 3 || d_ > MAXD || D_ < 2) { printf("0 0\n"); return 0; }
    if (minG < 1) minG = 1;
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    double tend = now() + tl;
    gen_cands(minG);
    attempts = calloc((size_t)(ncand > 0 ? ncand : 1), sizeof(int));

    /* Ascending sweep. lo is the first candidate that is still useful:
       its order exceeds bestG and it has attempts left. Both conditions
       only become false over time, so lo never needs to move back. */
    int lo = 0;
    while (now() < tend) {
        while (lo < ncand && (cand[lo].G <= bestG || attempts[lo] >= MAXTRY)) lo++;
        if (lo >= ncand) break;
        Cand c = cand[lo];
        attempts[lo]++;
        if (!build_group(c.m, c.k, c.r)) continue;
        if (anneal(tend)) store_best();
    }

    if (bestG == 0) { printf("0 0\n"); return 0; }
    int E = bestG * d_;
    printf("%d %d\n", 2 * bestG, E);
    for (int p = 0; p < E; p++) printf("%d %d\n", bestE[2 * p], bestE[2 * p + 1]);
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

    if d < 3 or D < 2:
        return best

    budget = max(0.5, min(0.85 * time_limit, time_limit - 8.0))
    # Smallest group order to try (output order is twice this). Heuristic start
    # near the region where good Cayley-type graphs live; the search climbs from here.
    moore = lib.moore_bound(d, D)
    min_group = max(best_n // 2 + 1, int(0.4 * moore / 2))
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), min_group],
                        timeout=budget + 6.0)
        n, e = lib.parse_graph_text(out)
        if n > 0:
            consider(n, e)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
