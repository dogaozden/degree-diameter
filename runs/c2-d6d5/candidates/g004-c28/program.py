import lib


C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

/* Multi-base voltage-lift search.
   Base: K "A" vertices and K "B" vertices, group H of order G (semidirect Z_m x| Z_kk).
   Each A_i has d darts; dart (t, i) goes to B_{PI[t][i]} with voltage GE[t][i]:
       A_{i,x} ~ B_{PI[t][i], x*GE[t][i]}.
   Every B_j receives exactly d darts (one per t, from the unique i with PI[t][i]=j), so the
   graph is d-regular bipartite on 2KG vertices. Left translation by H is an automorphism,
   so the diameter test needs BFS from A_{i,e} and B_{j,e} for all i, j (2K sources).
   K = 1 is the Cayley-type search; K >= 2 is a genuinely larger base. */

typedef uint64_t u64;

#define MAXD 12
#define MAXK 6
#define GMAX 1200
#define NVMAX (2 * MAXK * GMAX)
#define KMAX 5
#define SPAN 40
#define WIN 60
#define ITERS 20000
#define PAT 4000
#define DUPW 1000
#define CANDCAP 300000

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

static int d_, D_, K_, G;
static uint16_t MT[GMAX * GMAX];
static int INV[GMAX];
static int PI[MAXD][MAXK];
static int GE[MAXD][MAXK];
static int distv[NVMAX], que[NVMAX];

typedef struct { int n, K, G, m, kk, r; } Cand;
static Cand *cand = NULL;
static int ncand = 0;

static int cmpc(const void *a, const void *b) {
    const Cand *x = a, *y = b;
    return (x->n > y->n) - (x->n < y->n);
}

static void add_cand(int K, int G2, int m, int kk, int r) {
    if (ncand >= CANDCAP) return;
    Cand *c = &cand[ncand++];
    c->n = 2 * K * G2; c->K = K; c->G = G2; c->m = m; c->kk = kk; c->r = r;
}

static void gen_cands(int minN, int d) {
    cand = malloc(sizeof(Cand) * (size_t)CANDCAP);
    ncand = 0;
    for (int K = 1; K <= KMAX; K++) {
        int Glo = minN / (2 * K) + 1;
        if (Glo < d) Glo = d;
        if (Glo < 1) Glo = 1;
        int Ghi = Glo + SPAN;
        if (Ghi > GMAX) Ghi = GMAX;
        for (int G2 = Glo; G2 <= Ghi; G2++) {
            for (int m = 1; m <= G2; m++) {
                if (G2 % m) continue;
                int kk = G2 / m;
                if (m == 1) { add_cand(K, G2, 1, kk, 0); continue; }
                for (int r = 1; r < m; r++) {
                    if (gcd_i(r, m) != 1) continue;
                    if (powmod(r, kk, m) != 1 % m) continue;
                    add_cand(K, G2, m, kk, r);
                }
            }
        }
    }
    qsort(cand, (size_t)ncand, sizeof(Cand), cmpc);
}

/* Semidirect product Z_m x| Z_kk: (a,b)(c,e) = (a + r^b c, b + e), element coded a*kk + b. */
static int build_group(int m, int kk, int r) {
    G = m * kk;
    if (G > GMAX || G < 1) return 0;
    static int pw[GMAX];
    pw[0] = 1 % m;
    for (int t = 1; t < kk; t++) pw[t] = (int)((long long)pw[t - 1] * r % m);
    for (int x = 0; x < G; x++) {
        int a = x / kk, b = x % kk;
        for (int y = 0; y < G; y++) {
            int c = y / kk, e = y % kk;
            int aa = (int)(((long long)a + (long long)pw[b] * c) % m);
            MT[x * G + y] = (uint16_t)(aa * kk + (b + e) % kk);
        }
    }
    for (int x = 0; x < G; x++)
        for (int y = 0; y < G; y++)
            if (MT[x * G + y] == 0) { INV[x] = y; break; }
    return 1;
}

/* Vertices: A_{i,x} = i*G + x, B_{j,y} = K*G + j*G + y. */
static int bfs_unreached(int src) {
    int K = K_, d = d_, N = 2 * K * G, BOFF = K * G;
    for (int v = 0; v < N; v++) distv[v] = -1;
    int qh = 0, qt = 0;
    distv[src] = 0;
    que[qt++] = src;
    while (qh < qt) {
        int v = que[qh++];
        int dv = distv[v];
        if (dv >= D_) continue;
        if (v < BOFF) {
            int i = v / G, x = v - i * G;
            const uint16_t *row = MT + (size_t)x * G;
            for (int t = 0; t < d; t++) {
                int w = BOFF + PI[t][i] * G + (int)row[GE[t][i]];
                if (distv[w] < 0) { distv[w] = dv + 1; que[qt++] = w; }
            }
        } else {
            int u = v - BOFF;
            int j = u / G, y = u - j * G;
            const uint16_t *row = MT + (size_t)y * G;
            for (int i = 0; i < K; i++)
                for (int t = 0; t < d; t++) {
                    if (PI[t][i] != j) continue;
                    int w = i * G + (int)row[INV[GE[t][i]]];
                    if (distv[w] < 0) { distv[w] = dv + 1; que[qt++] = w; }
                }
        }
    }
    return N - qt;
}

static long long evalc(void) {
    int K = K_, d = d_;
    long long cost = 0;
    for (int i = 0; i < K; i++)
        for (int t1 = 0; t1 < d; t1++)
            for (int t2 = t1 + 1; t2 < d; t2++)
                if (PI[t1][i] == PI[t2][i] && GE[t1][i] == GE[t2][i]) cost += DUPW;
    for (int s = 0; s < 2 * K; s++) {
        int src = s < K ? s * G : K * G + (s - K) * G;
        cost += bfs_unreached(src);
    }
    return cost;
}

static int anneal(double tend) {
    int K = K_, d = d_;
    for (int t = 0; t < d; t++) {
        for (int i = 0; i < K; i++) PI[t][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndi(i + 1);
            int tmp = PI[t][i]; PI[t][i] = PI[t][j]; PI[t][j] = tmp;
        }
        for (int i = 0; i < K; i++) GE[t][i] = rndi(G);
    }
    long long cost = evalc(), best = cost;
    int last = 0;
    for (int it = 0; it < ITERS; it++) {
        if (cost == 0) break;
        if (it - last > PAT) break;
        if ((it & 127) == 0 && now() > tend) break;
        int sPI[MAXD][MAXK], sGE[MAXD][MAXK];
        memcpy(sPI, PI, sizeof PI);
        memcpy(sGE, GE, sizeof GE);
        if (K == 1 || rndu() < 0.7) {
            int t = rndi(d), i = rndi(K);
            GE[t][i] = rndi(G);
        } else {
            int t = rndi(d), i1 = rndi(K), i2 = rndi(K);
            if (i1 == i2) continue;
            int tmp = PI[t][i1]; PI[t][i1] = PI[t][i2]; PI[t][i2] = tmp;
        }
        long long c2 = evalc();
        double temp = 2.0 * (1.0 - (double)it / ITERS) + 0.05;
        if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
            if (cost < best) { best = cost; last = it; }
        } else {
            memcpy(PI, sPI, sizeof PI);
            memcpy(GE, sGE, sizeof GE);
        }
    }
    return cost == 0;
}

static int *bestEdges = NULL;
static int bestM = 0, bestNv = 0;

static void store_best(void) {
    int K = K_, d = d_;
    int E = K * G * d;
    free(bestEdges);
    bestEdges = malloc(sizeof(int) * 2 * (size_t)E);
    int BOFF = K * G;
    int p = 0;
    for (int x = 0; x < G; x++)
        for (int i = 0; i < K; i++)
            for (int t = 0; t < d; t++) {
                bestEdges[2 * p] = i * G + x;
                bestEdges[2 * p + 1] = BOFF + PI[t][i] * G + (int)MT[x * G + GE[t][i]];
                p++;
            }
    bestM = E;
    bestNv = 2 * K * G;
}

int main(int argc, char **argv) {
    if (argc < 6) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    int minN = atoi(argv[5]);
    if (d_ < 3 || d_ > MAXD || D_ < 2) { printf("0 0\n"); return 0; }
    if (minN < 0) minN = 0;
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    double tend = now() + tl;
    gen_cands(minN, d_);

    int lo = 0;
    while (now() < tend && lo < ncand) {
        int span = ncand - lo;
        int idx = lo + (int)(rndu() * rndu() * (double)span);
        if (idx >= ncand) idx = ncand - 1;
        Cand c = cand[idx];
        K_ = c.K;
        if (!build_group(c.m, c.kk, c.r)) continue;
        if (anneal(tend)) {
            store_best();
            while (lo < ncand && cand[lo].n <= bestNv) lo++;
        }
    }

    if (bestNv == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", bestNv, bestM);
    for (int p = 0; p < bestM; p++) printf("%d %d\n", bestEdges[2 * p], bestEdges[2 * p + 1]);
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
    # Only accept C output above this floor; the C search climbs upward from here.
    moore = lib.moore_bound(d, D)
    floor = max(best_n, int(0.42 * moore))
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), floor],
                        timeout=budget + 6.0)
        n, e = lib.parse_graph_text(out)
        if n > 0:
            consider(n, e)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
