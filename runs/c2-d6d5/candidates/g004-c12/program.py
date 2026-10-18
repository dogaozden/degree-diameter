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
#define NMAX (4 * GMAX)
#define WIN 40
#define ITERS 60000
#define PAT 10000
#define CANDCAP 400000

/* Multi-orbit Cayley-type bipartite search.
   Group H of order G. NB orbits on each side (NB = 1 or 2).
   Vertices: A_{i,x} = i*G + x, B_{j,y} = NB*G + j*G + y.
   Edges: A_{i,x} ~ B_{j, x*s} for s in SS[i][j], where |SS[i][j]| = SZ[i][j].
   Row and column sums of SZ equal d, so the graph is d-regular.
   For NB = 2: SZ = [[a, d-a],[d-a, a]] with 1 <= a <= d-1.
   Left translation is an automorphism, so the cost is the number of vertices
   unreached within D from each of the 2*NB orbit base points. */

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

static int d_, D_, G, NB;
static uint16_t MT[GMAX * GMAX];
static int INV[GMAX];
static int SZ[2][2];
static int SS[2][2][MAXD];
static int distA[NMAX], que[NMAX];

static int *bestE = NULL;
static int bestTot = 0, bestE_cnt = 0;

typedef struct { int T, G, m, k, r, nb; } Cand;
static Cand *cand = NULL;
static int ncand = 0;

static int cmpc(const void *a, const void *b) {
    const Cand *x = a, *y = b;
    return (x->T > y->T) - (x->T < y->T);
}

static void add_cand(int minT, int maxT, int G2, int m, int k, int r) {
    for (int nb = 1; nb <= 2; nb++) {
        int T = 2 * nb * G2;
        if (T < minT || T > maxT) continue;
        if (ncand >= CANDCAP) return;
        cand[ncand].T = T;
        cand[ncand].G = G2;
        cand[ncand].m = m;
        cand[ncand].k = k;
        cand[ncand].r = r;
        cand[ncand].nb = nb;
        ncand++;
    }
}

static void gen_cands(int minT, int maxT, int d) {
    cand = malloc(sizeof(Cand) * (size_t)CANDCAP);
    ncand = 0;
    int GL = maxT / 2;
    if (GL > GMAX) GL = GMAX;
    for (int m = 1; m <= GL; m++) {
        for (int k = 1; m * k <= GL; k++) {
            int G2 = m * k;
            if (G2 < d) continue;
            if (m == 1) { add_cand(minT, maxT, G2, 1, k, 0); continue; }
            for (int r = 1; r < m; r++) {
                if (gcd_i(r, m) != 1) continue;
                if (powmod(r, k, m) != 1 % m) continue;
                add_cand(minT, maxT, G2, m, k, r);
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

static int inset_ij(int i, int j, int n, int x) {
    for (int q = 0; q < n; q++) if (SS[i][j][q] == x) return 1;
    return 0;
}

static int bfs_unreached(int src) {
    int N = 2 * NB * G;
    int BOFF = NB * G;
    for (int v = 0; v < N; v++) distA[v] = -1;
    int qh = 0, qt = 0;
    distA[src] = 0;
    que[qt++] = src;
    while (qh < qt) {
        int v = que[qh++];
        int dv = distA[v];
        if (dv >= D_) continue;
        if (v < BOFF) {
            int i = v / G, x = v % G;
            const uint16_t *row = MT + (size_t)x * G;
            for (int j = 0; j < NB; j++)
                for (int t = 0; t < SZ[i][j]; t++) {
                    int s = SS[i][j][t];
                    int w = BOFF + j * G + (int)row[s];
                    if (distA[w] < 0) { distA[w] = dv + 1; que[qt++] = w; }
                }
        } else {
            int u = v - BOFF;
            int j = u / G, y = u % G;
            const uint16_t *row = MT + (size_t)y * G;
            for (int i = 0; i < NB; i++)
                for (int t = 0; t < SZ[i][j]; t++) {
                    int s = SS[i][j][t];
                    int w = i * G + (int)row[INV[s]];
                    if (distA[w] < 0) { distA[w] = dv + 1; que[qt++] = w; }
                }
        }
    }
    return N - qt;
}

static long long evalc(void) {
    long long c = 0;
    for (int i = 0; i < NB; i++) c += bfs_unreached(i * G);
    for (int j = 0; j < NB; j++) c += bfs_unreached(NB * G + j * G);
    return c;
}

static int anneal(double tend, int nb) {
    int d = d_;
    if (G < d) return 0;
    NB = nb;
    if (NB == 1) {
        SZ[0][0] = d;
        SZ[0][1] = 0; SZ[1][0] = 0; SZ[1][1] = 0;
    } else {
        int a = 1 + rndi(d - 1);
        SZ[0][0] = a;
        SZ[0][1] = d - a;
        SZ[1][0] = d - a;
        SZ[1][1] = a;
    }
    for (int i = 0; i < NB; i++)
        for (int j = 0; j < NB; j++)
            for (int t = 0; t < SZ[i][j]; t++) {
                int x;
                do { x = rndi(G); } while (inset_ij(i, j, t, x));
                SS[i][j][t] = x;
            }

    long long cost = evalc(), best = cost;
    int last = 0;
    for (int t = 0; t < ITERS; t++) {
        if (cost == 0) break;
        if (t - last > PAT) break;
        if ((t & 255) == 0 && now() > tend) break;
        int i = rndi(NB), j = rndi(NB);
        if (SZ[i][j] == 0) continue;
        int tt = rndi(SZ[i][j]);
        int nw = rndi(G);
        if (inset_ij(i, j, SZ[i][j], nw)) continue;
        int old = SS[i][j][tt];
        SS[i][j][tt] = nw;
        long long c2 = evalc();
        double temp = 3.0 * (1.0 - (double)t / ITERS) + 0.05;
        if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
            if (cost < best) { best = cost; last = t; }
        } else {
            SS[i][j][tt] = old;
        }
    }
    return cost == 0;
}

static void store_best(void) {
    int E = NB * G * d_;
    free(bestE);
    bestE = malloc(sizeof(int) * 2 * (size_t)E);
    int p = 0;
    int BOFF = NB * G;
    for (int i = 0; i < NB; i++)
        for (int x = 0; x < G; x++)
            for (int j = 0; j < NB; j++)
                for (int t = 0; t < SZ[i][j]; t++) {
                    int s = SS[i][j][t];
                    bestE[2 * p] = i * G + x;
                    bestE[2 * p + 1] = BOFF + j * G + (int)MT[x * G + s];
                    p++;
                }
    bestE_cnt = p;
    bestTot = 2 * NB * G;
}

int main(int argc, char **argv) {
    if (argc < 7) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    int minT = atoi(argv[5]);
    int maxT = atoi(argv[6]);
    if (d_ < 3 || d_ > MAXD || D_ < 2) { printf("0 0\n"); return 0; }
    if (minT < 2) minT = 2;
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    double tend = now() + tl;
    gen_cands(minT, maxT, d_);

    int lo = 0;
    while (now() < tend && lo < ncand) {
        int span = ncand - lo;
        int W = span < WIN ? span : WIN;
        int idx = lo + rndi(W);
        Cand c = cand[idx];
        if (!build_group(c.m, c.k, c.r)) continue;
        if (anneal(tend, c.nb)) {
            store_best();
            while (lo < ncand && cand[lo].T <= bestTot) lo++;
        }
    }

    if (bestTot == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", bestTot, bestE_cnt);
    for (int p = 0; p < bestE_cnt; p++) printf("%d %d\n", bestE[2 * p], bestE[2 * p + 1]);
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

    budget = max(0.5, min(0.9 * time_limit, time_limit - 6.0))
    moore = lib.moore_bound(d, D)
    # Search only orders between a bit above the current best and the Moore bound.
    min_total = max(best_n + 2, int(0.4 * moore))
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), min_total, moore],
                        timeout=budget + 5.0)
        n, e = lib.parse_graph_text(out)
        if n > 0:
            consider(n, e)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
