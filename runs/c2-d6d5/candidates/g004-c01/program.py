import lib


C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

/* Two-class voltage lifts over semidirect products Z_m x| Z_k.
   Base graph: K A-vertices and K B-vertices (K = 1 or 2), with darts
   (i, j, g) meaning A_i x ~ B_j (x*g) for all x in the group.
   Count matrix for K = 2: [[p, d-p], [d-p, p]]; each class has degree d.
   Output order is 2*K*G. Each block of darts needs distinct voltages.
   Left translation preserves the structure, so the diameter check reduces
   to BFS from the identity of each of the 2K classes. */

typedef uint64_t u64;

#define MAXD 16
#define MAXK 2
#define GMAX 1200
#define NVMAX (2 * MAXK * GMAX)
#define NDMAX (MAXK * MAXD)
#define WIN 40
#define ITERS 30000
#define PAT 6000

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

static int d_, D_, G, K, ND;
static uint16_t MT[GMAX * GMAX];
static int INV[GMAX];
static int dI[NDMAX], dJ[NDMAX], dG[NDMAX];
static int adjA[MAXK][MAXD], adjB[MAXK][MAXD];
static int distv[NVMAX], que[NVMAX];

static int *bestE = NULL;
static int bestNV = 0, bestNE = 0;

typedef struct { int G, m, k, r; } Cand;
static Cand *cand = NULL;
static int ncand = 0;

static int cmpc(const void *a, const void *b) {
    const Cand *x = a, *y = b;
    return (x->G > y->G) - (x->G < y->G);
}

static void gen_cands(void) {
    int cap = 400000;
    cand = malloc(sizeof(Cand) * (size_t)cap);
    ncand = 0;
    for (int m = 1; m <= GMAX; m++) {
        for (int k = 1; m * k <= GMAX; k++) {
            int G2 = m * k;
            if (G2 < d_) continue;
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

static int lower_idx(int g) {
    int lo = 0, hi = ncand;
    while (lo < hi) {
        int mid = (lo + hi) / 2;
        if (cand[mid].G < g) lo = mid + 1; else hi = mid;
    }
    return lo;
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

static void setup_darts(int p) {
    int cnt[MAXK][MAXK];
    if (K == 1) {
        cnt[0][0] = d_;
    } else {
        cnt[0][0] = p;
        cnt[0][1] = d_ - p;
        cnt[1][0] = d_ - p;
        cnt[1][1] = p;
    }
    int k = 0;
    for (int i = 0; i < K; i++)
        for (int j = 0; j < K; j++)
            for (int t = 0; t < cnt[i][j]; t++) {
                dI[k] = i; dJ[k] = j; k++;
            }
    ND = k;
    for (int i = 0; i < K; i++) {
        int t = 0;
        for (int q = 0; q < ND; q++) if (dI[q] == i) adjA[i][t++] = q;
    }
    for (int j = 0; j < K; j++) {
        int t = 0;
        for (int q = 0; q < ND; q++) if (dJ[q] == j) adjB[j][t++] = q;
    }
}

/* 1 if assigning voltage g to dart k clashes with another dart in the same block. */
static int conflict(int k, int g, int upto) {
    for (int q = 0; q < upto; q++)
        if (q != k && dI[q] == dI[k] && dJ[q] == dJ[k] && dG[q] == g) return 1;
    return 0;
}

static int bfs_unreached(int src) {
    int NV = 2 * K * G;
    for (int i = 0; i < NV; i++) distv[i] = -1;
    int qh = 0, qt = 0;
    distv[src] = 0;
    que[qt++] = src;
    while (qh < qt) {
        int v = que[qh++];
        int dv = distv[v];
        if (dv >= D_) continue;
        int c = v / G, x = v - c * G;
        if (c < K) {
            for (int t = 0; t < d_; t++) {
                int kk = adjA[c][t];
                int w = (K + dJ[kk]) * G + (int)MT[x * G + dG[kk]];
                if (distv[w] < 0) { distv[w] = dv + 1; que[qt++] = w; }
            }
        } else {
            int j = c - K;
            for (int t = 0; t < d_; t++) {
                int kk = adjB[j][t];
                int w = dI[kk] * G + (int)MT[x * G + INV[dG[kk]]];
                if (distv[w] < 0) { distv[w] = dv + 1; que[qt++] = w; }
            }
        }
    }
    return NV - qt;
}

static long long evalc(void) {
    long long s = 0;
    for (int c = 0; c < 2 * K; c++) s += bfs_unreached(c * G);
    return s;
}

static int anneal(double tend, int p) {
    if (G < d_) return 0;
    setup_darts(p);
    for (int k = 0; k < ND; k++) {
        do { dG[k] = rndi(G); } while (conflict(k, dG[k], k));
    }
    long long cost = evalc(), best = cost;
    int last = 0;
    for (int t = 0; t < ITERS; t++) {
        if (cost == 0) break;
        if (t - last > PAT) break;
        if ((t & 255) == 0 && now() > tend) break;
        int k = rndi(ND);
        int nw = rndi(G);
        if (nw == dG[k]) continue;
        if (conflict(k, nw, ND)) continue;
        int old = dG[k];
        dG[k] = nw;
        long long c2 = evalc();
        double temp = 3.0 * (1.0 - (double)t / ITERS) + 0.05;
        if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
            if (cost < best) { best = cost; last = t; }
        } else {
            dG[k] = old;
        }
    }
    return cost == 0;
}

static void store_best(void) {
    int NE = ND * G;
    free(bestE);
    bestE = malloc(sizeof(int) * 2 * (size_t)NE);
    int p = 0;
    for (int k = 0; k < ND; k++)
        for (int x = 0; x < G; x++) {
            bestE[2 * p] = dI[k] * G + x;
            bestE[2 * p + 1] = (K + dJ[k]) * G + (int)MT[x * G + dG[k]];
            p++;
        }
    bestNE = NE;
    bestNV = 2 * K * G;
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
    gen_cands();

    int bestN = minN;
    while (now() < tend && ncand > 0) {
        K = (rndu() < 0.8) ? 2 : 1;
        int thr = bestN / (2 * K) + 1;
        if (thr < d_) thr = d_;
        int lo = lower_idx(thr);
        if (lo >= ncand) break;
        int span = ncand - lo;
        int W = span < WIN ? span : WIN;
        Cand c = cand[lo + rndi(W)];
        if (!build_group(c.m, c.k, c.r)) continue;
        int p = (K == 2) ? 1 + rndi(d_ - 1) : d_;
        if (anneal(tend, p)) {
            store_best();
            bestN = bestNV;
        }
    }

    if (bestNV == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", bestNV, bestNE);
    for (int p = 0; p < bestNE; p++) printf("%d %d\n", bestE[2 * p], bestE[2 * p + 1]);
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
    try:
        # The C search only accepts outputs strictly larger than best_n.
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), best_n],
                        timeout=budget + 6.0)
        n, e = lib.parse_graph_text(out)
        if n > 0:
            consider(n, e)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
