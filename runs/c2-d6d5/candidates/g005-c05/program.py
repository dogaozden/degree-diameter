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
#define MAXK 4
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

/* Bi-Cayley-type block lifts over a group G = Z_m x| Z_k2 (element a*k2+b).
   Blocks A_{i,g} (i<K, g<G) index i*G+g; blocks B_{j,x} index K*G + j*G + x.
   Layer l: A_{i,g} ~ B_{sig[l][i], g * vs[l][i]}.
   The group acts by left multiplication, so BFS from one representative per block
   (A_{i,e} and B_{j,e}) decides the diameter exactly. */

static int d_, D_, K_, G_;
static int *MT = NULL, *INV = NULL;
static int *stamp = NULL, *fa = NULL, *fb = NULL;
static int curstamp = 0;
static int sig[MAXD][MAXK], sinv[MAXD][MAXK], vs[MAXD][MAXK];
static int *bE = NULL;
static int bEc = 0, bestN = 0;

static int build_group(int m, int k2, int r) {
    int G = m * k2;
    if (G > GMAX || G < 2) return 0;
    G_ = G;
    free(MT); free(INV);
    MT = malloc(sizeof(int) * (size_t)G * G);
    INV = malloc(sizeof(int) * (size_t)G);
    int *pwr = malloc(sizeof(int) * (size_t)k2);
    pwr[0] = 1 % m;
    for (int t = 1; t < k2; t++) pwr[t] = (int)((long long)pwr[t - 1] * r % m);
    for (int x = 0; x < G; x++) {
        int a = x / k2, b = x % k2;
        for (int y = 0; y < G; y++) {
            int c = y / k2, e = y % k2;
            int aa = (int)(((long long)a + (long long)pwr[b] * c) % m);
            MT[x * G + y] = aa * k2 + (b + e) % k2;
        }
    }
    for (int x = 0; x < G; x++)
        for (int y = 0; y < G; y++)
            if (MT[x * G + y] == 0) INV[x] = y;
    free(pwr);
    return 1;
}

static void alloc_bfs(void) {
    int N2 = 2 * K_ * G_;
    free(stamp); free(fa); free(fb);
    stamp = calloc((size_t)N2, sizeof(int));
    fa = malloc(sizeof(int) * (size_t)N2);
    fb = malloc(sizeof(int) * (size_t)N2);
    curstamp = 0;
}

static int bfs_count(int src) {
    int G = G_, k = K_, d = d_;
    int kG = k * G;
    curstamp++;
    if (curstamp == 0x7ffffff0) {
        memset(stamp, 0, sizeof(int) * (size_t)(2 * kG));
        curstamp = 1;
    }
    int *cur = fa, *nxt = fb;
    int nf = 0, reached = 1;
    stamp[src] = curstamp;
    cur[nf++] = src;
    for (int dep = 0; dep < D_ && nf > 0; dep++) {
        int nn = 0;
        for (int q = 0; q < nf; q++) {
            int v = cur[q];
            if (v < kG) {
                int i = v / G, g = v % G;
                const int *row = MT + (size_t)g * G;
                for (int l = 0; l < d; l++) {
                    int j = sig[l][i];
                    int w = kG + j * G + row[vs[l][i]];
                    if (stamp[w] != curstamp) { stamp[w] = curstamp; nxt[nn++] = w; }
                }
            } else {
                int u = v - kG;
                int j = u / G, x = u % G;
                const int *row = MT + (size_t)x * G;
                for (int l = 0; l < d; l++) {
                    int i = sinv[l][j];
                    int w = i * G + row[INV[vs[l][i]]];
                    if (stamp[w] != curstamp) { stamp[w] = curstamp; nxt[nn++] = w; }
                }
            }
        }
        reached += nn;
        int *t = cur; cur = nxt; nxt = t;
        nf = nn;
    }
    return reached;
}

static int dupcount(void) {
    int c = 0, k = K_, d = d_;
    for (int i = 0; i < k; i++)
        for (int l = 0; l < d; l++)
            for (int l2 = l + 1; l2 < d; l2++)
                if (sig[l][i] == sig[l2][i] && vs[l][i] == vs[l2][i]) c++;
    return c;
}

static long long cost_of(void) {
    int k = K_, G = G_;
    long long N2 = 2LL * k * G;
    long long unreached = 0;
    for (int src = 0; src < 2 * k; src++) {
        int s0 = (src < k) ? src * G : k * G + (src - k) * G;
        unreached += N2 - bfs_count(s0);
    }
    return unreached + 1000LL * dupcount();
}

static int anneal(double tend, long long iters) {
    int k = K_, d = d_, G = G_;
    for (int l = 0; l < d; l++) {
        int perm[MAXK];
        for (int i = 0; i < k; i++) perm[i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rndi(i + 1);
            int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
        }
        for (int i = 0; i < k; i++) {
            sig[l][i] = perm[i];
            sinv[l][perm[i]] = i;
            vs[l][i] = rndi(G);
        }
    }
    long long cost = cost_of();
    const double T0 = 2.0, T1 = 0.1;
    for (long long t = 0; t < iters && cost > 0; t++) {
        if ((t & 127) == 0 && now() > tend) break;
        double temp = T0 + (T1 - T0) * (double)t / (double)iters;
        if (k >= 2 && rndu() < 0.3) {
            int l = rndi(d);
            int i1 = rndi(k), i2 = rndi(k - 1);
            if (i2 >= i1) i2++;
            int j1 = sig[l][i1], j2 = sig[l][i2];
            sig[l][i1] = j2; sig[l][i2] = j1;
            sinv[l][j2] = i1; sinv[l][j1] = i2;
            long long c2 = cost_of();
            if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
            } else {
                sig[l][i1] = j1; sig[l][i2] = j2;
                sinv[l][j1] = i1; sinv[l][j2] = i2;
            }
        } else {
            int l = rndi(d), i = rndi(k);
            int old = vs[l][i];
            int nw = rndi(G);
            if (nw == old) continue;
            vs[l][i] = nw;
            long long c2 = cost_of();
            if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
            } else {
                vs[l][i] = old;
            }
        }
    }
    return cost == 0;
}

static void save_graph(void) {
    int k = K_, G = G_, d = d_;
    int cnt = k * G * d;
    int *ne = malloc(sizeof(int) * 2 * (size_t)cnt);
    int p = 0;
    for (int i = 0; i < k; i++)
        for (int g = 0; g < G; g++)
            for (int l = 0; l < d; l++) {
                int j = sig[l][i];
                int s = vs[l][i];
                ne[2 * p] = i * G + g;
                ne[2 * p + 1] = k * G + j * G + MT[g * G + s];
                p++;
            }
    free(bE);
    bE = ne;
    bEc = cnt;
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
    static const int Ks[10] = {1, 1, 1, 1, 2, 2, 2, 3, 3, 4};
    static const int K2s[12] = {1, 1, 2, 2, 3, 4, 5, 6, 8, 10, 12, 16};
    static int cand[GMAX + 1];
    int target = minN < 2 ? 2 : minN;

    while (now() < tend) {
        int k = Ks[rndi(10)];
        int Gt = (target + 2 * k - 1) / (2 * k);
        if (Gt < d_) Gt = d_;
        Gt += rndi(Gt / 25 + 2);
        int k2 = K2s[rndi(12)];
        int m = (Gt + k2 - 1) / k2;
        if (m < 2) m = 2;
        int G = m * k2;
        if (G > GMAX || G < d_) continue;
        int nc = 0;
        for (int r = 1; r < m; r++)
            if (gcd_i(r, m) == 1 && powmod(r, k2, m) == 1 % m) cand[nc++] = r;
        if (nc == 0) continue;
        int r = cand[rndi(nc)];
        if (!build_group(m, k2, r)) continue;
        K_ = k;
        alloc_bfs();
        int ok = anneal(tend, 150000);
        if (ok && 2 * k * G > bestN) {
            save_graph();
            bestN = 2 * k * G;
            target = bestN + 1;
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

    if d < 3 or d > 16 or D < 3:
        return best

    budget = max(0.5, min(0.85 * time_limit, time_limit - 10.0))
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), best_n + 1],
                        timeout=budget + 5.0)
        n, e = lib.parse_graph_text(out)
        if n > 0:
            consider(n, e)
    except Exception:
        pass

    _ = time.monotonic() - start
    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
