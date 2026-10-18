"""Bipartite lift search for d-regular graphs with diameter D.

Change from the parent: instead of sampling random groups, the C engine scans group
orders upward from the current target. For each order G and each block size k in
{1, 2, 3}, it enumerates every semidirect group Z_m x| Z_k2 of that order (with
gcd(r, m) = 1 and r^k2 = 1 mod m) and runs a longer simulated annealing on the
voltage assignment. Once a valid lift is found, the target moves above it.
The Python side keeps the best of the projective-plane incidence graph, K_{d,d},
and the C result, and validates everything before returning.
"""
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
#define MAXK 8
#define GMAX 2000
#define MAXSPEC 2048

static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int n) { return (int)(rnd() % (u64)n); }
static double rndu(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }
static int gcd_i(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }
static long long powmod(long long b, int e, long long m) {
    long long r = 1 % m; b %= m;
    while (e > 0) { if (e & 1) r = r * b % m; b = b * b % m; e >>= 1; }
    return r;
}
static int popc(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int d_, D_, K_, G_, N_;
static int *MT = NULL, *RS = NULL;
static int *nb = NULL;
static u64 *rch = NULL, *tmpr = NULL;
static int lay[MAXD][MAXK], VS[MAXD][MAXK];
static int *bE = NULL;
static int bEc = 0, bestN = 0;

/* Group Z_m x| Z_k2 with (a,b)(c,e) = (a + r^b c, b + e). r = 1 gives the direct product. */
static int build_group(int m, int k2, int r) {
    long long Gl = (long long)m * k2;
    if (Gl > GMAX || Gl < 2) return 0;
    int G = (int)Gl;
    G_ = G;
    free(MT); free(RS);
    MT = malloc(sizeof(int) * (size_t)G * G);
    RS = malloc(sizeof(int) * (size_t)G * G);
    int *pwr = malloc(sizeof(int) * k2);
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
    for (int g = 0; g < G; g++)
        for (int s = 0; s < G; s++)
            RS[s * G + MT[g * G + s]] = g;
    free(pwr);
    return 1;
}

static void alloc_state(int N) {
    free(nb); free(rch); free(tmpr);
    nb = malloc(sizeof(int) * (size_t)d_ * N);
    rch = malloc(sizeof(u64) * N);
    tmpr = malloc(sizeof(u64) * N);
    N_ = N;
}

/* Dart (l, i, j, s): A_{i,g} ~ B_{j, g*s}. Vertex A_{i,g} = i*G+g, B_{j,g} = (K+j)*G+g. */
static void setdart(int l, int i, int j, int s) {
    int G = G_, k = K_, N = N_;
    int *row = nb + (size_t)l * N;
    for (int g = 0; g < G; g++) {
        row[i * G + g] = (k + j) * G + MT[g * G + s];
        row[(k + j) * G + g] = i * G + RS[s * G + g];
    }
}

static long long evalcost(void) {
    int N = N_, G = G_, k = K_, d = d_;
    for (int v = 0; v < N; v++) rch[v] = 0;
    for (int b = 0; b < 2 * k; b++) rch[(size_t)b * G] = 1ULL << b;
    for (int t = 0; t < D_; t++) {
        for (int v = 0; v < N; v++) {
            u64 x = rch[v];
            for (int l = 0; l < d; l++) x |= rch[nb[l * N + v]];
            tmpr[v] = x;
        }
        u64 *sw = rch; rch = tmpr; tmpr = sw;
    }
    long long cnt = 0;
    for (int v = 0; v < N; v++) cnt += popc(rch[v]);
    long long unreached = (long long)2 * k * N - cnt;
    long long dup = 0;
    for (int i = 0; i < k; i++)
        for (int l = 0; l < d; l++)
            for (int l2 = l + 1; l2 < d; l2++)
                if (lay[l][i] == lay[l2][i] && VS[l][i] == VS[l2][i]) dup++;
    return unreached + 1000 * dup;
}

static int search(double tend, int iters, int patience) {
    int k = K_, d = d_, G = G_;
    for (int l = 0; l < d; l++) {
        int perm[MAXK];
        for (int i = 0; i < k; i++) perm[i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rndi(i + 1);
            int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
        }
        for (int i = 0; i < k; i++) { lay[l][i] = perm[i]; VS[l][i] = rndi(G); }
    }
    for (int l = 0; l < d; l++)
        for (int i = 0; i < k; i++)
            setdart(l, i, lay[l][i], VS[l][i]);
    long long cost = evalcost();
    double c0 = (double)(cost > 0 ? cost : 1);
    long long bestc = cost;
    int last = 0;
    for (int t = 0; t < iters; t++) {
        if (cost == 0) break;
        if (t - last > patience) break;
        if ((t & 63) == 0 && now() > tend) break;
        double temp = 0.02 * c0 * (1.0 - (double)t / iters);
        if (temp < 0.3) temp = 0.3;
        if (k >= 2 && rndu() < 0.25) {
            int l = rndi(d);
            int i1 = rndi(k), i2 = rndi(k - 1);
            if (i2 >= i1) i2++;
            int t1 = lay[l][i1], t2 = lay[l][i2];
            lay[l][i1] = t2; lay[l][i2] = t1;
            setdart(l, i1, t2, VS[l][i1]);
            setdart(l, i2, t1, VS[l][i2]);
            long long c2 = evalcost();
            if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                if (cost < bestc) { bestc = cost; last = t; }
            } else {
                lay[l][i1] = t1; lay[l][i2] = t2;
                setdart(l, i1, t1, VS[l][i1]);
                setdart(l, i2, t2, VS[l][i2]);
            }
        } else {
            int l = rndi(d), i = rndi(k);
            int old = VS[l][i];
            int nw = rndi(G);
            if (nw == old) continue;
            VS[l][i] = nw;
            setdart(l, i, lay[l][i], nw);
            long long c2 = evalcost();
            if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                if (cost < bestc) { bestc = cost; last = t; }
            } else {
                VS[l][i] = old;
                setdart(l, i, lay[l][i], old);
            }
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
    if (minN < 2) minN = 2;
    if (d_ < 3 || D_ < 3 || d_ > MAXD) { printf("0 0\n"); return 0; }
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    double tend = now() + tl;
    static int sm[MAXSPEC], sk2[MAXSPEC], sr[MAXSPEC];
    int Ks[6] = {1, 1, 1, 2, 2, 3};
    int cur = minN;

    while (now() < tend) {
        int k = Ks[rndi(6)];
        int Gmin = (cur + 2 * k - 1) / (2 * k);
        if (Gmin < 2) Gmin = 2;
        int G0 = Gmin + rndi(3);
        int found = 0;

        for (int G = G0; G < G0 + 8 && G <= GMAX && !found && now() < tend; G++) {
            /* Enumerate all semidirect groups of order G in the family. */
            int ns = 0;
            for (int k2 = 1; k2 <= 12 && k2 <= G; k2++) {
                if (G % k2) continue;
                int m = G / k2;
                if (m < 2) continue;
                for (int r = 1; r < m && ns < MAXSPEC; r++) {
                    if (gcd_i(r, m) != 1) continue;
                    if (powmod(r, k2, m) != 1 % m) continue;
                    sm[ns] = m; sk2[ns] = k2; sr[ns] = r; ns++;
                }
            }
            if (ns == 0) continue;
            for (int i = ns - 1; i > 0; i--) {
                int j = rndi(i + 1);
                int t;
                t = sm[i]; sm[i] = sm[j]; sm[j] = t;
                t = sk2[i]; sk2[i] = sk2[j]; sk2[j] = t;
                t = sr[i]; sr[i] = sr[j]; sr[j] = t;
            }
            int lim = ns < 6 ? ns : 6;
            for (int s = 0; s < lim && !found && now() < tend; s++) {
                if (!build_group(sm[s], sk2[s], sr[s])) continue;
                K_ = k;
                alloc_state(2 * k * G_);
                int ok = search(tend, 40000, 6000);
                if (ok && N_ > bestN) {
                    int N = N_, kG = K_ * G_;
                    int cnt = kG * d_;
                    int *ne = malloc(sizeof(int) * 2 * (size_t)cnt);
                    int p = 0;
                    for (int u = 0; u < kG; u++)
                        for (int l = 0; l < d_; l++) {
                            ne[2 * p] = u;
                            ne[2 * p + 1] = nb[l * N + u];
                            p++;
                        }
                    free(bE);
                    bE = ne;
                    bEc = cnt;
                    bestN = N;
                    found = 1;
                }
            }
        }
        if (found) cur = bestN + 1;
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

    budget = max(1.0, min(0.85 * time_limit, time_limit - 9.0))
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), best_n + 1],
                        timeout=budget + 5.0)
        n, e = lib.parse_graph_text(out)
        if n > 0:
            consider(n, e)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
