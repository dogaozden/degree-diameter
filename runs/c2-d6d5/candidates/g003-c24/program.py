import time

import lib


# Phase-1 engine: the parent's group-lift search (Z_m x| Z_k2 voltage lifts).
C_GROUP = r'''
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

/* Group Z_m x| Z_k2 with (a,b)(c,e) = (a + r^b c, b + e). */
static int build_group(int m, int k2, int r) {
    int G = m * k2;
    if (G > GMAX) return 0;
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

/* Dart (l, i, j, s): A_{i,g} ~ B_{j, g*s}. */
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
    int Ks[7] = {1, 1, 1, 2, 2, 3, 4};
    int K2s[13] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12};
    static int cand[GMAX + 5];

    while (now() < tend) {
        int k = Ks[rndi(7)];
        if (k > MAXK) k = MAXK;
        int Gmin = (minN + 2 * k - 1) / (2 * k);
        if (Gmin < 2) Gmin = 2;
        Gmin += rndi(Gmin / 30 + 3);
        int k2 = K2s[rndi(13)];
        int m = (Gmin + k2 - 1) / k2;
        if (m < 2) m = 2;
        if (m * k2 > GMAX) continue;
        int nc = 0;
        for (int r = 1; r < m; r++)
            if (gcd_i(r, m) == 1 && powmod(r, k2, m) == 1 % m) cand[nc++] = r;
        if (nc == 0) continue;
        int r = cand[rndi(nc)];
        if (!build_group(m, k2, r)) continue;
        K_ = k;
        alloc_state(2 * k * G_);
        int ok = search(tend, 40000, 6000);
        if (ok && N_ > bestN) {
            int kG = K_ * G_;
            int cnt = kG * d_;
            int *ne = malloc(sizeof(int) * 2 * (size_t)cnt);
            int p = 0;
            for (int u = 0; u < kG; u++)
                for (int l = 0; l < d_; l++) {
                    ne[2 * p] = u;
                    ne[2 * p + 1] = nb[l * N_ + u];
                    p++;
                }
            free(bE);
            bE = ne;
            bEc = cnt;
            bestN = N_;
            minN = N_ + 1;
        }
    }

    if (bestN == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", bestN, bEc);
    for (int p = 0; p < bEc; p++) printf("%d %d\n", bE[2 * p], bE[2 * p + 1]);
    return 0;
}
'''


# Phase-2 engine: a different construction. Simulated annealing over d-regular
# bipartite graphs written as d perfect matchings (permutations between two sides
# of size h). Cost = ordered pairs at distance > D (bitset BFS). Once cost hits 0,
# the graph is saved and grown by one vertex per side, then annealing continues.
C_ANNEAL = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

#define MAXD 12
#define MAXH 1000
#define MAXW ((2 * MAXH + 63) / 64)

static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int n) { return (int)(rnd() % (u64)n); }
static double rndu(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }
static int popc(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int d_, D_, h_;
static int P[MAXD][MAXH];   /* A index i -> B index P[l][i] */
static int Q[MAXD][MAXH];   /* B index j -> A index Q[l][j] */
static int bestP[MAXD][MAXH];
static int besth = 0;
static u64 bufA[2 * MAXH * MAXW], bufB[2 * MAXH * MAXW];
static unsigned char seen[MAXH * MAXH];

static void rebuildQ(void) {
    for (int l = 0; l < d_; l++)
        for (int i = 0; i < h_; i++) Q[l][P[l][i]] = i;
}

/* Vertices: A i -> i, B j -> h + j. Returns number of ordered non-self pairs at distance > D. */
static long long evalc(void) {
    int h = h_, N = 2 * h, d = d_, W = (N + 63) >> 6;
    u64 *cur = bufA, *nxt = bufB;
    memset(cur, 0, sizeof(u64) * (size_t)N * W);
    for (int v = 0; v < N; v++) cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int t = 0; t < D_; t++) {
        for (int v = 0; v < N; v++) {
            u64 *dst = nxt + (size_t)v * W;
            const u64 *src = cur + (size_t)v * W;
            for (int w = 0; w < W; w++) dst[w] = src[w];
            if (v < h) {
                for (int l = 0; l < d; l++) {
                    const u64 *s = cur + (size_t)(h + P[l][v]) * W;
                    for (int w = 0; w < W; w++) dst[w] |= s[w];
                }
            } else {
                for (int l = 0; l < d; l++) {
                    const u64 *s = cur + (size_t)Q[l][v - h] * W;
                    for (int w = 0; w < W; w++) dst[w] |= s[w];
                }
            }
        }
        u64 *tmp = cur; cur = nxt; nxt = tmp;
    }
    long long cnt = 0;
    for (int v = 0; v < N; v++) {
        const u64 *s = cur + (size_t)v * W;
        for (int w = 0; w < W; w++) cnt += popc(s[w]);
    }
    return (long long)N * N - cnt;
}

static void init_random(int h) {
    h_ = h;
    for (int l = 0; l < d_; l++) {
        for (int i = 0; i < h; i++) P[l][i] = i;
        for (int i = h - 1; i > 0; i--) {
            int j = rndi(i + 1);
            int t = P[l][i]; P[l][i] = P[l][j]; P[l][j] = t;
        }
    }
    rebuildQ();
}

/* Add one A vertex and one B vertex, keeping each layer a permutation. */
static void grow(void) {
    int h = h_;
    for (int l = 0; l < d_; l++) {
        P[l][h] = h;
        int r = rndi(h + 1);
        int t = P[l][r]; P[l][r] = P[l][h]; P[l][h] = t;
    }
    h_ = h + 1;
    rebuildQ();
}

static void save_best(void) {
    besth = h_;
    for (int l = 0; l < d_; l++)
        for (int i = 0; i < h_; i++) bestP[l][i] = P[l][i];
}

static void anneal(double tl) {
    double tend = now() + tl;
    const double T0 = 6.0, T1 = 0.4;
    const long long S = 8000;
    long long cost = evalc();
    long long it = 0;
    while (1) {
        if ((it & 127) == 0 && now() > tend) break;
        if (cost == 0) {
            save_best();
            if (h_ >= MAXH - 2) break;
            grow();
            cost = evalc();
            it++;
            continue;
        }
        double frac = (double)(it % S) / (double)S;
        double T = T0 * pow(T1 / T0, frac);
        int l = rndi(d_);
        int i1 = rndi(h_), i2 = rndi(h_ - 1);
        if (i2 >= i1) i2++;
        int a = P[l][i1], b = P[l][i2];
        P[l][i1] = b; P[l][i2] = a;
        Q[l][b] = i1; Q[l][a] = i2;
        long long c2 = evalc();
        if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / T)) {
            cost = c2;
        } else {
            P[l][i1] = a; P[l][i2] = b;
            Q[l][a] = i1; Q[l][b] = i2;
        }
        it++;
    }
}

int main(int argc, char **argv) {
    if (argc < 6) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    int h0 = atoi(argv[5]);
    if (d_ < 2 || d_ > MAXD || D_ < 1) { printf("0 0\n"); return 0; }
    if (h0 < 4) h0 = 4;
    if (h0 > MAXH - 2) h0 = MAXH - 2;
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    init_random(h0);
    anneal(tl);

    if (besth == 0) { printf("0 0\n"); return 0; }
    int h = besth, N = 2 * h, d = d_;
    int *E = malloc(sizeof(int) * 2 * (size_t)h * d);
    int cnt = 0;
    for (int l = 0; l < d; l++)
        for (int i = 0; i < h; i++) {
            int j = bestP[l][i];
            if (!seen[i * h + j]) {
                seen[i * h + j] = 1;
                E[2 * cnt] = i;
                E[2 * cnt + 1] = h + j;
                cnt++;
            }
        }
    printf("%d %d\n", N, cnt);
    for (int p = 0; p < cnt; p++) printf("%d %d\n", E[2 * p], E[2 * p + 1]);
    free(E);
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
    end_by = start + max(3.0, time_limit - 5.0)
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        try:
            if n > best_n and lib.is_valid(n, e, d, D):
                best = (n, e)
                best_n = n
        except Exception:
            pass

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best  # exact optimum

    if d < 3 or D < 3:
        return best

    # Phase 1: the proven group-lift search, given a share of the time.
    rem = end_by - time.monotonic()
    b1 = max(0.5, 0.4 * rem)
    try:
        out = lib.run_c(C_GROUP, [d, D, seed, round(b1, 2), best_n + 1],
                        timeout=b1 + 4.0)
        n, e = lib.parse_graph_text(out)
        if n > 0:
            consider(n, e)
    except Exception:
        pass

    # Phase 2: a different construction. Anneal d-regular bipartite graphs
    # (d permutations) grown from a small size; this is independent of phase 1.
    rem = end_by - time.monotonic()
    b2 = rem - 3.0
    if b2 >= 1.0:
        try:
            out = lib.run_c(C_ANNEAL, [d, D, seed, round(b2, 2), 8],
                            timeout=b2 + 4.0)
            n, e = lib.parse_graph_text(out)
            if n > 0:
                consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
