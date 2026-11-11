import time

import lib


# Group-lift engine (the parent search): simulated annealing over voltages on
# semidirect-product groups Z_m x| Z_k2 with k blocks per side.
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
static int BL[MAXD][MAXK], BV[MAXD][MAXK];
static int *bE = NULL;
static int bEc = 0, bestN = 0;

/* Group Z_m x| Z_k2 with (a,b)(c,e) = (a + r^b c, b + e). Element a*k2+b. */
static int build_group(int m, int k2, int r) {
    int G = m * k2;
    if (G > GMAX) return 0;
    G_ = G;
    free(MT); free(RS);
    MT = malloc(sizeof(int) * (size_t)G * G);
    RS = malloc(sizeof(int) * (size_t)G * G);
    int *pwr = malloc(sizeof(int) * (size_t)k2);
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
    rch = malloc(sizeof(u64) * (size_t)N);
    tmpr = malloc(sizeof(u64) * (size_t)N);
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

static void apply_dart(int l, int i) { setdart(l, i, lay[l][i], VS[l][i]); }

static void snapshot(void) {
    memcpy(BL, lay, sizeof lay);
    memcpy(BV, VS, sizeof VS);
}

static void restore_snapshot(void) {
    int d = d_, k = K_;
    for (int l = 0; l < d; l++)
        for (int i = 0; i < k; i++) { lay[l][i] = BL[l][i]; VS[l][i] = BV[l][i]; }
    for (int l = 0; l < d; l++)
        for (int i = 0; i < k; i++) apply_dart(l, i);
}

/* Cost = unreached (representative, vertex) pairs + heavy penalty for duplicate darts. */
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

/* Simulated annealing with iterated-local-search kicks from the best state.
   Returns 1 when a valid graph (cost 0) is in the current state. */
static int search(double tend, int iters, int patience, int maxkick) {
    int k = K_, d = d_, G = G_, N = N_;
    u64 full = (1ULL << (2 * k)) - 1;
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
        for (int i = 0; i < k; i++) apply_dart(l, i);
    long long cost = evalcost();
    double c0 = (double)(cost > 0 ? cost : 1);
    long long bestc = cost;
    snapshot();
    int last = 0, kicks = 0;

    for (int t = 0; t < iters && cost != 0; t++) {
        if ((t & 63) == 0 && now() > tend) break;
        if (t - last > patience) {
            if (kicks >= maxkick) break;
            kicks++;
            restore_snapshot();
            for (int q = 0; q < 3; q++) {
                int l = rndi(d), i = rndi(k);
                VS[l][i] = rndi(G);
                apply_dart(l, i);
            }
            cost = evalcost();
            if (cost < bestc) { bestc = cost; snapshot(); }
            last = t;
            continue;
        }
        double temp = 0.02 * c0 * (1.0 - (double)t / iters);
        if (temp < 0.3) temp = 0.3;

        if (k >= 2 && rndu() < 0.25) {
            /* Layer-swap move: exchange the B-targets of two A-blocks in one layer. */
            int l = rndi(d);
            int i1 = rndi(k), i2 = rndi(k - 1);
            if (i2 >= i1) i2++;
            int t1 = lay[l][i1], t2 = lay[l][i2];
            lay[l][i1] = t2; lay[l][i2] = t1;
            apply_dart(l, i1);
            apply_dart(l, i2);
            long long c2 = evalcost();
            if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
            } else {
                lay[l][i1] = t1; lay[l][i2] = t2;
                apply_dart(l, i1);
                apply_dart(l, i2);
            }
        } else {
            /* Voltage move: defect-targeted with probability 0.4, otherwise uniform. */
            int l = 0, i = 0, picked = 0;
            if (rndu() < 0.4) {
                int start = rndi(N), v = -1;
                for (int q = 0; q < N; q++) {
                    int w = (start + q) % N;
                    if (rch[w] != full) { v = w; break; }
                }
                if (v >= 0) {
                    int b = v / G;
                    l = rndi(d);
                    if (b < k) i = b;
                    else {
                        int jb = b - k;
                        i = -1;
                        for (int ii = 0; ii < k; ii++)
                            if (lay[l][ii] == jb) { i = ii; break; }
                        if (i < 0) i = rndi(k);
                    }
                    picked = 1;
                }
            }
            if (!picked) { l = rndi(d); i = rndi(k); }
            int old = VS[l][i];
            int nw = rndi(G);
            if (nw == old) continue;
            VS[l][i] = nw;
            apply_dart(l, i);
            long long c2 = evalcost();
            if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
            } else {
                VS[l][i] = old;
                apply_dart(l, i);
            }
        }
        if (cost < bestc) { bestc = cost; last = t; snapshot(); }
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
    static const int Ks[10] = {1, 1, 1, 2, 2, 2, 3, 3, 4, 5};
    static const int K2s[13] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12};
    static int cand[GMAX + 5];

    while (now() < tend) {
        int k = Ks[rndi(10)];
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
        int ok = search(tend, 20000, 3000, 6);
        if (ok && N_ > bestN) {
            int kG = K_ * G_;
            int cnt = kG * d_;
            int *ne = malloc(sizeof(int) * 2 * (size_t)cnt);
            int p = 0;
            for (int u = 0; u < kG; u++)
                for (int l = 0; l < d_; l++) {
                    ne[2 * p] = u;
                    ne[2 * p + 1] = nb[(size_t)l * N_ + u];
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


# Permutation-lift engine (new): k blocks per side, each of fibre size M.
# Layer l is a perfect matching between A-blocks and B-blocks (lay), and within
# each matched pair the fibre map is an arbitrary bijection (sig), not a group
# element. Cost = unreached pairs + duplicate-dart penalty; SA with defect-
# targeted swaps and ILS kicks.
C_PERM = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

#define MAXD 16
#define MAXK 6
#define NMAX 4000

static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int n) { return (int)(rnd() % (u64)n); }
static double rndu(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}
static int popc(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int d_, D_, k_, M_, N_, W_;
static int *nb = NULL, *sig = NULL, *lay = NULL, *bsig = NULL, *blay = NULL, *defc = NULL;
static u64 *R1 = NULL, *R2 = NULL;

static void setup(int k, int M) {
    k_ = k; M_ = M; N_ = 2 * k * M; W_ = (N_ + 63) / 64;
    free(nb); free(sig); free(lay); free(bsig); free(blay); free(defc); free(R1); free(R2);
    nb = malloc(sizeof(int) * (size_t)N_ * d_);
    sig = malloc(sizeof(int) * (size_t)d_ * k * M);
    bsig = malloc(sizeof(int) * (size_t)d_ * k * M);
    lay = malloc(sizeof(int) * (size_t)d_ * k);
    blay = malloc(sizeof(int) * (size_t)d_ * k);
    defc = malloc(sizeof(int) * (size_t)N_);
    R1 = malloc(sizeof(u64) * (size_t)N_ * W_);
    R2 = malloc(sizeof(u64) * (size_t)N_ * W_);
}

/* Rewrite all darts of layer l from sig and lay. A-vertex i*M+x, B-vertex k*M+j*M+y. */
static void apply_layer(int l) {
    int k = k_, M = M_, d = d_;
    for (int i = 0; i < k; i++) {
        int j = lay[l * k + i];
        const int *s = sig + (size_t)(l * k + i) * M;
        for (int x = 0; x < M; x++) {
            int a = i * M + x;
            int b = k * M + j * M + s[x];
            nb[(size_t)a * d + l] = b;
            nb[(size_t)b * d + l] = a;
        }
    }
}

static void randomize(void) {
    int d = d_, k = k_, M = M_;
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < k; i++) {
            int *s = sig + (size_t)(l * k + i) * M;
            for (int x = 0; x < M; x++) s[x] = x;
            for (int x = M - 1; x > 0; x--) {
                int j = rndi(x + 1);
                int t = s[x]; s[x] = s[j]; s[j] = t;
            }
        }
        int *p = lay + (size_t)l * k;
        for (int i = 0; i < k; i++) p[i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rndi(i + 1);
            int t = p[i]; p[i] = p[j]; p[j] = t;
        }
    }
    for (int l = 0; l < d; l++) apply_layer(l);
}

static void save_best(void) {
    memcpy(bsig, sig, sizeof(int) * (size_t)d_ * k_ * M_);
    memcpy(blay, lay, sizeof(int) * (size_t)d_ * k_);
}

static void load_best(void) {
    memcpy(sig, bsig, sizeof(int) * (size_t)d_ * k_ * M_);
    memcpy(lay, blay, sizeof(int) * (size_t)d_ * k_);
    for (int l = 0; l < d_; l++) apply_layer(l);
}

/* Cost = ordered unreached pairs + 1000 * duplicate darts. Fills defc per vertex. */
static long long evalcost(void) {
    int N = N_, d = d_, W = W_, D = D_;
    u64 *cur = R1, *nxt = R2;
    memset(cur, 0, sizeof(u64) * (size_t)N * (size_t)W);
    for (int v = 0; v < N; v++) cur[(size_t)v * W + (size_t)(v >> 6)] |= 1ULL << (v & 63);
    for (int t = 0; t < D; t++) {
        for (int v = 0; v < N; v++) {
            u64 *o = nxt + (size_t)v * W;
            const u64 *c = cur + (size_t)v * W;
            for (int w = 0; w < W; w++) o[w] = c[w];
            for (int l = 0; l < d; l++) {
                const u64 *c2 = cur + (size_t)nb[(size_t)v * d + l] * W;
                for (int w = 0; w < W; w++) o[w] |= c2[w];
            }
        }
        u64 *sw = cur; cur = nxt; nxt = sw;
    }
    long long unreached = 0;
    for (int v = 0; v < N; v++) {
        const u64 *c = cur + (size_t)v * W;
        int cnt = 0;
        for (int w = 0; w < W; w++) cnt += popc(c[w]);
        defc[v] = N - cnt;
        unreached += N - cnt;
    }
    long long dup = 0;
    for (int v = 0; v < N; v++)
        for (int l = 0; l < d; l++)
            for (int l2 = l + 1; l2 < d; l2++)
                if (nb[(size_t)v * d + l] == nb[(size_t)v * d + l2]) dup++;
    return unreached + 1000LL * dup;
}

static int pick_defect(int *pv) {
    int N = N_;
    for (int tries = 0; tries < 64; tries++) {
        int v = rndi(N);
        if (defc[v] > 0) { *pv = v; return 1; }
    }
    int start = rndi(N);
    for (int q = 0; q < N; q++) {
        int w = (start + q) % N;
        if (defc[w] > 0) { *pv = w; return 1; }
    }
    return 0;
}

/* Swap images of x1 and x2 in sig[l][i]; an involution, so calling twice reverts. */
static void swap_sig(int l, int i, int x1, int x2) {
    int *s = sig + (size_t)(l * k_ + i) * M_;
    int t = s[x1]; s[x1] = s[x2]; s[x2] = t;
    apply_layer(l);
}

/* Swap the B-blocks of A-blocks i1 and i2 in layer l; an involution. */
static void swap_lay(int l, int i1, int i2) {
    int *p = lay + (size_t)l * k_;
    int t = p[i1]; p[i1] = p[i2]; p[i2] = t;
    apply_layer(l);
}

static long long sa(double tend, int patience, int maxkick) {
    int d = d_, k = k_, M = M_;
    double t0 = now();
    double span = tend - t0;
    if (span < 1e-3) span = 1e-3;
    long long cost = evalcost();
    long long bestc = cost;
    save_best();
    long long last = 0;
    int kicks = 0;
    double frac = 0.0;
    for (long long t = 0; cost != 0; t++) {
        if ((t & 31) == 0) {
            double nw = now();
            if (nw > tend) break;
            frac = (nw - t0) / span;
            if (frac > 1.0) frac = 1.0;
        }
        if (t - last > patience) {
            if (kicks >= maxkick) break;
            kicks++;
            load_best();
            for (int q = 0; q < 4; q++) {
                int l = rndi(d), i = rndi(k), x1 = rndi(M), x2 = rndi(M);
                if (x1 != x2) swap_sig(l, i, x1, x2);
            }
            cost = evalcost();
            last = t;
            continue;
        }
        double T = 0.3 + 0.03 * (double)cost * (1.0 - frac);
        if (k >= 2 && rndu() < 0.15) {
            int l = rndi(d);
            int i1 = rndi(k), i2 = rndi(k - 1);
            if (i2 >= i1) i2++;
            swap_lay(l, i1, i2);
            long long c2 = evalcost();
            if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / T)) cost = c2;
            else swap_lay(l, i1, i2);
        } else {
            int l, i, x1, x2, v;
            if (rndu() < 0.5 && pick_defect(&v)) {
                l = rndi(d);
                i = 0; x1 = 0;
                if (v < k * M) {
                    i = v / M; x1 = v % M;
                } else {
                    int u = v - k * M, j = u / M, y = u % M;
                    const int *p = lay + (size_t)l * k;
                    for (int ii = 0; ii < k; ii++) if (p[ii] == j) { i = ii; break; }
                    const int *s = sig + (size_t)(l * k + i) * M;
                    for (int xx = 0; xx < M; xx++) if (s[xx] == y) { x1 = xx; break; }
                }
                x2 = rndi(M);
            } else {
                l = rndi(d); i = rndi(k); x1 = rndi(M); x2 = rndi(M);
            }
            if (x1 == x2) continue;
            swap_sig(l, i, x1, x2);
            long long c2 = evalcost();
            if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / T)) cost = c2;
            else swap_sig(l, i, x1, x2);
        }
        if (cost < bestc) { bestc = cost; last = t; save_best(); }
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
    int bestN = 0, bestEc = 0;
    int *bestE = NULL;
    static const int Ks[8] = {1, 1, 2, 2, 2, 3, 3, 4};

    while (now() < tend) {
        int k = Ks[rndi(8)];
        int Mmin = (minN + 2 * k - 1) / (2 * k);
        int M = Mmin + rndi(3);
        if (M < 2) M = 2;
        if (2 * k * M > NMAX) continue;
        setup(k, M);
        randomize();
        double remain = tend - now();
        double slice = remain * 0.5;
        if (slice < 3.0) slice = remain;
        int ok = (int)sa(now() + slice, 20000, 8);
        if (ok) {
            int N = N_;
            int cnt = k * M * d_;
            int *ne = malloc(sizeof(int) * 2 * (size_t)cnt);
            int p = 0;
            for (int a = 0; a < k * M; a++)
                for (int l = 0; l < d_; l++) {
                    ne[2 * p] = a;
                    ne[2 * p + 1] = nb[(size_t)a * d_ + l];
                    p++;
                }
            free(bestE);
            bestE = ne;
            bestEc = cnt;
            bestN = N;
            minN = N + 1;
        }
    }

    if (bestN == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", bestN, bestEc);
    for (int p = 0; p < bestEc; p++) printf("%d %d\n", bestE[2 * p], bestE[2 * p + 1]);
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

    def left():
        return time_limit - (time.monotonic() - start)

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

    total = max(0.5, min(0.85 * time_limit, time_limit - 8.0))

    # Phase 1: the proven group-lift search gets most of the budget.
    b1 = min(0.75 * total, left() - 8.0)
    if b1 >= 1.0:
        try:
            out = lib.run_c(C_GROUP, [d, D, seed, round(b1, 2), best_n + 1],
                            timeout=b1 + 3.0)
            n, e = lib.parse_graph_text(out)
            if n > 0:
                consider(n, e)
        except Exception:
            pass

    # Phase 2: unstructured permutation lifts, seeded only by the size target.
    b2 = left() - 6.0
    if b2 >= 1.0:
        try:
            out = lib.run_c(C_PERM, [d, D, seed + 7919, round(b2, 2), best_n + 1],
                            timeout=b2 + 3.0)
            n, e = lib.parse_graph_text(out)
            if n > 0:
                consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
