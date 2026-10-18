import time

import lib


# ---------------------------------------------------------------------------
# Phase 1: group-lift search (voltage lifts over Z_m x| Z_k2 with k blocks).
# ---------------------------------------------------------------------------
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


# ---------------------------------------------------------------------------
# Phase 2 (new construction): semi-regular permutation lifts.
# Each layer l pairs A-block i with B-block lay[l][i] (lay[l] is a permutation
# of the k blocks) through an arbitrary bijection P[l][i] of Z_m, not only a
# translation. Vertex A(i,x) ~ B(lay[l][i], P[l][i][x]) for every layer l, so
# the graph is d-regular bipartite on 2*k*m vertices. Cost = unreached pairs
# plus a penalty for multi-edges. Search is annealing with iterated restarts
# from the best valid state, which is extended by one point per block whenever
# it becomes valid, so the order grows step by step.
# ---------------------------------------------------------------------------
C_PERM = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

#define MAXD 8
#define MAXK 2
#define MAXM 1200
#define MAXN 2400
#define MAXW 38

static u64 rs = 1;
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

static int d_, D_, k_, m_, N_, minN_;
static int P_[MAXD][MAXK][MAXM];
static int lay_[MAXD][MAXK];
static int IL_[MAXD][MAXK];          /* IL[l][j] = i with lay[l][i] == j */
static int Q_[MAXD][MAXK][MAXM];     /* Q[l][j][y] = x with P[l][IL[l][j]][x] == y */
static int nb_[MAXN][MAXD];
static u64 RA_[MAXN * MAXW], RB_[MAXN * MAXW];
static u64 *curR_ = RA_;
static int bestN_ = 0, bestM_ = 0;
static int bestE_[2 * MAXN * MAXD];
static int bK_ = 0, bm_ = 0;
static int bP_[MAXD][MAXK][MAXM];
static int bLay_[MAXD][MAXK];

static void build_nb(void) {
    int k = k_, m = m_, d = d_;
    N_ = 2 * k * m;
    for (int l = 0; l < d; l++)
        for (int i = 0; i < k; i++) {
            int j = lay_[l][i];
            IL_[l][j] = i;
            for (int x = 0; x < m; x++) Q_[l][j][P_[l][i][x]] = x;
        }
    for (int i = 0; i < k; i++)
        for (int x = 0; x < m; x++) {
            int v = i * m + x;
            for (int l = 0; l < d; l++)
                nb_[v][l] = k * m + lay_[l][i] * m + P_[l][i][x];
        }
    for (int j = 0; j < k; j++)
        for (int y = 0; y < m; y++) {
            int v = k * m + j * m + y;
            for (int l = 0; l < d; l++)
                nb_[v][l] = IL_[l][j] * m + Q_[l][j][y];
        }
}

/* Cost = unordered pairs at distance > D_ plus 1000 per duplicate neighbour. */
static long long evalcost(void) {
    build_nb();
    int N = N_, d = d_, D = D_, W = (N + 63) >> 6;
    long long dup = 0;
    for (int v = 0; v < N; v++)
        for (int l = 0; l < d; l++)
            for (int l2 = l + 1; l2 < d; l2++)
                if (nb_[v][l] == nb_[v][l2]) dup++;
    u64 *R = RA_, *T = RB_;
    for (int v = 0; v < N; v++) {
        for (int w = 0; w < W; w++) R[v * MAXW + w] = 0;
        R[v * MAXW + (v >> 6)] |= 1ULL << (v & 63);
    }
    for (int t = 0; t < D; t++) {
        for (int v = 0; v < N; v++) {
            u64 *tv = T + v * MAXW;
            const u64 *rv = R + v * MAXW;
            for (int w = 0; w < W; w++) tv[w] = rv[w];
            for (int l = 0; l < d; l++) {
                const u64 *src = R + nb_[v][l] * MAXW;
                for (int w = 0; w < W; w++) tv[w] |= src[w];
            }
        }
        u64 *sw = R; R = T; T = sw;
    }
    long long cnt = 0;
    for (int v = 0; v < N; v++)
        for (int w = 0; w < W; w++) cnt += popc(R[v * MAXW + w]);
    curR_ = R;
    long long unreached = ((long long)N * N - cnt) / 2;
    return unreached + 1000 * dup;
}

static int row_full(int v) {
    int W = (N_ + 63) >> 6, c = 0;
    for (int w = 0; w < W; w++) c += popc(curR_[v * MAXW + w]);
    return c == N_;
}

static void init_random(int m, int k) {
    m_ = m; k_ = k;
    for (int l = 0; l < d_; l++) {
        for (int i = 0; i < k; i++) lay_[l][i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rndi(i + 1);
            int t = lay_[l][i]; lay_[l][i] = lay_[l][j]; lay_[l][j] = t;
        }
        for (int i = 0; i < k; i++) {
            for (int x = 0; x < m; x++) P_[l][i][x] = x;
            for (int x = m - 1; x > 0; x--) {
                int y = rndi(x + 1);
                int t = P_[l][i][x]; P_[l][i][x] = P_[l][i][y]; P_[l][i][y] = t;
            }
        }
    }
}

static int can_extend(void) { return (m_ + 1 <= MAXM) && (2 * k_ * (m_ + 1) <= MAXN); }

static void extend(void) {
    for (int l = 0; l < d_; l++)
        for (int i = 0; i < k_; i++) P_[l][i][m_] = m_;
    m_++;
}

static void swap_p(int l, int i, int x1, int x2) {
    int t = P_[l][i][x1]; P_[l][i][x1] = P_[l][i][x2]; P_[l][i][x2] = t;
}

static void swap_lay(int l, int i1, int i2) {
    int t = lay_[l][i1]; lay_[l][i1] = lay_[l][i2]; lay_[l][i2] = t;
}

/* Called only right after an accepted evaluation with cost 0, so nb_ is current. */
static void save_best(void) {
    int k = k_, m = m_, d = d_;
    int N = 2 * k * m;
    if (N <= bestN_) return;
    int cnt = 0;
    for (int v = 0; v < k * m; v++)
        for (int l = 0; l < d; l++) {
            bestE_[2 * cnt] = v;
            bestE_[2 * cnt + 1] = nb_[v][l];
            cnt++;
        }
    bestN_ = N;
    bestM_ = cnt;
    bK_ = k;
    bm_ = m;
    memcpy(bLay_, lay_, sizeof lay_);
    for (int l = 0; l < d; l++)
        for (int i = 0; i < k; i++)
            memcpy(bP_[l][i], P_[l][i], sizeof(int) * (size_t)m);
}

static void load_best(void) {
    k_ = bK_; m_ = bm_;
    memcpy(lay_, bLay_, sizeof lay_);
    for (int l = 0; l < d_; l++)
        for (int i = 0; i < k_; i++)
            memcpy(P_[l][i], bP_[l][i], sizeof(int) * (size_t)m_);
}

static void perturb(int r) {
    for (int q = 0; q < r; q++) {
        int l = rndi(d_), i = rndi(k_);
        int x1 = rndi(m_), x2 = rndi(m_);
        if (x1 != x2) swap_p(l, i, x1, x2);
    }
}

int main(int argc, char **argv) {
    if (argc < 6) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    minN_ = atoi(argv[5]);
    if (d_ < 3 || d_ > MAXD || D_ < 3) { printf("0 0\n"); return 0; }
    if (minN_ < 2) minN_ = 2;
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    double tend = now() + tl;
    const int patience = 40000;
    const int cycle_len = 6000;

    while (now() < tend) {
        int from_best = (bestN_ > 0) && (rndu() < 0.85);
        if (from_best) {
            load_best();
            if (can_extend()) {
                extend();
                perturb(20);
            } else {
                from_best = 0;
            }
        }
        if (!from_best) {
            int need = minN_ > bestN_ + 2 ? minN_ : bestN_ + 2;
            int k = 1 + rndi(2);
            int m = (need + 2 * k - 1) / (2 * k);
            if (bestN_ == 0) m = (3 * m) / 4;
            if (m < 2) m = 2;
            if (m > MAXM) m = MAXM;
            if (2 * k * m > MAXN) m = MAXN / (2 * k);
            init_random(m, k);
        }

        long long cost = evalcost();
        if (cost == 0) save_best();
        long long since = 0;

        while (now() < tend) {
            if (cost == 0) {
                save_best();
                if (!can_extend()) break;
                extend();
                since = 0;
                cost = evalcost();
                continue;
            }
            if (since > patience) break;
            since++;
            double phase = (double)(since % cycle_len) / (double)cycle_len;
            double T = 0.3 + 3.0 * (1.0 - phase) * (1.0 - phase);
            double r = rndu();
            if (k_ >= 2 && r < 0.2) {
                int l = rndi(d_);
                int i1 = rndi(k_), i2 = rndi(k_ - 1);
                if (i2 >= i1) i2++;
                swap_lay(l, i1, i2);
                long long c2 = evalcost();
                long long dl = c2 - cost;
                if (dl <= 0 || rndu() < exp(-(double)dl / T)) {
                    cost = c2;
                } else {
                    swap_lay(l, i1, i2);
                }
            } else {
                int m = m_, k = k_, N = N_;
                int l = rndi(d_), i = rndi(k), x1 = rndi(m);
                if (rndu() < 0.4) {
                    int start = rndi(N), v = -1;
                    for (int q = 0; q < N; q++) {
                        int w = (start + q) % N;
                        if (!row_full(w)) { v = w; break; }
                    }
                    if (v >= 0) {
                        if (v < k * m) {
                            i = v / m;
                            x1 = v % m;
                        } else {
                            int j = (v - k * m) / m;
                            int y = (v - k * m) % m;
                            i = IL_[l][j];
                            x1 = Q_[l][j][y];
                        }
                    }
                }
                int x2 = rndi(m);
                if (x2 == x1) continue;
                swap_p(l, i, x1, x2);
                long long c2 = evalcost();
                long long dl = c2 - cost;
                if (dl <= 0 || rndu() < exp(-(double)dl / T)) {
                    cost = c2;
                } else {
                    swap_p(l, i, x1, x2);
                }
            }
        }
    }

    if (bestN_ == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", bestN_, bestM_);
    for (int e = 0; e < bestM_; e++) printf("%d %d\n", bestE_[2 * e], bestE_[2 * e + 1]);
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

    budget = max(0.5, min(0.85 * time_limit, time_limit - 8.0))
    g_budget = 0.35 * budget

    # Phase 1: group-lift search gives a valid start graph (kept as a fallback).
    try:
        out = lib.run_c(C_GROUP, [d, D, seed, round(g_budget, 2), best_n + 1],
                        timeout=g_budget + 6.0)
        n, e = lib.parse_graph_text(out)
        if n > 0:
            consider(n, e)
    except Exception:
        pass

    # Phase 2: permutation-lift search, growing from its own best valid state.
    remaining = budget - (time.monotonic() - start)
    p_budget = remaining - 1.0
    if p_budget >= 1.0:
        try:
            out = lib.run_c(C_PERM, [d, D, seed, round(p_budget, 2), best_n + 1],
                            timeout=p_budget + 6.0)
            n, e = lib.parse_graph_text(out)
            if n > 0:
                consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
