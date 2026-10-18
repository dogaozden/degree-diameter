import time

import lib


C_LIFT = r'''
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


C_REPAIR = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

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

/* General bipartite graph repair: max degree d_, diameter D_, grow by adding
   one A and one B vertex whenever a valid graph is reached.
   Cost = number of ordered vertex pairs at distance > D_. */
static int d_, D_, cap_, W_, N_;
static int *side_, *deg_, *adj_, *dA_, *dB_, *col_, *snapE_;
static unsigned char *am_;
static u64 *R1_, *R2_;
static int snapN_ = 0, snapM_ = 0;

static void add_e(int u, int v) {
    am_[(size_t)u * cap_ + v] = 1;
    am_[(size_t)v * cap_ + u] = 1;
    adj_[u * d_ + deg_[u]] = v; deg_[u]++;
    adj_[v * d_ + deg_[v]] = u; deg_[v]++;
}

static void rm_nb(int u, int v) {
    int dg = deg_[u];
    int *a = adj_ + u * d_;
    for (int i = 0; i < dg; i++)
        if (a[i] == v) { a[i] = a[dg - 1]; deg_[u] = dg - 1; return; }
}

static void del_e(int u, int v) {
    am_[(size_t)u * cap_ + v] = 0;
    am_[(size_t)v * cap_ + u] = 0;
    rm_nb(u, v);
    rm_nb(v, u);
}

static long long cost_eval(void) {
    int N = N_, W = W_, d = d_, Wn = (N + 63) >> 6;
    for (int v = 0; v < N; v++) {
        u64 *r = R1_ + (size_t)v * W;
        for (int w = 0; w < Wn; w++) r[w] = 0;
        r[v >> 6] |= 1ULL << (v & 63);
    }
    for (int t = 0; t < D_; t++) {
        for (int v = 0; v < N; v++) {
            u64 *dst = R2_ + (size_t)v * W;
            const u64 *src = R1_ + (size_t)v * W;
            for (int w = 0; w < Wn; w++) dst[w] = src[w];
            for (int i = 0; i < deg_[v]; i++) {
                const u64 *s2 = R1_ + (size_t)adj_[v * d + i] * W;
                for (int w = 0; w < Wn; w++) dst[w] |= s2[w];
            }
        }
        u64 *tmp = R1_; R1_ = R2_; R2_ = tmp;
    }
    long long unreached = 0;
    for (int v = 0; v < N; v++) {
        const u64 *r = R1_ + (size_t)v * W;
        int cnt = 0;
        for (int w = 0; w < Wn; w++) cnt += popc(r[w]);
        unreached += N - cnt;
    }
    return unreached;
}

static void take_snapshot(void) {
    int N = N_, d = d_, p = 0;
    for (int v = 0; v < N; v++)
        for (int i = 0; i < deg_[v]; i++) {
            int u = adj_[v * d + i];
            if (u > v) { snapE_[2 * p] = v; snapE_[2 * p + 1] = u; p++; }
        }
    snapN_ = N;
    snapM_ = p;
}

static void grow(void) {
    int a = N_, b = N_ + 1;
    side_[a] = 0; side_[b] = 1;
    deg_[a] = 0; deg_[b] = 0;
    N_ += 2;
}

static int handle_valid(long long *cur, long long *bestg, double *T, int *stall) {
    take_snapshot();
    if (N_ + 2 > cap_) return 0;
    grow();
    *cur = cost_eval();
    *bestg = *cur;
    *T = 3.0;
    *stall = 0;
    return 1;
}

static int pick_side(int s) {
    for (int t = 0; t < 400; t++) {
        int v = rndi(N_);
        if (side_[v] == s && deg_[v] > 0) return v;
    }
    return -1;
}

static void apply_move(int nrem, const int *ru, const int *rv,
                       int nadd, const int *au, const int *av) {
    for (int i = 0; i < nrem; i++) del_e(ru[i], rv[i]);
    for (int i = 0; i < nadd; i++) add_e(au[i], av[i]);
}

static void undo_move(int nrem, const int *ru, const int *rv,
                      int nadd, const int *au, const int *av) {
    for (int i = 0; i < nadd; i++) del_e(au[i], av[i]);
    for (int i = 0; i < nrem; i++) add_e(ru[i], rv[i]);
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    int extra = argc > 5 ? atoi(argv[5]) : 200;
    if (d_ < 2 || d_ > 16 || D_ < 2 || extra < 0) { printf("0 0\n"); return 0; }
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    double tend = now() + tl;

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { printf("0 0\n"); return 0; }
    if (n0 < 2 || m0 < 0 || n0 > 5000) { printf("0 0\n"); return 0; }
    int *eu = malloc(sizeof(int) * (size_t)(m0 + 1));
    int *ev = malloc(sizeof(int) * (size_t)(m0 + 1));
    for (int i = 0; i < m0; i++)
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) { printf("0 0\n"); return 0; }

    cap_ = n0 + extra + 2;
    W_ = (cap_ + 63) >> 6;
    am_ = calloc((size_t)cap_ * cap_, 1);
    adj_ = malloc(sizeof(int) * (size_t)cap_ * d_);
    deg_ = calloc((size_t)cap_, sizeof(int));
    side_ = calloc((size_t)cap_, sizeof(int));
    col_ = malloc(sizeof(int) * (size_t)cap_);
    dA_ = malloc(sizeof(int) * (size_t)cap_);
    dB_ = malloc(sizeof(int) * (size_t)cap_);
    R1_ = calloc((size_t)cap_ * W_, sizeof(u64));
    R2_ = calloc((size_t)cap_ * W_, sizeof(u64));
    snapE_ = malloc(sizeof(int) * 2 * (size_t)cap_ * d_);

    N_ = n0;
    for (int i = 0; i < m0; i++) {
        int u = eu[i], v = ev[i];
        if (u < 0 || v < 0 || u >= n0 || v >= n0 || u == v ||
            am_[(size_t)u * cap_ + v] || deg_[u] >= d_ || deg_[v] >= d_) {
            printf("0 0\n");
            return 0;
        }
        add_e(u, v);
    }

    /* Bipartition by BFS 2-colouring. */
    for (int v = 0; v < n0; v++) col_[v] = -1;
    int *q = malloc(sizeof(int) * (size_t)n0);
    for (int s = 0; s < n0; s++) {
        if (col_[s] >= 0) continue;
        int head = 0, tail = 0;
        col_[s] = 0;
        q[tail++] = s;
        while (head < tail) {
            int u = q[head++];
            for (int i = 0; i < deg_[u]; i++) {
                int w = adj_[u * d_ + i];
                if (col_[w] < 0) { col_[w] = 1 - col_[u]; q[tail++] = w; }
                else if (col_[w] == col_[u]) { printf("0 0\n"); return 0; }
            }
        }
    }
    for (int v = 0; v < n0; v++) side_[v] = col_[v];

    long long cur = cost_eval();
    long long bestg = cur;
    double T = 3.0;
    int stall = 0;
    int alive = 1;
    if (cur == 0) alive = handle_valid(&cur, &bestg, &T, &stall);

    const int STALL = 30000;
    long long iter = 0;
    int ru[2], rv[2], au[2], av[2];

    while (alive) {
        if ((iter & 15) == 0 && now() > tend) break;
        iter++;
        int N = N_, d = d_, cap = cap_;
        int nda = 0, ndb = 0;
        for (int v = 0; v < N; v++)
            if (deg_[v] < d) {
                if (side_[v] == 0) dA_[nda++] = v;
                else dB_[ndb++] = v;
            }

        int nrem = 0, nadd = 0, mv = 0;

        /* Fill: add a non-edge between two deficient vertices on opposite sides. */
        if (nda > 0 && ndb > 0 && rndi(100) < 60) {
            for (int t = 0; t < 8 && !mv; t++) {
                int a = dA_[rndi(nda)], b = dB_[rndi(ndb)];
                if (!am_[(size_t)a * cap + b]) {
                    nadd = 1; au[0] = a; av[0] = b; mv = 1;
                }
            }
        }

        if (!mv) {
            if (rndi(2) == 0) {
                /* Degree-preserving 2-switch. */
                int a = pick_side(0), c = pick_side(0);
                if (a >= 0 && c >= 0 && a != c) {
                    int b = adj_[a * d + rndi(deg_[a])];
                    int e = adj_[c * d + rndi(deg_[c])];
                    if (b != e && !am_[(size_t)a * cap + e] && !am_[(size_t)c * cap + b]) {
                        nrem = 2; ru[0] = a; rv[0] = b; ru[1] = c; rv[1] = e;
                        nadd = 2; au[0] = a; av[0] = e; au[1] = c; av[1] = b;
                        mv = 1;
                    }
                }
            } else if (nda + ndb > 0) {
                /* Slide: move one unit of deficiency from an edge end to a deficient vertex x. */
                int x;
                if (nda > 0 && (ndb == 0 || rndi(2) == 0)) x = dA_[rndi(nda)];
                else x = dB_[rndi(ndb)];
                if (side_[x] == 0) {
                    int c = pick_side(0);
                    if (c >= 0 && c != x) {
                        int e = adj_[c * d + rndi(deg_[c])];
                        if (!am_[(size_t)x * cap + e]) {
                            nrem = 1; ru[0] = c; rv[0] = e;
                            nadd = 1; au[0] = x; av[0] = e;
                            mv = 1;
                        }
                    }
                } else {
                    int e = pick_side(1);
                    if (e >= 0 && e != x) {
                        int c = adj_[e * d + rndi(deg_[e])];
                        if (!am_[(size_t)c * cap + x]) {
                            nrem = 1; ru[0] = c; rv[0] = e;
                            nadd = 1; au[0] = c; av[0] = x;
                            mv = 1;
                        }
                    }
                }
            }
        }
        if (!mv) continue;

        apply_move(nrem, ru, rv, nadd, au, av);
        long long c2 = cost_eval();
        long long delta = c2 - cur;
        if (delta <= 0 || rndu() < exp(-(double)delta / T)) {
            cur = c2;
            if (cur < bestg) { bestg = cur; stall = 0; }
            else stall++;
            if (cur == 0) alive = handle_valid(&cur, &bestg, &T, &stall);
        } else {
            undo_move(nrem, ru, rv, nadd, au, av);
            stall++;
        }
        T *= 0.9999;
        if (T < 0.35) T = 0.35;
        if (stall > STALL) { T = 2.5; stall = 0; }
    }

    if (snapM_ == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", snapN_, snapM_);
    for (int p = 0; p < snapM_; p++)
        printf("%d %d\n", snapE_[2 * p], snapE_[2 * p + 1]);
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

    total = max(0.5, min(0.85 * time_limit, time_limit - 8.0))

    # Stage 1: cyclic-group / bi-Cayley lift search (keeps the parent's floor).
    lift_budget = max(0.5, 0.5 * total)
    try:
        out = lib.run_c(C_LIFT, [d, D, seed, round(lift_budget, 2), best_n + 1],
                        timeout=lift_budget + 6.0)
        n, e = lib.parse_graph_text(out)
        if n > 0:
            consider(n, e)
    except Exception:
        pass

    # Stage 2: general bipartite repair search that grows the best graph by
    # adding vertex pairs and re-wiring by annealing. Output is always a valid
    # snapshot, so this stage can only improve the result.
    remaining = total - (time.monotonic() - start)
    if remaining >= 2.0 and best_n >= 2:
        try:
            out = lib.run_c(C_REPAIR, [d, D, seed + 1, round(remaining - 1.0, 2), 200],
                            stdin_graph=best, timeout=remaining + 5.0)
            n, e = lib.parse_graph_text(out)
            if n > 0:
                consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
