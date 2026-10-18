import time

import lib


# Stage 1 engine (unchanged parent search): voltage lifts over small semidirect groups.
LIFT_C = r'''
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
    double slice = tl / 6.0;
    if (slice < 1.0) slice = 1.0;
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
        double gend = now() + slice;
        if (gend > tend) gend = tend;
        int ok = search(gend, 20000, 3000, 6);
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


# Stage 2 engine (new): unstructured local search on a bipartite graph.
# Takes a valid d-regular-ish bipartite graph on stdin, repeatedly inserts one
# A-vertex and one B-vertex (by stealing edges), then repairs diameter defects
# with degree-preserving bipartite double-edge swaps under simulated annealing.
# Keeps the last valid graph and prints it.
REPAIR_C = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

#define NMAX 1400
#define DMAX 16
#define WMAX 22

static u64 rs = 0x123456789ULL;
static u64 rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int n) { return (int)(rnd64() % (u64)n); }
static double rndu(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}
static int popc64(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int d_, D_, n_;
static int deg_[NMAX], col_[NMAX], nb_[NMAX][DMAX];
static unsigned char am_[NMAX][NMAX];
static u64 RA[NMAX][WMAX], RB[NMAX][WMAX];

static int sn_, sdeg_[NMAX], scol_[NMAX], snb_[NMAX][DMAX];
static int q_[NMAX];
static int LA_[NMAX], LB_[NMAX];

static void add_edge(int a, int b) {
    nb_[a][deg_[a]++] = b;
    nb_[b][deg_[b]++] = a;
    am_[a][b] = 1;
    am_[b][a] = 1;
}

static void del_from(int v, int u) {
    for (int i = 0; i < deg_[v]; i++)
        if (nb_[v][i] == u) { nb_[v][i] = nb_[v][--deg_[v]]; return; }
}

static void del_edge(int a, int b) {
    del_from(a, b);
    del_from(b, a);
    am_[a][b] = 0;
    am_[b][a] = 0;
}

/* Number of ordered pairs (x, y) with dist(x, y) > D. Zero means valid. */
static long long cost_fn(void) {
    int n = n_, W = (n + 63) >> 6;
    u64 (*cur)[WMAX] = RA;
    u64 (*nxt)[WMAX] = RB;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) cur[v][w] = 0;
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int t = 0; t < D_; t++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < W; w++) nxt[v][w] = cur[v][w];
            for (int i = 0; i < deg_[v]; i++) {
                int u = nb_[v][i];
                for (int w = 0; w < W; w++) nxt[v][w] |= cur[u][w];
            }
        }
        u64 (*tmp)[WMAX] = cur;
        cur = nxt;
        nxt = tmp;
    }
    long long cnt = 0;
    for (int v = 0; v < n; v++)
        for (int w = 0; w < W; w++) cnt += popc64(cur[v][w]);
    return (long long)n * n - cnt;
}

static int color_all(int n) {
    for (int v = 0; v < n; v++) col_[v] = -1;
    for (int s = 0; s < n; s++) {
        if (col_[s] >= 0) continue;
        int h = 0, t = 0;
        q_[t++] = s;
        col_[s] = 0;
        while (h < t) {
            int v = q_[h++];
            for (int i = 0; i < deg_[v]; i++) {
                int u = nb_[v][i];
                if (col_[u] < 0) { col_[u] = 1 - col_[v]; q_[t++] = u; }
                else if (col_[u] == col_[v]) return 0;
            }
        }
    }
    return 1;
}

static void save_state(void) {
    sn_ = n_;
    for (int v = 0; v < n_; v++) {
        sdeg_[v] = deg_[v];
        scol_[v] = col_[v];
        for (int i = 0; i < deg_[v]; i++) snb_[v][i] = nb_[v][i];
    }
}

static void restore_state(void) {
    for (int v = 0; v < n_; v++)
        for (int u = 0; u < n_; u++) am_[v][u] = 0;
    n_ = sn_;
    for (int v = 0; v < n_; v++) {
        deg_[v] = sdeg_[v];
        col_[v] = scol_[v];
        for (int i = 0; i < deg_[v]; i++) nb_[v][i] = snb_[v][i];
    }
    for (int v = 0; v < n_; v++)
        for (int i = 0; i < deg_[v]; i++) am_[v][nb_[v][i]] = 1;
}

/* Random vertex of the given side with positive degree, among indices < lim. */
static int pick_side(int side, int lim) {
    for (int tries = 0; tries < 100000; tries++) {
        int v = rndi(lim);
        if (col_[v] == side && deg_[v] > 0) return v;
    }
    return -1;
}

static void shuffle_list(int *a, int n) {
    for (int i = n - 1; i > 0; i--) {
        int j = rndi(i + 1);
        int t = a[i]; a[i] = a[j]; a[j] = t;
    }
}

/* Greedily join deficient A vertices to deficient B vertices (never a repeated edge). */
static void fill_deficient(void) {
    for (int round = 0; round < 8; round++) {
        int na = 0, nbb = 0;
        for (int v = 0; v < n_; v++) {
            if (deg_[v] >= d_) continue;
            if (col_[v] == 0) LA_[na++] = v;
            else LB_[nbb++] = v;
        }
        if (na == 0 || nbb == 0) break;
        shuffle_list(LA_, na);
        shuffle_list(LB_, nbb);
        int progress = 0;
        for (int i = 0; i < na; i++) {
            int x = LA_[i];
            for (int j = 0; j < nbb && deg_[x] < d_; j++) {
                int y = LB_[j];
                if (deg_[y] >= d_ || am_[x][y]) continue;
                add_edge(x, y);
                progress = 1;
            }
        }
        if (!progress) break;
    }
}

/* Add one new A vertex and one new B vertex, taking edges away from old vertices. */
static void insert_pair(void) {
    int a = n_, b = n_ + 1, lim = n_;
    n_ += 2;
    col_[a] = 0;
    col_[b] = 1;
    deg_[a] = 0;
    deg_[b] = 0;

    int guard = 0;
    while (deg_[a] < d_ && guard++ < 100000) {
        int x = pick_side(0, lim);
        if (x < 0) break;
        int y = nb_[x][rndi(deg_[x])];
        if (am_[a][y]) continue;
        del_edge(x, y);
        add_edge(a, y);
    }
    guard = 0;
    while (deg_[b] < d_ && guard++ < 100000) {
        int p = pick_side(1, lim);
        if (p < 0) break;
        int q = nb_[p][rndi(deg_[p])];
        if (am_[q][b]) continue;
        del_edge(p, q);
        add_edge(q, b);
    }
    fill_deficient();
}

/* Simulated annealing on degree-preserving bipartite double-edge swaps.
   Returns 1 once the current graph has diameter <= D. */
static int sa_run(double tend, double temp0) {
    long long cost = cost_fn();
    if (cost == 0) return 1;
    double t_start = now();
    double span = tend - t_start;
    if (span < 1e-3) span = 1e-3;
    double T = temp0;
    long long it = 0;
    for (;;) {
        if ((it & 31) == 0) {
            double tn = now();
            if (tn >= tend) break;
            double frac = (tn - t_start) / span;
            T = temp0 * (1.0 - frac) + 0.15;
        }
        it++;
        int a1 = pick_side(0, n_);
        int a2 = pick_side(0, n_);
        if (a1 < 0 || a2 < 0 || a1 == a2) continue;
        int b1 = nb_[a1][rndi(deg_[a1])];
        int b2 = nb_[a2][rndi(deg_[a2])];
        if (b1 == b2 || am_[a1][b2] || am_[a2][b1]) continue;
        del_edge(a1, b1);
        del_edge(a2, b2);
        add_edge(a1, b2);
        add_edge(a2, b1);
        long long c2 = cost_fn();
        if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / T)) {
            cost = c2;
            if (cost == 0) return 1;
        } else {
            del_edge(a1, b2);
            del_edge(a2, b1);
            add_edge(a1, b1);
            add_edge(a2, b2);
        }
    }
    return cost == 0;
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    if (d_ < 3 || d_ > DMAX || D_ < 1) { printf("0 0\n"); return 0; }
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd64();
    double tend = now() + tl;

    int n, m;
    if (scanf("%d %d", &n, &m) != 2 || n < 1 || n > NMAX - 4 || m < 0) { printf("0 0\n"); return 0; }
    memset(am_, 0, sizeof am_);
    for (int v = 0; v < n; v++) deg_[v] = 0;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { printf("0 0\n"); return 0; }
        if (u < 0 || v < 0 || u >= n || v >= n || u == v || am_[u][v] ||
            deg_[u] >= d_ || deg_[v] >= d_) {
            printf("0 0\n");
            return 0;
        }
        add_edge(u, v);
    }
    n_ = n;
    if (!color_all(n_) || cost_fn() != 0) { printf("0 0\n"); return 0; }
    save_state();

    while (n_ + 2 <= NMAX - 2) {
        double rem = tend - now();
        if (rem < 0.3) break;
        double slice = rem < 4.0 ? rem : 4.0;
        insert_pair();
        int ok = sa_run(now() + slice, 4.0);
        if (ok) save_state();
        else restore_state();
    }
    restore_state();

    long long ecount = 0;
    for (int v = 0; v < sn_; v++)
        if (scol_[v] == 0) ecount += sdeg_[v];
    printf("%d %lld\n", sn_, ecount);
    for (int v = 0; v < sn_; v++) {
        if (scol_[v] != 0) continue;
        for (int i = 0; i < sdeg_[v]; i++) printf("%d %d\n", v, snb_[v][i]);
    }
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

    # Stage 1: group-lift search for a large structured start graph.
    lift_budget = 0.45 * budget
    try:
        out = lib.run_c(LIFT_C, [d, D, seed, round(lift_budget, 2), best_n + 1],
                        timeout=lift_budget + 6.0)
        n, e = lib.parse_graph_text(out)
        if n > 0:
            consider(n, e)
    except Exception:
        pass

    # Stage 2: unstructured insertion-and-anneal repair, starting from the best graph so far.
    remaining = budget - (time.monotonic() - start)
    if remaining > 2.0:
        rep_budget = max(0.5, remaining - 1.5)
        try:
            out = lib.run_c(REPAIR_C, [d, D, seed, round(rep_budget, 2)],
                            stdin_graph=(best[0], best[1]), timeout=rep_budget + 6.0)
            n, e = lib.parse_graph_text(out)
            if n > 0:
                consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return lib.haar_graph(d, range(d))
    return best
