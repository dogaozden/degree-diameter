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
#define XMAXGROW 400
#define XMAXN 3000

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

/* ===================== mode 0: group-lift voltage search ===================== */

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

/* ===================== mode 1: switch-based growth on a general graph ===================== */

static int X_n = 0, X_m = 0, X_cap = 0, X_ecap = 0, X_wm = 1;
static int *X_side = NULL, *X_deg = NULL, *X_nb = NULL;
static int *X_EA = NULL, *X_EB = NULL, *X_SA = NULL, *X_SB = NULL;
static int *X_OA = NULL, *X_OB = NULL;
static int X_sm = 0, X_on = 0, X_om = 0;
static u64 *X_R0 = NULL, *X_R1 = NULL;

static void X_alloc(int cap) {
    X_cap = cap;
    X_wm = (cap + 63) / 64;
    X_ecap = cap * d_ + 16;
    free(X_side); free(X_deg); free(X_nb);
    free(X_EA); free(X_EB); free(X_SA); free(X_SB); free(X_OA); free(X_OB);
    free(X_R0); free(X_R1);
    X_side = calloc(cap, sizeof(int));
    X_deg = calloc(cap, sizeof(int));
    X_nb = calloc((size_t)cap * d_, sizeof(int));
    X_EA = calloc(X_ecap, sizeof(int));
    X_EB = calloc(X_ecap, sizeof(int));
    X_SA = calloc(X_ecap, sizeof(int));
    X_SB = calloc(X_ecap, sizeof(int));
    X_OA = calloc(X_ecap, sizeof(int));
    X_OB = calloc(X_ecap, sizeof(int));
    X_R0 = calloc((size_t)cap * X_wm, sizeof(u64));
    X_R1 = calloc((size_t)cap * X_wm, sizeof(u64));
}

static int X_adj(int a, int b) {
    const int *p = X_nb + (size_t)a * d_;
    int dg = X_deg[a];
    for (int j = 0; j < dg; j++) if (p[j] == b) return 1;
    return 0;
}

static void X_nb_replace(int v, int old, int nw) {
    int *p = X_nb + (size_t)v * d_;
    for (int j = 0; j < X_deg[v]; j++)
        if (p[j] == old) { p[j] = nw; return; }
}

static void X_nb_add(int v, int u) {
    X_nb[(size_t)v * d_ + X_deg[v]] = u;
    X_deg[v]++;
}

static void X_rebuild_nb(void) {
    for (int v = 0; v < X_n; v++) X_deg[v] = 0;
    for (int i = 0; i < X_m; i++) {
        X_nb_add(X_EA[i], X_EB[i]);
        X_nb_add(X_EB[i], X_EA[i]);
    }
}

/* Load a simple bipartite graph with max degree <= d_. Returns 1 on success. */
static int X_load(int n, int m, const int *u, const int *v) {
    X_n = n; X_m = 0;
    for (int i = 0; i < n; i++) X_deg[i] = 0;
    for (int i = 0; i < m; i++) {
        int a = u[i], b = v[i];
        if (a < 0 || b < 0 || a >= n || b >= n || a == b) return 0;
        if (X_deg[a] >= d_ || X_deg[b] >= d_) return 0;
        if (X_adj(a, b)) return 0;
        X_nb_add(a, b);
        X_nb_add(b, a);
    }
    int *q = malloc(sizeof(int) * (size_t)(n > 0 ? n : 1));
    for (int i = 0; i < n; i++) X_side[i] = -1;
    for (int s = 0; s < n; s++) {
        if (X_side[s] >= 0) continue;
        X_side[s] = 0;
        int h = 0, t = 0;
        q[t++] = s;
        while (h < t) {
            int x = q[h++];
            for (int j = 0; j < X_deg[x]; j++) {
                int y = X_nb[(size_t)x * d_ + j];
                if (X_side[y] < 0) { X_side[y] = 1 - X_side[x]; q[t++] = y; }
                else if (X_side[y] == X_side[x]) { free(q); return 0; }
            }
        }
    }
    free(q);
    for (int i = 0; i < m; i++) {
        int a = u[i], b = v[i];
        if (X_side[a] == 1) { int t = a; a = b; b = t; }
        X_EA[X_m] = a; X_EB[X_m] = b; X_m++;
    }
    return 1;
}

static void X_load_kdd(void) {
    int k = d_;
    X_n = 2 * k; X_m = 0;
    for (int i = 0; i < X_n; i++) { X_deg[i] = 0; X_side[i] = (i < k) ? 0 : 1; }
    for (int i = 0; i < k; i++)
        for (int j = 0; j < k; j++) {
            int a = i, b = k + j;
            X_EA[X_m] = a; X_EB[X_m] = b; X_m++;
            X_nb_add(a, b);
            X_nb_add(b, a);
        }
}

/* Add edges between deficient opposite-side vertices (no-op for regular graphs). */
static void X_fill(void) {
    for (int a = 0; a < X_n; a++) {
        if (X_side[a] != 0 || X_deg[a] >= d_) continue;
        for (int b = 0; b < X_n && X_deg[a] < d_; b++) {
            if (X_side[b] != 1 || X_deg[b] >= d_ || X_adj(a, b)) continue;
            if (X_m + 1 >= X_ecap) return;
            X_EA[X_m] = a; X_EB[X_m] = b; X_m++;
            X_nb_add(a, b);
            X_nb_add(b, a);
        }
    }
}

/* Cost = ordered pairs at distance > D_ (0 iff valid diameter). */
static long long X_cost(void) {
    int N = X_n, W = (N + 63) / 64, wm = X_wm, d = d_;
    u64 *A = X_R0, *B = X_R1;
    for (int v = 0; v < N; v++) {
        u64 *p = A + (size_t)v * wm;
        for (int w = 0; w < W; w++) p[w] = 0;
        p[v >> 6] |= 1ULL << (v & 63);
    }
    for (int t = 0; t < D_; t++) {
        for (int v = 0; v < N; v++) {
            u64 *dst = B + (size_t)v * wm;
            const u64 *src = A + (size_t)v * wm;
            for (int w = 0; w < W; w++) dst[w] = src[w];
            int dg = X_deg[v];
            const int *nbv = X_nb + (size_t)v * d;
            for (int j = 0; j < dg; j++) {
                const u64 *su = A + (size_t)nbv[j] * wm;
                for (int w = 0; w < W; w++) dst[w] |= su[w];
            }
        }
        u64 *sw = A; A = B; B = sw;
    }
    long long cnt = 0;
    for (int v = 0; v < N; v++) {
        const u64 *p = A + (size_t)v * wm;
        for (int w = 0; w < W; w++) cnt += popc(p[w]);
    }
    return (long long)N * N - cnt;
}

/* Edge i = (a1,b1), edge j = (a2,b2)  ->  (a1,b2), (a2,b1). Applying it twice reverts. */
static void X_switch(int i, int j) {
    int a1 = X_EA[i], b1 = X_EB[i], a2 = X_EA[j], b2 = X_EB[j];
    X_nb_replace(a1, b1, b2);
    X_nb_replace(b1, a1, a2);
    X_nb_replace(a2, b2, b1);
    X_nb_replace(b2, a2, a1);
    X_EB[i] = b2;
    X_EB[j] = b1;
}

static void X_save(void) {
    X_sm = X_m;
    memcpy(X_SA, X_EA, sizeof(int) * (size_t)X_m);
    memcpy(X_SB, X_EB, sizeof(int) * (size_t)X_m);
}

static void X_restore(void) {
    X_m = X_sm;
    memcpy(X_EA, X_SA, sizeof(int) * (size_t)X_m);
    memcpy(X_EB, X_SB, sizeof(int) * (size_t)X_m);
    X_rebuild_nb();
}

/* Simulated annealing with 2-switch moves at the current vertex count.
   Returns 1 if a valid graph is reached (state left at cost 0). */
static int X_anneal(double tend) {
    long long cur = X_cost();
    if (cur == 0) return 1;
    long long best = cur;
    X_save();
    const int EPOCH = 8000;
    int ep = 0;
    double T0 = 0.5 + 0.01 * (double)cur;
    if (T0 > 10.0) T0 = 10.0;
    const double T1 = 0.3;
    long long iter = 0;
    while (cur > 0) {
        if ((iter & 127) == 0 && now() > tend) break;
        iter++;
        if (ep >= EPOCH) {
            X_restore();
            cur = best;
            ep = 0;
        }
        double T = T0 * pow(T1 / T0, (double)ep / EPOCH);
        ep++;
        int i = rndi(X_m), j = rndi(X_m);
        if (i == j) continue;
        int a1 = X_EA[i], b1 = X_EB[i], a2 = X_EA[j], b2 = X_EB[j];
        if (a1 == a2 || b1 == b2) continue;
        if (X_adj(a1, b2) || X_adj(a2, b1)) continue;
        X_switch(i, j);
        long long nc = X_cost();
        if (nc <= cur || rndu() < exp(-(double)(nc - cur) / T)) {
            cur = nc;
            if (cur < best) { best = cur; X_save(); }
        } else {
            X_switch(i, j);
        }
    }
    if (cur == 0) return 1;
    X_restore();
    return 0;
}

/* Add two vertices x (side 0) and y (side 1), each with d_ edges, by splitting random edges. */
static int X_insert(int x, int y) {
    for (int k = 0; k < d_; k++) {
        int ok = 0;
        for (int tries = 0; tries < 200000 && !ok; tries++) {
            if (X_m + 2 >= X_ecap) return 0;
            int i = rndi(X_m);
            int a = X_EA[i], b = X_EB[i];
            if (a == x || b == y) continue;
            if (X_adj(x, b) || X_adj(a, y)) continue;
            X_nb_replace(a, b, y);
            X_nb_replace(b, a, x);
            X_nb_add(x, b);
            X_nb_add(y, a);
            X_EA[i] = x; X_EB[i] = b;
            X_EA[X_m] = a; X_EB[X_m] = y; X_m++;
            ok = 1;
        }
        if (!ok) return 0;
    }
    return 1;
}

static void run_switch_mode(double tend) {
    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { n0 = 0; m0 = 0; }
    if (n0 < 0 || n0 > XMAXN || m0 < 0 || m0 > 4000000) { n0 = 0; m0 = 0; }
    int *tu = malloc(sizeof(int) * (size_t)(m0 + 1));
    int *tv = malloc(sizeof(int) * (size_t)(m0 + 1));
    int readok = 1;
    for (int i = 0; i < m0; i++)
        if (scanf("%d %d", &tu[i], &tv[i]) != 2) { readok = 0; break; }
    int capn = n0 > 2 * d_ ? n0 : 2 * d_;
    X_alloc(capn + 2 * XMAXGROW);
    int ok = 0;
    if (readok && n0 >= 2) ok = X_load(n0, m0, tu, tv);
    if (!ok) X_load_kdd();
    free(tu); free(tv);
    X_fill();

    X_on = 0; X_om = 0;
    while (1) {
        if (!X_anneal(tend)) break;
        X_on = X_n;
        X_om = X_m;
        memcpy(X_OA, X_EA, sizeof(int) * (size_t)X_m);
        memcpy(X_OB, X_EB, sizeof(int) * (size_t)X_m);
        if (now() > tend) break;
        if (X_n + 2 > X_cap) break;
        int x = X_n, y = X_n + 1;
        X_side[x] = 0; X_side[y] = 1;
        X_deg[x] = 0; X_deg[y] = 0;
        X_n += 2;
        if (!X_insert(x, y)) break;
    }
    if (X_on > 0) {
        printf("%d %d\n", X_on, X_om);
        for (int i = 0; i < X_om; i++) printf("%d %d\n", X_OA[i], X_OB[i]);
    } else {
        printf("0 0\n");
    }
}

/* ===================== main ===================== */

int main(int argc, char **argv) {
    if (argc < 6) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    int minN = atoi(argv[5]);
    int mode = (argc >= 7) ? atoi(argv[6]) : 0;
    if (minN < 2) minN = 2;
    if (d_ < 3 || D_ < 3 || d_ > MAXD) { printf("0 0\n"); return 0; }
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    double tend = now() + tl;
    if (mode == 1) {
        run_switch_mode(tend);
        return 0;
    }

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

    total = max(0.5, min(0.85 * time_limit, time_limit - 8.0))

    # Phase A: group-lift voltage search (finds a strong regular starting graph).
    tA = 0.45 * total
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(tA, 2), best_n + 1, 0],
                        timeout=tA + 6.0)
        n, e = lib.parse_graph_text(out)
        if n > 0:
            consider(n, e)
    except Exception:
        pass

    # Phase B: grow the best graph by inserting vertex pairs and annealing
    # with degree-preserving 2-switches (a general-graph search, not a lift).
    tB = total - tA - 1.0
    if tB >= 2.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed + 1, round(tB, 2), 0, 1],
                            stdin_graph=best, timeout=tB + 6.0)
            n, e = lib.parse_graph_text(out)
            if n > 0:
                consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
