import lib


# Arm 1: the parent's voltage-lift search over semidirect groups, unchanged.
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


# Arm 2: direct search on bipartite graphs (no voltage structure). The state is a
# d-regular bipartite graph with A ids even and B ids odd. Edge switches are accepted
# by simulated annealing on the number of ordered pairs at distance > D. Once the graph
# has diameter <= D, two vertices are added (one per side) and the graph is repaired.
DIRECT_C = r'''
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

static int d_, D_;
static int N_, W_, CAP, WCAP;
static int *nb, *perm, *chX, *chY, *usedA, *usedB, *bestnb;
static u64 *rA, *rB;

/* Ordered pairs at distance > D_ (self pairs are always reached). */
static long long bad_pairs(void) {
    int N = N_, W = W_, d = d_;
    u64 *cur = rA, *nxt = rB;
    memset(cur, 0, sizeof(u64) * (size_t)N * (size_t)W);
    for (int v = 0; v < N; v++) cur[(size_t)v * W + (size_t)(v >> 6)] |= 1ULL << (v & 63);
    for (int t = 0; t < D_; t++) {
        for (int v = 0; v < N; v++) {
            u64 *dst = nxt + (size_t)v * W;
            const u64 *src = cur + (size_t)v * W;
            for (int w = 0; w < W; w++) dst[w] = src[w];
            for (int j = 0; j < d; j++) {
                const u64 *su = cur + (size_t)nb[(size_t)v * d + j] * W;
                for (int w = 0; w < W; w++) dst[w] |= su[w];
            }
        }
        u64 *s = cur; cur = nxt; nxt = s;
    }
    long long cnt = 0;
    for (size_t i = 0; i < (size_t)N * W; i++) cnt += popc(cur[i]);
    return (long long)N * N - cnt;
}

static int adjq(int v, int u) {
    int d = d_;
    for (int j = 0; j < d; j++) if (nb[(size_t)v * d + j] == u) return 1;
    return 0;
}

/* In row v, replace neighbour oldu by newu. */
static void repl(int v, int oldu, int newu) {
    int d = d_;
    int *p = nb + (size_t)v * d;
    for (int j = 0; j < d; j++) if (p[j] == oldu) { p[j] = newu; return; }
}

static void swap_apply(int a1, int j1, int b1, int a2, int j2, int b2) {
    int d = d_;
    nb[(size_t)a1 * d + j1] = b2;
    nb[(size_t)a2 * d + j2] = b1;
    repl(b1, a1, a2);
    repl(b2, a2, a1);
}

static void swap_undo(int a1, int j1, int b1, int a2, int j2, int b2) {
    int d = d_;
    nb[(size_t)a1 * d + j1] = b1;
    nb[(size_t)a2 * d + j2] = b2;
    repl(b1, a2, a1);
    repl(b2, a1, a2);
}

static int load_graph(int n, int m, const int *eu, const int *ev) {
    int d = d_;
    if (n <= 0 || (n & 1) || n > CAP) return 0;
    int *deg = calloc((size_t)n, sizeof(int));
    if (!deg) return 0;
    int ok = 1;
    for (int i = 0; i < m && ok; i++) {
        int u = eu[i], v = ev[i];
        if (u < 0 || v < 0 || u >= n || v >= n || u == v || ((u ^ v) & 1) == 0) { ok = 0; break; }
        if (deg[u] >= d || deg[v] >= d) { ok = 0; break; }
        for (int j = 0; j < deg[u]; j++) if (nb[(size_t)u * d + j] == v) { ok = 0; break; }
        if (!ok) break;
        nb[(size_t)u * d + deg[u]++] = v;
        nb[(size_t)v * d + deg[v]++] = u;
    }
    if (ok) for (int v = 0; v < n; v++) if (deg[v] != d) { ok = 0; break; }
    free(deg);
    if (ok) { N_ = n; W_ = (n + 63) / 64; }
    return ok;
}

/* Random d-regular bipartite graph on NA + NA vertices (A = even ids, B = odd ids). */
static int build_random(int NA) {
    int d = d_;
    N_ = 2 * NA;
    W_ = (N_ + 63) / 64;
    for (size_t i = 0; i < (size_t)N_ * d; i++) nb[i] = -1;
    for (int l = 0; l < d; l++) {
        int ok = 0;
        for (int tries = 0; tries < 200000 && !ok; tries++) {
            for (int i = 0; i < NA; i++) perm[i] = i;
            for (int i = NA - 1; i > 0; i--) {
                int j = rndi(i + 1);
                int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
            }
            ok = 1;
            for (int i = 0; i < NA && ok; i++) {
                int a = 2 * i, b = 2 * perm[i] + 1;
                for (int j = 0; j < l; j++) if (nb[(size_t)a * d + j] == b) { ok = 0; break; }
            }
        }
        if (!ok) return 0;
        for (int i = 0; i < NA; i++) {
            int a = 2 * i, b = 2 * perm[i] + 1;
            nb[(size_t)a * d + l] = b;
            nb[(size_t)b * d + l] = a;
        }
    }
    return 1;
}

/* Add one A vertex (id N) and one B vertex (id N+1). Take d edges forming a matching
   (x_i, y_i); reroute x_i to b and y_i to a. Both new vertices get degree d. */
static int grow(void) {
    int d = d_;
    int N = N_;
    int NA = N / 2;
    for (int v = 0; v < N; v++) { usedA[v] = 0; usedB[v] = 0; }
    int cnt = 0;
    for (int tries = 0; tries < 200000 && cnt < d; tries++) {
        int x = 2 * rndi(NA), j = rndi(d);
        int y = nb[(size_t)x * d + j];
        if (usedA[x] || usedB[y]) continue;
        usedA[x] = 1; usedB[y] = 1;
        chX[cnt] = x; chY[cnt] = y; cnt++;
    }
    if (cnt < d) return 0;
    int a = N, b = N + 1;
    for (int i = 0; i < d; i++) {
        int x = chX[i], y = chY[i];
        repl(x, y, b);
        repl(y, x, a);
        nb[(size_t)a * d + i] = y;
        nb[(size_t)b * d + i] = x;
    }
    N_ = N + 2;
    W_ = (N_ + 63) / 64;
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 6) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    int minNA = atoi(argv[5]);
    if (d_ < 3 || d_ > 16 || D_ < 3 || D_ > 30) { printf("0 0\n"); return 0; }
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    double tend = now() + tl;

    double mb = 0.0, pw = 1.0;
    for (int i = 0; i < D_; i++) { mb += pw; pw *= (double)(d_ - 1); if (mb > 1e6) break; }
    double tot = 2.0 * mb;
    long nmax = tot > 3000.0 ? 3000L : (long)tot;
    CAP = (int)nmax + 4;
    if (CAP & 1) CAP++;
    WCAP = (CAP + 63) / 64;
    nb = malloc(sizeof(int) * (size_t)CAP * d_);
    perm = malloc(sizeof(int) * (size_t)CAP);
    chX = malloc(sizeof(int) * (size_t)d_);
    chY = malloc(sizeof(int) * (size_t)d_);
    usedA = calloc((size_t)CAP, sizeof(int));
    usedB = calloc((size_t)CAP, sizeof(int));
    bestnb = malloc(sizeof(int) * (size_t)CAP * d_);
    rA = malloc(sizeof(u64) * (size_t)CAP * WCAP);
    rB = malloc(sizeof(u64) * (size_t)CAP * WCAP);
    if (!nb || !perm || !chX || !chY || !usedA || !usedB || !bestnb || !rA || !rB) {
        printf("0 0\n");
        return 0;
    }

    /* Optional start graph on stdin. */
    int loaded = 0;
    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) == 2 && n0 > 0 && m0 > 0 && n0 <= CAP) {
        int *eu = malloc(sizeof(int) * (size_t)m0);
        int *ev = malloc(sizeof(int) * (size_t)m0);
        int good = (eu != NULL && ev != NULL);
        for (int i = 0; i < m0 && good; i++)
            if (scanf("%d %d", &eu[i], &ev[i]) != 2) good = 0;
        if (good) loaded = load_graph(n0, m0, eu, ev);
        free(eu);
        free(ev);
    }

    if (!loaded) {
        int NA = minNA;
        if (NA < d_ + 1) NA = d_ + 1;
        if (2 * NA > CAP) NA = CAP / 2;
        int okb = 0;
        for (int tr = 0; tr < 40 && !okb && NA > d_; tr++) {
            okb = build_random(NA);
            if (!okb) NA--;
        }
        if (!okb) { printf("0 0\n"); return 0; }
    }

    int haveBest = 0;
    int bestN_ = 0;

    while (now() < tend) {
        long long cost = bad_pairs();
        long long bestc = cost;
        long long since = 0, it = 0;
        long long P = 5LL * N_ + 2000;
        while (cost > 0) {
            if ((it & 31) == 0 && now() > tend) break;
            it++;
            int NA = N_ / 2;
            int a1 = 2 * rndi(NA), j1 = rndi(d_);
            int b1 = nb[(size_t)a1 * d_ + j1];
            int a2 = 2 * rndi(NA), j2 = rndi(d_);
            int b2 = nb[(size_t)a2 * d_ + j2];
            int legal = (a1 != a2) && (b1 != b2) && !adjq(a1, b2) && !adjq(a2, b1);
            if (legal) {
                swap_apply(a1, j1, b1, a2, j2, b2);
                long long c2 = bad_pairs();
                double T = 1.5 + 0.01 * (double)cost;
                if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / T)) {
                    cost = c2;
                } else {
                    swap_undo(a1, j1, b1, a2, j2, b2);
                }
            }
            if (cost < bestc) { bestc = cost; since = 0; }
            else since++;
            if (since > P) break;
        }
        if (cost != 0) break;
        memcpy(bestnb, nb, sizeof(int) * (size_t)N_ * (size_t)d_);
        bestN_ = N_;
        haveBest = 1;
        if (N_ + 2 > CAP) break;
        if (!grow()) break;
    }

    if (!haveBest) { printf("0 0\n"); return 0; }
    long long m = (long long)bestN_ * d_ / 2;
    printf("%d %lld\n", bestN_, m);
    for (int v = 0; v < bestN_; v += 2)
        for (int j = 0; j < d_; j++)
            printf("%d %d\n", v, bestnb[(size_t)v * d_ + j]);
    return 0;
}
'''


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _relabel_even_odd(n, edges):
    """Relabel a bipartite graph so side A gets even ids and side B odd ids. Returns (n, edges) or None."""
    adj = lib.adjacency(n, edges)
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
                elif color[v] == color[u]:
                    return None
    side_a = [v for v in range(n) if color[v] == 0]
    side_b = [v for v in range(n) if color[v] == 1]
    if not side_a or len(side_a) != len(side_b):
        return None
    new = [0] * n
    for i, v in enumerate(side_a):
        new[v] = 2 * i
    for i, v in enumerate(side_b):
        new[v] = 2 * i + 1
    return n, [(new[u], new[v]) for u, v in edges]


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
            return True
        return False

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best  # exact optimum

    if d < 3 or D < 3:
        return best

    budget = max(0.5, min(0.85 * time_limit, time_limit - 8.0))

    # Arm 1: voltage-lift search (the parent's strategy), gets a minority of the budget.
    lift_budget = 0.4 * budget
    try:
        out = lib.run_c(LIFT_C, [d, D, seed, round(lift_budget, 2), best_n + 1],
                        timeout=lift_budget + 6.0)
        n, e = lib.parse_graph_text(out)
        if n > 0:
            consider(n, e)
    except Exception:
        pass

    # Arm 2: direct bipartite annealing + vertex growth, starting from the best graph so far.
    direct_budget = max(0.5, budget - lift_budget - 1.0)
    start = None
    rel = _relabel_even_odd(best[0], best[1])
    if rel is not None:
        start = rel
    try:
        out = lib.run_c(DIRECT_C, [d, D, seed + 1, round(direct_budget, 2), 40],
                        stdin_graph=start, timeout=direct_budget + 6.0)
        n, e = lib.parse_graph_text(out)
        if n > 0:
            consider(n, e)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
