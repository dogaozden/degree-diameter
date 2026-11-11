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


# Unstructured bipartite search: keep a d-regular bipartite graph, grow it by
# a pair of vertices (one per side) using edge-splitting, then repair the
# diameter defect with degree-preserving edge swaps (simulated annealing on
# the number of ordered pairs at distance > D, computed with bitsets).
C_GROW_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

#define MAXN 2048
#define MAXW (MAXN / 64)
#define MAXDEG 12
#define MAXM (MAXN * MAXDEG / 2 + 64)
#define ITER0 3000
#define ITERMAX 200000
#define TSTART 3.0
#define TEND 0.3

static int d_, D_;
static int N, M, W;
static int side[MAXN], dg[MAXN];
static int adj[MAXN][MAXDEG];
static int ea[MAXM], eb[MAXM];
static int tu[MAXM], tv[MAXM];
static int queue_[MAXN];

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

static u64 BX[MAXN * MAXW], BY[MAXN * MAXW];
static u64 Rcur[MAXN * MAXW], Rnew[MAXN * MAXW];
static int badcur[MAXN], badnew[MAXN];
static long long curcost;

static int sN, sM;
static int sside[MAXN], sdg[MAXN];
static int sadj[MAXN][MAXDEG];
static int sea[MAXM], seb[MAXM];

static int bestN = 0, bestM = 0;
static int bEA[MAXM], bEB[MAXM];

static void set_W(void) { W = (N + 63) / 64; }

static int has_edge(int x, int y) {
    for (int k = 0; k < dg[x]; k++) if (adj[x][k] == y) return 1;
    return 0;
}
static void adj_replace(int x, int oldy, int newy) {
    for (int k = 0; k < dg[x]; k++) if (adj[x][k] == oldy) { adj[x][k] = newy; return; }
}
static void adj_append(int x, int y) { adj[x][dg[x]++] = y; }

/* Edges i=(x1,y1), j=(x2,y2) become (x1,y2), (x2,y1). Self-inverse. */
static void swap_edges(int i, int j) {
    int x1 = ea[i], y1 = eb[i], x2 = ea[j], y2 = eb[j];
    adj_replace(x1, y1, y2);
    adj_replace(y1, x1, x2);
    adj_replace(x2, y2, y1);
    adj_replace(y2, x2, x1);
    eb[i] = y2;
    eb[j] = y1;
}

static void init_complete(int d) {
    N = 2 * d;
    M = 0;
    for (int v = 0; v < N; v++) { side[v] = v < d ? 0 : 1; dg[v] = 0; }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) {
            int bb = d + b;
            adj_append(a, bb);
            adj_append(bb, a);
            ea[M] = a; eb[M] = bb; M++;
        }
    set_W();
}

static int read_input(void) {
    int n, m;
    if (scanf("%d %d", &n, &m) != 2) return 0;
    if (n < 2 || n > MAXN - 2 || m < 1 || m > MAXM) return 0;
    N = n; M = 0;
    for (int v = 0; v < n; v++) { dg[v] = 0; side[v] = -1; }
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return 0;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) return 0;
        if (dg[u] >= d_ || dg[v] >= d_) return 0;
        if (has_edge(u, v)) return 0;
        adj[u][dg[u]++] = v;
        adj[v][dg[v]++] = u;
        tu[e] = u; tv[e] = v;
    }
    for (int v = 0; v < n; v++) if (dg[v] != d_) return 0;
    for (int s = 0; s < n; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int qh = 0, qt = 0;
        queue_[qt++] = s;
        while (qh < qt) {
            int u = queue_[qh++];
            for (int k = 0; k < dg[u]; k++) {
                int w = adj[u][k];
                if (side[w] < 0) { side[w] = 1 - side[u]; queue_[qt++] = w; }
                else if (side[w] == side[u]) return 0;
            }
        }
    }
    for (int e = 0; e < m; e++) {
        int u = tu[e], v = tv[e];
        if (side[u] == 0) { ea[e] = u; eb[e] = v; }
        else { ea[e] = v; eb[e] = u; }
    }
    M = m;
    set_W();
    return 1;
}

/* Bitset reachability within D_ steps; fills Rnew/badnew and returns the cost. */
static long long eval(void) {
    int n = N, w = W;
    u64 *cur = BX, *nxt = BY;
    memset(cur, 0, sizeof(u64) * (size_t)n * (size_t)w);
    for (int v = 0; v < n; v++) cur[(size_t)v * w + (v >> 6)] |= 1ULL << (v & 63);
    for (int t = 0; t < D_; t++) {
        for (int v = 0; v < n; v++) {
            u64 *dst = nxt + (size_t)v * w;
            const u64 *src = cur + (size_t)v * w;
            for (int q = 0; q < w; q++) dst[q] = src[q];
            for (int k = 0; k < dg[v]; k++) {
                const u64 *s2 = cur + (size_t)adj[v][k] * w;
                for (int q = 0; q < w; q++) dst[q] |= s2[q];
            }
        }
        u64 *tmp = cur; cur = nxt; nxt = tmp;
    }
    long long cost = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        const u64 *src = cur + (size_t)v * w;
        for (int q = 0; q < w; q++) c += popc(src[q]);
        badnew[v] = n - c;
        cost += n - c;
    }
    memcpy(Rnew, cur, sizeof(u64) * (size_t)n * (size_t)w);
    return cost;
}

static void accept_new(void) {
    memcpy(Rcur, Rnew, sizeof(u64) * (size_t)N * (size_t)W);
    memcpy(badcur, badnew, sizeof(int) * (size_t)N);
}

/* Split d random edges around two new vertices a=N, b=N+1. Keeps d-regularity. */
static int grow_pair(void) {
    if (N + 2 > MAXN) return 0;
    int d = d_;
    int a = N, b = N + 1;
    side[a] = 0; side[b] = 1;
    dg[a] = 0; dg[b] = 0;
    N += 2;
    set_W();
    for (int it = 0; it < d; it++) {
        int ok = 0;
        for (int tries = 0; tries < 10000 && !ok; tries++) {
            int e = rndi(M);
            int x = ea[e], y = eb[e];
            if (x == a || y == b) continue;
            if (has_edge(a, y)) continue;
            if (has_edge(x, b)) continue;
            adj_replace(x, y, b);
            adj_replace(y, x, a);
            adj_append(a, y);
            adj_append(b, x);
            ea[e] = a; eb[e] = y;
            ea[M] = x; eb[M] = b;
            M++;
            ok = 1;
        }
        if (!ok) return 0;
    }
    return 1;
}

static void save_state(void) {
    sN = N; sM = M;
    memcpy(sside, side, sizeof side);
    memcpy(sdg, dg, sizeof dg);
    memcpy(sadj, adj, sizeof adj);
    memcpy(sea, ea, sizeof(int) * (size_t)M);
    memcpy(seb, eb, sizeof(int) * (size_t)M);
}

static void load_state(void) {
    N = sN; M = sM;
    memcpy(side, sside, sizeof side);
    memcpy(dg, sdg, sizeof dg);
    memcpy(adj, sadj, sizeof adj);
    memcpy(ea, sea, sizeof(int) * (size_t)M);
    memcpy(eb, seb, sizeof(int) * (size_t)M);
    set_W();
}

static void record_best(void) {
    if (N > bestN) {
        bestN = N;
        bestM = M;
        memcpy(bEA, ea, sizeof(int) * (size_t)M);
        memcpy(bEB, eb, sizeof(int) * (size_t)M);
    }
}

/* Degree-preserving swap search. Current state must be in Rcur/badcur/curcost. */
static int repair(long long iters, double tend) {
    if (curcost == 0) return 1;
    for (long long t = 0; t < iters; t++) {
        if ((t & 255) == 0 && now() > tend) return 0;
        double T = TSTART * pow(TEND / TSTART, (double)t / (double)iters);
        int v = -1;
        for (int tries = 0; tries < 64; tries++) {
            int w = rndi(N);
            if (badcur[w] > 0) { v = w; break; }
        }
        if (v < 0) v = rndi(N);
        int i = -1;
        int start = rndi(M);
        for (int q = 0; q < M; q++) {
            int e = start + q;
            if (e >= M) e -= M;
            if (side[v] == 0 ? (ea[e] == v) : (eb[e] == v)) { i = e; break; }
        }
        if (i < 0) continue;
        int j = rndi(M);
        if (j == i) continue;
        int x1 = ea[i], y1 = eb[i], x2 = ea[j], y2 = eb[j];
        if (x1 == x2 || y1 == y2) continue;
        if (has_edge(x1, y2) || has_edge(x2, y1)) continue;
        swap_edges(i, j);
        long long c2 = eval();
        if (c2 <= curcost || rndu() < exp(-(double)(c2 - curcost) / T)) {
            curcost = c2;
            accept_new();
            if (curcost == 0) return 1;
        } else {
            swap_edges(i, j);
        }
    }
    return curcost == 0;
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    if (d_ < 3 || d_ > MAXDEG - 1 || D_ < 2) { printf("0 0\n"); return 0; }
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    double tend = now() + tl;

    if (!read_input()) init_complete(d_);
    curcost = (long long)eval();
    accept_new();
    if (curcost != 0) {
        init_complete(d_);
        curcost = (long long)eval();
        accept_new();
    }
    save_state();

    long long iters = ITER0;
    while (now() < tend) {
        if (curcost == 0) {
            record_best();
            save_state();
            if (!grow_pair()) break;
            curcost = (long long)eval();
            accept_new();
            continue;
        }
        if (repair(iters, tend)) {
            iters = ITER0;
            continue;
        }
        /* Failed: return to the last valid graph and grow again with more effort. */
        iters += iters / 2;
        if (iters > ITERMAX) iters = ITERMAX;
        load_state();
        curcost = (long long)eval();
        accept_new();
    }
    if (curcost == 0) record_best();

    if (bestN == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", bestN, bestM);
    for (int e = 0; e < bestM; e++) printf("%d %d\n", bEA[e], bEB[e]);
    return 0;
}
'''


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _run_engine(source, args, stdin_graph, secs):
    """Run one C engine with a wall-clock limit of about secs; return parsed (n, edges)."""
    out = lib.run_c(source, args, stdin_graph=stdin_graph, timeout=secs + 3.0)
    return lib.parse_graph_text(out)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + time_limit - 6.0  # margin for compilation and process overhead
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

    if d >= 4 and D >= 4:
        # Phase 1: the parent group-lift search gets half of the remaining time.
        p1 = max(0.5, 0.5 * (deadline - time.monotonic()))
        try:
            n, e = _run_engine(C_SOURCE, [d, D, seed, round(p1, 2), best_n + 1], None, p1)
            if n > 0:
                consider(n, e)
        except Exception:
            pass

        # Phase 2: unstructured grow-and-repair, started from the best valid graph so far.
        p2 = deadline - time.monotonic() - 1.0
        if p2 >= 1.0:
            try:
                n, e = _run_engine(C_GROW_SOURCE, [d, D, seed + 1, round(p2, 2)],
                                   best, p2)
                if n > 0:
                    consider(n, e)
            except Exception:
                pass
    else:
        budget = max(0.5, min(0.9 * time_limit, time_limit - 6.0))
        budget = max(0.5, min(budget, time_limit - (time.monotonic() - start) - 4.0))
        try:
            n, e = _run_engine(C_SOURCE, [d, D, seed, round(budget, 2), best_n + 1],
                               None, budget)
            if n > 0:
                consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
