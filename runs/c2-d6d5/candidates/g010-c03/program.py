import time

import lib


# Phase 1 engine: voltage lifts over semidirect groups (parent search, unchanged).
C_VOLT = r'''
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


# Phase 2 engine: unstructured degree-preserving 2-switch annealing on a
# d-regular bipartite graph, minimising ordered pairs at distance > D.
# When a valid graph is reached, it is grown by one vertex per side
# (edge-subdivision style, degrees preserved) and annealed again.
C_ANNEAL = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

#define MAXN 1600
#define MAXW ((MAXN + 63) / 64)
#define MAXDEG 16

static int d_, D_, N = 0, W = 0, NA = 0, NB = 0, bestN = 0, bestM = 0;
static int side[MAXN];
static int nbl[MAXN][MAXDEG];
static int deg[MAXN];
static u64 adj[MAXN][MAXW];
static u64 RA[MAXN * MAXW], RB[MAXN * MAXW];
static int VA[MAXN], VB[MAXN];
static int BE[2 * MAXN * MAXDEG];
static u64 rs = 1;

static u64 rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int n) { return (int)(rnd64() % (u64)n); }
static double rndu(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
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

static int isadj(int a, int b) { return (int)((adj[a][b >> 6] >> (b & 63)) & 1ULL); }
static void setb(int a, int b) { adj[a][b >> 6] |= 1ULL << (b & 63); }
static void clrb(int a, int b) { adj[a][b >> 6] &= ~(1ULL << (b & 63)); }
static void add_bits(int a, int b) { setb(a, b); setb(b, a); }
static void del_bits(int a, int b) { clrb(a, b); clrb(b, a); }

static int findidx(int v, int u) {
    for (int j = 0; j < d_; j++) if (nbl[v][j] == u) return j;
    return -1;
}

/* Remove edges (a,b),(c,e) and add (a,e),(c,b). a,c in A; b,e in B. Self-inverse with
   the arguments (a,e,c,b). Degrees are preserved. */
static void swap_edges(int a, int b, int c, int e) {
    int i;
    i = findidx(a, b); nbl[a][i] = e;
    i = findidx(e, c); nbl[e][i] = a;
    i = findidx(c, e); nbl[c][i] = b;
    i = findidx(b, a); nbl[b][i] = c;
    del_bits(a, b);
    del_bits(c, e);
    add_bits(a, e);
    add_bits(c, b);
}

/* Number of ordered pairs (v,w) with dist(v,w) > D_. */
static long long evalbad(void) {
    u64 *cur = RA, *nxt = RB;
    for (int v = 0; v < N; v++)
        for (int w = 0; w < W; w++) cur[v * W + w] = 0;
    for (int v = 0; v < N; v++) cur[v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int t = 0; t < D_; t++) {
        for (int v = 0; v < N; v++) {
            u64 *dst = nxt + v * W;
            const u64 *src = cur + v * W;
            for (int w = 0; w < W; w++) dst[w] = src[w];
            for (int j = 0; j < d_; j++) {
                const u64 *s2 = cur + nbl[v][j] * W;
                for (int w = 0; w < W; w++) dst[w] |= s2[w];
            }
        }
        u64 *tmp = cur; cur = nxt; nxt = tmp;
    }
    long long cnt = 0;
    for (int v = 0; v < N; v++)
        for (int w = 0; w < W; w++) cnt += popc(cur[v * W + w]);
    return (long long)N * N - cnt;
}

static void init_K(int d) {
    memset(adj, 0, sizeof adj);
    N = 2 * d;
    W = (N + 63) / 64;
    NA = NB = 0;
    for (int a = 0; a < d; a++) { side[a] = 0; VA[NA++] = a; }
    for (int b = 0; b < d; b++) { side[d + b] = 1; VB[NB++] = d + b; }
    for (int a = 0; a < d; a++)
        for (int j = 0; j < d; j++) {
            int b = d + j;
            nbl[a][j] = b;
            nbl[b][a] = a;
            deg[a] = d;
            deg[b] = d;
            add_bits(a, b);
        }
}

/* Reads a d-regular bipartite simple graph with vertices 0..n-1. Returns 0 otherwise. */
static int read_input(void) {
    int n, m;
    memset(adj, 0, sizeof adj);
    if (scanf("%d %d", &n, &m) != 2) return 0;
    if (n < 2 || n > MAXN - 2 || m <= 0) return 0;
    int *eu = malloc(sizeof(int) * (size_t)m);
    int *ev = malloc(sizeof(int) * (size_t)m);
    if (!eu || !ev) return 0;
    for (int i = 0; i < m; i++)
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) { free(eu); free(ev); return 0; }
    int ok = 1;
    N = n;
    W = (N + 63) / 64;
    for (int v = 0; v < N; v++) deg[v] = 0;
    for (int i = 0; i < m; i++) {
        int u = eu[i], v = ev[i];
        if (u < 0 || v < 0 || u >= N || v >= N || u == v) { ok = 0; break; }
        if (deg[u] >= d_ || deg[v] >= d_ || isadj(u, v)) { ok = 0; break; }
        nbl[u][deg[u]++] = v;
        nbl[v][deg[v]++] = u;
        add_bits(u, v);
    }
    free(eu); free(ev);
    if (!ok) return 0;
    for (int v = 0; v < N; v++) if (deg[v] != d_) return 0;

    static int col[MAXN], qq[MAXN];
    for (int v = 0; v < N; v++) col[v] = -1;
    for (int s = 0; s < N; s++) {
        if (col[s] >= 0) continue;
        int h = 0, t = 0;
        col[s] = 0;
        qq[t++] = s;
        while (h < t) {
            int u = qq[h++];
            for (int j = 0; j < d_; j++) {
                int v = nbl[u][j];
                if (col[v] < 0) { col[v] = 1 - col[u]; qq[t++] = v; }
                else if (col[v] == col[u]) return 0;
            }
        }
    }
    NA = NB = 0;
    for (int v = 0; v < N; v++) {
        side[v] = col[v];
        if (col[v] == 0) VA[NA++] = v;
        else VB[NB++] = v;
    }
    return NA == NB && NA > 0;
}

static void save_best(void) {
    int p = 0;
    for (int i = 0; i < NA; i++) {
        int a = VA[i];
        for (int j = 0; j < d_; j++) {
            BE[2 * p] = a;
            BE[2 * p + 1] = nbl[a][j];
            p++;
        }
    }
    bestN = N;
    bestM = p;
}

/* Degree-preserving annealing. Returns 1 as soon as cost is 0, 0 on timeout. */
static int anneal(double tend) {
    long long cur = evalbad();
    if (cur == 0) return 1;
    double t0 = now();
    double span = tend - t0;
    if (span <= 0) return 0;
    double frac = 0.0;
    for (long long it = 0;; it++) {
        if ((it & 63) == 0) {
            double tn = now();
            if (tn >= tend) return 0;
            frac = (tn - t0) / span;
        }
        double T = 2.0 * (1.0 - frac) + 0.2;
        int a = VA[rndi(NA)];
        int b = nbl[a][rndi(d_)];
        int c = VA[rndi(NA)];
        int e = nbl[c][rndi(d_)];
        if (a == c || b == e) continue;
        if (isadj(a, e) || isadj(c, b)) continue;
        swap_edges(a, b, c, e);
        long long c2 = evalbad();
        long long delta = c2 - cur;
        if (delta <= 0 || rndu() < exp(-(double)delta / T)) {
            cur = c2;
            if (cur == 0) return 1;
        } else {
            swap_edges(a, e, c, b);
        }
    }
    return 0;
}

/* Adds one A vertex and one B vertex. Takes d disjoint edges (x,y) and rewires them
   through the new pair: x-nb and na-y. All old degrees are preserved. */
static int grow(void) {
    if (N + 2 > MAXN) return 0;
    int oldNA = NA;
    int xs[MAXDEG], ys[MAXDEG], k = 0;
    long long tries = 0;
    while (k < d_ && tries < 200000) {
        tries++;
        int x = VA[rndi(oldNA)];
        int y = nbl[x][rndi(d_)];
        int ok = 1;
        for (int i = 0; i < k; i++)
            if (xs[i] == x || ys[i] == y) { ok = 0; break; }
        if (ok) { xs[k] = x; ys[k] = y; k++; }
    }
    if (k < d_) return 0;
    int na = N, nb = N + 1;
    N += 2;
    W = (N + 63) / 64;
    side[na] = 0; side[nb] = 1;
    deg[na] = 0; deg[nb] = 0;
    VA[NA++] = na;
    VB[NB++] = nb;
    for (int i = 0; i < k; i++) {
        int x = xs[i], y = ys[i];
        nbl[x][findidx(x, y)] = nb;
        nbl[y][findidx(y, x)] = na;
        del_bits(x, y);
        add_bits(x, nb);
        add_bits(na, y);
        nbl[na][deg[na]++] = y;
        nbl[nb][deg[nb]++] = x;
    }
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    if (d_ < 2 || d_ > MAXDEG || D_ < 1) { printf("0 0\n"); return 0; }
    double tend = now() + tl;
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd64();

    if (!read_input()) init_K(d_);
    long long c = evalbad();
    while (1) {
        if (c != 0) {
            double rem = tend - now();
            if (rem < 0.05) break;
            double lvl = rem > 1.0 ? rem * 0.6 : rem;
            if (!anneal(now() + lvl)) break;
            c = 0;
        }
        save_best();
        if (now() >= tend) break;
        if (!grow()) break;
        c = evalbad();
    }

    if (bestN == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", bestN, bestM);
    for (int p = 0; p < bestM; p++) printf("%d %d\n", BE[2 * p], BE[2 * p + 1]);
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

    # Wall-clock budget: keep a margin for compilation and process start-up.
    usable = max(1.0, time_limit - 8.0)

    # Phase 1: voltage-lift search (parent engine) for a strong structured start.
    b1 = round(usable * 0.5, 2)
    try:
        out = lib.run_c(C_VOLT, [d, D, seed, b1, best_n + 1], timeout=b1 + 3.0)
        n, e = lib.parse_graph_text(out)
        if n > 0:
            consider(n, e)
    except Exception:
        pass

    # Phase 2: unstructured annealing with vertex growth, started from the best graph so far.
    b2 = round(max(0.5, usable - b1), 2)
    try:
        out = lib.run_c(C_ANNEAL, [d, D, seed, b2], stdin_graph=best, timeout=b2 + 3.0)
        n, e = lib.parse_graph_text(out)
        if n > 0:
            consider(n, e)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
