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


C_GROW = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

#define PATIENCE 20000

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

static int d_, D_, h_;                 /* h_ = vertices per side */
static int *nbA = NULL, *nbB = NULL;   /* nbA[a*d+s] = B index, nbB[b*d+s] = A index */
static int *sA = NULL, *sB = NULL, sh_ = 0;   /* last valid snapshot (largest valid so far) */
static u64 *R = NULL, *T = NULL;
static size_t Rcap = 0;

static void ensure_buf(size_t need) {
    if (need > Rcap) {
        free(R); free(T);
        R = malloc(sizeof(u64) * need);
        T = malloc(sizeof(u64) * need);
        Rcap = need;
    }
}

/* Returns sum over vertices of unreached vertices (ordered pairs). 0 iff diameter <= D_. */
static long long evalcost(void) {
    int h = h_, d = d_, V = 2 * h, W = (V + 63) / 64;
    size_t tot = (size_t)V * W;
    ensure_buf(tot);
    memset(R, 0, sizeof(u64) * tot);
    for (int v = 0; v < V; v++) R[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int t = 0; t < D_; t++) {
        for (int v = 0; v < V; v++) {
            u64 *out = T + (size_t)v * W;
            const u64 *in = R + (size_t)v * W;
            memcpy(out, in, sizeof(u64) * (size_t)W);
            const int *row = (v < h) ? nbA + (size_t)v * d : nbB + (size_t)(v - h) * d;
            int off = (v < h) ? h : 0;
            for (int s = 0; s < d; s++) {
                const u64 *src = R + (size_t)(row[s] + off) * W;
                for (int w = 0; w < W; w++) out[w] |= src[w];
            }
        }
        u64 *sw = R; R = T; T = sw;
    }
    long long cnt = 0;
    for (size_t i = 0; i < tot; i++) cnt += popc(R[i]);
    return (long long)V * V - cnt;
}

static int findp(const int *row, int d, int x) {
    for (int s = 0; s < d; s++) if (row[s] == x) return s;
    return -1;
}

typedef struct { int a1, s1, a2, s2, b1, b2, j1, j2; } Mv;

/* Double-edge switch: (a1,b1),(a2,b2) -> (a1,b2),(a2,b1). Keeps degrees and simplicity. */
static int propose(Mv *m) {
    int h = h_, d = d_;
    int a1 = rndi(h), s1 = rndi(d), a2 = rndi(h), s2 = rndi(d);
    if (a1 == a2) return 0;
    int b1 = nbA[a1 * d + s1], b2 = nbA[a2 * d + s2];
    if (b1 == b2) return 0;
    if (findp(nbA + (size_t)a1 * d, d, b2) >= 0) return 0;
    if (findp(nbA + (size_t)a2 * d, d, b1) >= 0) return 0;
    int j1 = findp(nbB + (size_t)b1 * d, d, a1);
    int j2 = findp(nbB + (size_t)b2 * d, d, a2);
    if (j1 < 0 || j2 < 0) return 0;
    m->a1 = a1; m->s1 = s1; m->a2 = a2; m->s2 = s2;
    m->b1 = b1; m->b2 = b2; m->j1 = j1; m->j2 = j2;
    nbA[a1 * d + s1] = b2;
    nbA[a2 * d + s2] = b1;
    nbB[b1 * d + j1] = a2;
    nbB[b2 * d + j2] = a1;
    return 1;
}

static void undo_mv(const Mv *m) {
    int d = d_;
    nbA[m->a1 * d + m->s1] = m->b1;
    nbA[m->a2 * d + m->s2] = m->b2;
    nbB[m->b1 * d + m->j1] = m->a1;
    nbB[m->b2 * d + m->j2] = m->a2;
}

/* Insert a new vertex pair (a* in A, b* in B): remove a random matching of size d,
   and rewire each matched edge (a_l, b_l) to (a*, b_l) and (a_l, b*). Keeps d-regularity. */
static int grow_one(void) {
    int h = h_, d = d_;
    int *ua = malloc(sizeof(int) * (size_t)d);
    int *ub = malloc(sizeof(int) * (size_t)d);
    int *us = malloc(sizeof(int) * (size_t)d);
    char *ma = calloc((size_t)h, 1);
    char *mb = calloc((size_t)h, 1);
    int cnt = 0, ok = 0;
    for (long tries = 0; cnt < d && tries < 200000; tries++) {
        int a = rndi(h), s = rndi(d);
        int b = nbA[a * d + s];
        if (ma[a] || mb[b]) continue;
        ma[a] = 1; mb[b] = 1;
        ua[cnt] = a; ub[cnt] = b; us[cnt] = s; cnt++;
    }
    if (cnt == d) {
        ok = 1;
        size_t sz = sizeof(int) * (size_t)(h + 1) * d;
        nbA = realloc(nbA, sz);
        nbB = realloc(nbB, sz);
        for (int l = 0; l < d; l++) {
            int a = ua[l], b = ub[l], s = us[l];
            nbA[a * d + s] = h;                       /* a now adjacent to new B-vertex h */
            int j = findp(nbB + (size_t)b * d, d, a);
            nbB[b * d + j] = h;                       /* b now adjacent to new A-vertex h */
            nbA[h * d + l] = b;                       /* new A-vertex h adjacent to b */
            nbB[h * d + l] = a;                       /* new B-vertex h adjacent to a */
        }
        h_ = h + 1;
    }
    free(ua); free(ub); free(us); free(ma); free(mb);
    return ok;
}

static void save_snapshot(void) {
    size_t sz = sizeof(int) * (size_t)h_ * d_;
    sA = realloc(sA, sz);
    sB = realloc(sB, sz);
    memcpy(sA, nbA, sz);
    memcpy(sB, nbB, sz);
    sh_ = h_;
}

static void restore_snapshot(void) {
    size_t sz = sizeof(int) * (size_t)sh_ * d_;
    memcpy(nbA, sA, sz);
    memcpy(nbB, sB, sz);
    h_ = sh_;
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    if (d_ < 3 || D_ < 3) { printf("0 0\n"); return 0; }
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    double tend = now() + tl;

    int n, m;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || m < 0) { printf("0 0\n"); return 0; }
    int *eu = malloc(sizeof(int) * (size_t)(m + 1));
    int *ev = malloc(sizeof(int) * (size_t)(m + 1));
    for (int i = 0; i < m; i++)
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) { printf("0 0\n"); return 0; }
    int *deg = calloc((size_t)n, sizeof(int));
    for (int i = 0; i < m; i++) {
        if (eu[i] < 0 || eu[i] >= n || ev[i] < 0 || ev[i] >= n || eu[i] == ev[i]) {
            printf("0 0\n"); return 0;
        }
        deg[eu[i]]++;
        deg[ev[i]]++;
    }
    for (int v = 0; v < n; v++) if (deg[v] != d_) { printf("0 0\n"); return 0; }

    int *off = malloc(sizeof(int) * (size_t)(n + 1));
    off[0] = 0;
    for (int v = 0; v < n; v++) off[v + 1] = off[v] + deg[v];
    int *adj = malloc(sizeof(int) * (size_t)(2 * m + 1));
    int *fillc = calloc((size_t)n, sizeof(int));
    for (int i = 0; i < m; i++) {
        int u = eu[i], v = ev[i];
        adj[off[u] + fillc[u]++] = v;
        adj[off[v] + fillc[v]++] = u;
    }

    /* Bipartition by BFS 2-colouring. */
    int *col = malloc(sizeof(int) * (size_t)n);
    for (int v = 0; v < n; v++) col[v] = -1;
    int *stk = malloc(sizeof(int) * (size_t)n);
    for (int s0 = 0; s0 < n; s0++) {
        if (col[s0] != -1) continue;
        int sp = 0;
        col[s0] = 0;
        stk[sp++] = s0;
        while (sp > 0) {
            int u = stk[--sp];
            for (int k = off[u]; k < off[u + 1]; k++) {
                int w = adj[k];
                if (col[w] == -1) { col[w] = 1 - col[u]; stk[sp++] = w; }
                else if (col[w] == col[u]) { printf("0 0\n"); return 0; }
            }
        }
    }
    int c0 = 0, c1 = 0;
    int *idx = malloc(sizeof(int) * (size_t)n);
    for (int v = 0; v < n; v++) idx[v] = (col[v] == 0) ? c0++ : c1++;
    if (c0 != c1 || c0 == 0) { printf("0 0\n"); return 0; }

    h_ = c0;
    int h = h_, d = d_;
    nbA = malloc(sizeof(int) * (size_t)h * d);
    nbB = malloc(sizeof(int) * (size_t)h * d);
    int *fa = calloc((size_t)h, sizeof(int));
    int *fb = calloc((size_t)h, sizeof(int));
    for (int i = 0; i < m; i++) {
        int u = eu[i], v = ev[i];
        if (col[u] == 1) { int t = u; u = v; v = t; }
        int a = idx[u], b = idx[v];
        nbA[a * d + fa[a]++] = b;
        nbB[b * d + fb[b]++] = a;
    }
    /* Reject multi-edges in the input. */
    for (int a = 0; a < h; a++)
        for (int s = 0; s < d; s++)
            for (int t = s + 1; t < d; t++)
                if (nbA[a * d + s] == nbA[a * d + t]) { printf("0 0\n"); return 0; }

    if (evalcost() != 0) { printf("0 0\n"); return 0; }
    save_snapshot();

    /* Growth loop: insert a vertex pair, anneal switches until valid, else roll back. */
    while (now() < tend) {
        if (!grow_one()) continue;
        long long cost = evalcost();
        long long bestc = cost;
        int last = 0;
        double temp = 1.0 + 4.0 * rndu();
        for (int t = 0; cost > 0; t++) {
            if (t - last > PATIENCE) break;
            if ((t & 31) == 0 && now() > tend) break;
            Mv mv;
            if (!propose(&mv)) continue;
            long long c2 = evalcost();
            if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                if (cost < bestc) { bestc = cost; last = t; }
            } else {
                undo_mv(&mv);
            }
        }
        if (cost == 0) save_snapshot();
        else restore_snapshot();
    }

    int bh = sh_;
    printf("%d %d\n", 2 * bh, bh * d_);
    for (int a = 0; a < bh; a++)
        for (int s = 0; s < d_; s++)
            printf("%d %d\n", a, bh + sA[a * d_ + s]);
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

    def elapsed():
        return time.monotonic() - start

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is d-regular.
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

    budget = max(0.5, min(0.9 * time_limit, time_limit - 6.0))
    budget = max(0.5, min(budget, time_limit - elapsed() - 4.0))

    # Stage 1: structured group-lift search (proven engine) on about half the budget.
    stage1 = 0.5 * budget
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(stage1, 2), best_n + 1],
                        timeout=stage1 + 3.0)
        n, e = lib.parse_graph_text(out)
        if n > 0:
            consider(n, e)
    except Exception:
        pass

    # Stage 2: unstructured growth from the best valid graph so far:
    # insert vertex pairs and repair diameter by annealed double-edge switches.
    grow = min(budget - elapsed(), time_limit - elapsed() - 5.0)
    if grow >= 1.0:
        try:
            out = lib.run_c(C_GROW, [d, D, seed + 1, round(grow, 2)],
                            stdin_graph=best, timeout=grow + 3.0)
            n, e = lib.parse_graph_text(out)
            if n > 0:
                consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
