import time

import lib


# Stage 1: the parent's group-lift search (unchanged), which produces the record-level base.
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


# Stage 2: NEW construction. Start from a valid d-regular bipartite graph, insert a
# pair of new vertices (a*, b*) by subdividing d matching-like edges
# (a_i,b_i) -> (a*,b_i),(a_i,b*), which keeps all degrees at d. Then repair the
# diameter defects by degree-preserving bipartite edge swaps under simulated
# annealing, using bitset ball-growth cost (number of pairs at distance > D).
# Repeats while time remains. Outputs the largest valid graph reached.
C_GROW = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

#define NMAX 4096
#define WMAX ((NMAX + 63) / 64)

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

static int d_, D_, N_, E_, W_;
static int *ea, *eb;          /* edge e joins A-node ea[e] (colour 0) and B-node eb[e] (colour 1) */
static int *nb;               /* nb[v*d + j] = j-th neighbour of v */
static int *bea, *beb;        /* best valid graph so far */
static int bestN = 0, bestE = 0;
static u64 *R1, *R2;          /* N*W bitsets, reach balls */

static void rebuild_nb(void) {
    int N = N_, d = d_;
    int *deg = calloc((size_t)N, sizeof(int));
    for (int e = 0; e < E_; e++) {
        int a = ea[e], b = eb[e];
        nb[a * d + deg[a]++] = b;
        nb[b * d + deg[b]++] = a;
    }
    free(deg);
}

static long long evalcost(void) {
    int N = N_, W = W_, d = d_;
    memset(R1, 0, sizeof(u64) * (size_t)N * W);
    for (int v = 0; v < N; v++) R1[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int t = 0; t < D_; t++) {
        for (int v = 0; v < N; v++) {
            u64 *out = R2 + (size_t)v * W;
            const u64 *in = R1 + (size_t)v * W;
            for (int w = 0; w < W; w++) out[w] = in[w];
            for (int j = 0; j < d; j++) {
                const u64 *src = R1 + (size_t)nb[v * d + j] * W;
                for (int w = 0; w < W; w++) out[w] |= src[w];
            }
        }
        u64 *sw = R1; R1 = R2; R2 = sw;
    }
    long long cnt = 0;
    for (size_t i = 0; i < (size_t)N * W; i++) cnt += popc(R1[i]);
    return ((long long)N * N - cnt) / 2;   /* unordered pairs at distance > D */
}

static int has_edge(int a, int b) {
    for (int j = 0; j < d_; j++) if (nb[a * d_ + j] == b) return 1;
    return 0;
}

static void repl(int v, int from, int to) {
    for (int j = 0; j < d_; j++)
        if (nb[v * d_ + j] == from) { nb[v * d_ + j] = to; return; }
}

/* Edges e1=(a1,x1), e2=(a2,x2) become (a1,x2), (a2,x1). Applying twice undoes it. */
static int do_swap(int e1, int e2) {
    int a1 = ea[e1], x1 = eb[e1], a2 = ea[e2], x2 = eb[e2];
    if (e1 == e2 || a1 == a2 || x1 == x2) return 0;
    if (has_edge(a1, x2) || has_edge(a2, x1)) return 0;
    repl(a1, x1, x2);
    repl(x1, a1, a2);
    repl(a2, x2, x1);
    repl(x2, a2, a1);
    eb[e1] = x2;
    eb[e2] = x1;
    return 1;
}

static int pick_edge_for(int v) {
    int cnt = 0, pick = -1;
    for (int e = 0; e < E_; e++)
        if (ea[e] == v || eb[e] == v) {
            cnt++;
            if (rndi(cnt) == 0) pick = e;
        }
    return pick;
}

static int deficient(void) {
    int N = N_, W = W_;
    int start = rndi(N);
    for (int q = 0; q < N; q++) {
        int v = (start + q) % N;
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(R1[(size_t)v * W + w]);
        if (c < N) return v;
    }
    return -1;
}

static int anneal(double tend) {
    long long cost = evalcost();
    if (cost == 0) return 1;
    double c0 = (double)cost;
    double T0 = 0.05 * c0 + 0.5;
    double tstart = now();
    double span = tend - tstart;
    if (span < 1e-3) span = 1e-3;
    double T = T0;
    for (long long it = 0;; it++) {
        if ((it & 31) == 0) {
            double tn = now();
            if (tn > tend) return 0;
            double frac = (tn - tstart) / span;
            if (frac > 1.0) frac = 1.0;
            T = T0 * (1.0 - frac) + 0.05;
        }
        int e2 = rndi(E_), e1 = -1;
        if (rndu() < 0.5) {
            int w = deficient();
            if (w >= 0) e1 = pick_edge_for(w);
        }
        if (e1 < 0) e1 = rndi(E_);
        if (e1 == e2) continue;
        if (!do_swap(e1, e2)) continue;
        long long c2 = evalcost();
        if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / T)) {
            cost = c2;
            if (cost == 0) return 1;
        } else {
            do_swap(e1, e2);   /* undo */
        }
    }
}

/* Subdivide d edges with pairwise distinct endpoints into the new vertex pair (a*, b*). */
static int insert_pair(void) {
    int d = d_, N = N_, E0 = E_;
    if (N + 2 > NMAX || d > 64) return 0;
    int pick[64], np = 0;
    for (int tries = 0; np < d && tries < 200000; tries++) {
        int e = rndi(E0);
        int ok = 1;
        for (int i = 0; i < np; i++)
            if (ea[pick[i]] == ea[e] || eb[pick[i]] == eb[e]) { ok = 0; break; }
        if (ok) pick[np++] = e;
    }
    if (np < d) return 0;
    int a = N, b = N + 1;
    for (int i = 0; i < d; i++) {
        int e = pick[i];
        int ai = ea[e], bi = eb[e];
        ea[e] = a;                        /* edge becomes (a*, b_i) */
        ea[E0 + i] = ai;                  /* new edge (a_i, b*) */
        eb[E0 + i] = b;
    }
    E_ = E0 + d;
    N_ = N + 2;
    W_ = (N_ + 63) / 64;
    rebuild_nb();
    return 1;
}

static void save_best(void) {
    bestN = N_;
    bestE = E_;
    memcpy(bea, ea, sizeof(int) * (size_t)E_);
    memcpy(beb, eb, sizeof(int) * (size_t)E_);
}

static void print_input(int n, int m, const int *iu, const int *iv) {
    printf("%d %d\n", n, m);
    for (int e = 0; e < m; e++) printf("%d %d\n", iu[e], iv[e]);
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    if (d_ < 3 || d_ > 16 || D_ < 3) { printf("0 0\n"); return 0; }
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    double tend = now() + tl;

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || m <= 0 || n > NMAX - 2) { printf("0 0\n"); return 0; }
    int *iu = malloc(sizeof(int) * (size_t)m), *iv = malloc(sizeof(int) * (size_t)m);
    for (int e = 0; e < m; e++) {
        if (scanf("%d %d", &iu[e], &iv[e]) != 2 ||
            iu[e] < 0 || iu[e] >= n || iv[e] < 0 || iv[e] >= n) { printf("0 0\n"); return 0; }
    }

    /* Require d-regular and bipartite input; otherwise echo it back unchanged. */
    int *dg = calloc((size_t)n, sizeof(int));
    for (int e = 0; e < m; e++) { dg[iu[e]]++; dg[iv[e]]++; }
    int regular = 1;
    for (int v = 0; v < n; v++) if (dg[v] != d_) regular = 0;
    if (!regular || 2 * m != n * d_) { print_input(n, m, iu, iv); return 0; }

    int *adj = malloc(sizeof(int) * (size_t)n * d_);
    int *fl = calloc((size_t)n, sizeof(int));
    for (int e = 0; e < m; e++) {
        adj[iu[e] * d_ + fl[iu[e]]++] = iv[e];
        adj[iv[e] * d_ + fl[iv[e]]++] = iu[e];
    }
    int *col = malloc(sizeof(int) * (size_t)n);
    int *qu = malloc(sizeof(int) * (size_t)n);
    for (int v = 0; v < n; v++) col[v] = -1;
    int bip = 1;
    for (int s = 0; s < n && bip; s++) {
        if (col[s] != -1) continue;
        col[s] = 0;
        int qh = 0, qt = 0;
        qu[qt++] = s;
        while (qh < qt && bip) {
            int u = qu[qh++];
            for (int j = 0; j < d_; j++) {
                int v = adj[u * d_ + j];
                if (col[v] == -1) { col[v] = 1 - col[u]; qu[qt++] = v; }
                else if (col[v] == col[u]) { bip = 0; break; }
            }
        }
    }
    if (!bip) { print_input(n, m, iu, iv); return 0; }

    N_ = n;
    E_ = m;
    W_ = (N_ + 63) / 64;
    ea = malloc(sizeof(int) * (size_t)NMAX * d_);
    eb = malloc(sizeof(int) * (size_t)NMAX * d_);
    nb = malloc(sizeof(int) * (size_t)NMAX * d_);
    bea = malloc(sizeof(int) * (size_t)NMAX * d_);
    beb = malloc(sizeof(int) * (size_t)NMAX * d_);
    R1 = malloc(sizeof(u64) * (size_t)NMAX * WMAX);
    R2 = malloc(sizeof(u64) * (size_t)NMAX * WMAX);
    for (int e = 0; e < m; e++) {
        if (col[iu[e]] == 0) { ea[e] = iu[e]; eb[e] = iv[e]; }
        else { ea[e] = iv[e]; eb[e] = iu[e]; }
    }
    rebuild_nb();

    if (evalcost() == 0) save_best();
    while (now() < tend) {
        if (!insert_pair()) break;
        if (!anneal(tend)) break;
        save_best();
    }

    if (bestN == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", bestN, bestE);
    for (int e = 0; e < bestE; e++) printf("%d %d\n", bea[e], beb[e]);
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
    t0 = time.monotonic()
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

    total = max(1.0, min(0.85 * time_limit, time_limit - 8.0))

    # Stage 1: group-lift search (parent engine) for a strong base graph.
    b1 = 0.5 * total
    try:
        out = lib.run_c(C_LIFT, [d, D, seed, round(b1, 2), best_n + 1],
                        timeout=b1 + 6.0)
        n, e = lib.parse_graph_text(out)
        if n > 0:
            consider(n, e)
    except Exception:
        pass

    # Stage 2: insert vertex pairs into the best graph and repair by annealing.
    left = total - (time.monotonic() - t0)
    b2 = left - 1.0
    if b2 >= 1.0:
        try:
            out = lib.run_c(C_GROW, [d, D, seed + 1, round(b2, 2)],
                            stdin_graph=best, timeout=b2 + 6.0)
            n, e = lib.parse_graph_text(out)
            if n > 0:
                consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
