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

/* ---------- group lift search (mode 0) ---------- */

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

static void group_main(double tend, double tl, int minN) {
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

    if (bestN == 0) { printf("0 0\n"); return; }
    printf("%d %d\n", bestN, bEc);
    for (int p = 0; p < bEc; p++) printf("%d %d\n", bE[2 * p], bE[2 * p + 1]);
}

/* ---------- explicit-graph switch annealing with vertex insertion (mode 1) ----------
   Graph is d-regular bipartite. A ids 0..sh-1, B ids sh..2sh-1 (global).
   Move: edge switch a1-b1, a2-b2 -> a1-b2, a2-b1 (keeps degrees and bipartiteness).
   Growth: remove a matching of d-1 edges a_i-b_i, add vertex a' ~ b_i and b' ~ a_i,
   plus edge a'-b'. Degrees stay d; the graph gains 2 vertices. */

static int *snb = NULL;
static int sh = 0;
static int sdeg = 0;
static u64 *sbuf1 = NULL, *sbuf2 = NULL;
static int sW = 0;

static void salloc(int h) {
    free(sbuf1); free(sbuf2);
    sh = h;
    sW = (2 * h + 63) / 64;
    sbuf1 = malloc(sizeof(u64) * (size_t)(2 * h) * sW);
    sbuf2 = malloc(sizeof(u64) * (size_t)(2 * h) * sW);
}

/* Ordered unreached pairs after D_ rounds of bitset ball growth. */
static long long scost(void) {
    int N = 2 * sh, W = sW, d = sdeg, D = D_;
    u64 *cur = sbuf1, *nxt = sbuf2;
    memset(cur, 0, sizeof(u64) * (size_t)N * W);
    for (int v = 0; v < N; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int t = 0; t < D; t++) {
        for (int v = 0; v < N; v++) {
            u64 *dst = nxt + (size_t)v * W;
            const u64 *src = cur + (size_t)v * W;
            for (int w = 0; w < W; w++) dst[w] = src[w];
            for (int j = 0; j < d; j++) {
                const u64 *s2 = cur + (size_t)snb[v * d + j] * W;
                for (int w = 0; w < W; w++) dst[w] |= s2[w];
            }
        }
        u64 *tmp = cur; cur = nxt; nxt = tmp;
    }
    long long cnt = 0;
    for (size_t i = 0; i < (size_t)N * W; i++) cnt += popc(cur[i]);
    return (long long)N * N - cnt;
}

static int shas(int a, int bg) {
    int d = sdeg;
    const int *row = snb + (size_t)a * d;
    for (int j = 0; j < d; j++) if (row[j] == bg) return 1;
    return 0;
}

static void sreplace(int v, int from, int to) {
    int d = sdeg;
    int *row = snb + (size_t)v * d;
    for (int j = 0; j < d; j++) if (row[j] == from) { row[j] = to; return; }
}

/* Load a d-regular bipartite graph from stdin; returns h (side size) or 0. */
static int sload(int d) {
    int n, m;
    if (scanf("%d %d", &n, &m) != 2) return 0;
    if (n < 2 || (n & 1) || m < 0 || m > 4000000) return 0;
    int *eu = malloc(sizeof(int) * (size_t)(m > 0 ? m : 1));
    int *ev = malloc(sizeof(int) * (size_t)(m > 0 ? m : 1));
    for (int i = 0; i < m; i++)
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) return 0;
    int *deg = calloc((size_t)n, sizeof(int));
    for (int i = 0; i < m; i++) {
        int u = eu[i], v = ev[i];
        if (u < 0 || u >= n || v < 0 || v >= n || u == v) return 0;
        deg[u]++; deg[v]++;
        if (deg[u] > d || deg[v] > d) return 0;
    }
    for (int v = 0; v < n; v++) if (deg[v] != d) return 0;
    int *adj = malloc(sizeof(int) * (size_t)n * d);
    int *cnt = calloc((size_t)n, sizeof(int));
    for (int i = 0; i < m; i++) {
        int u = eu[i], v = ev[i];
        adj[u * d + cnt[u]++] = v;
        adj[v * d + cnt[v]++] = u;
    }
    for (int v = 0; v < n; v++)
        for (int j = 0; j < d; j++)
            for (int k = 0; k < j; k++)
                if (adj[v * d + j] == adj[v * d + k]) return 0;
    int *col = malloc(sizeof(int) * (size_t)n);
    int *q = malloc(sizeof(int) * (size_t)n);
    for (int v = 0; v < n; v++) col[v] = -1;
    for (int s = 0; s < n; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int qh = 0, qt = 0;
        q[qt++] = s;
        while (qh < qt) {
            int x = q[qh++];
            for (int j = 0; j < d; j++) {
                int w = adj[x * d + j];
                if (col[w] < 0) { col[w] = 1 - col[x]; q[qt++] = w; }
                else if (col[w] == col[x]) return 0;
            }
        }
    }
    int c0 = 0;
    for (int v = 0; v < n; v++) if (col[v] == 0) c0++;
    if (c0 != n - c0) return 0;
    int *idx = malloc(sizeof(int) * (size_t)n);
    int ca = 0, cb = 0;
    for (int v = 0; v < n; v++) idx[v] = (col[v] == 0) ? ca++ : cb++;
    int h = n / 2;
    sdeg = d;
    free(snb);
    snb = malloc(sizeof(int) * (size_t)2 * h * d);
    for (int v = 0; v < n; v++) {
        int g = (col[v] == 0) ? idx[v] : h + idx[v];
        for (int j = 0; j < d; j++) {
            int w = adj[v * d + j];
            snb[g * d + j] = (col[w] == 0) ? idx[w] : h + idx[w];
        }
    }
    salloc(h);
    return h;
}

/* Insert two vertices (one per side) keeping the graph d-regular bipartite. */
static int sgrow(void) {
    int hh = sh, d = sdeg, m = d - 1;
    if (hh < 1 || m < 1) return 0;
    int *perm = malloc(sizeof(int) * (size_t)hh);
    for (int i = 0; i < hh; i++) perm[i] = i;
    for (int i = hh - 1; i > 0; i--) {
        int j = rndi(i + 1);
        int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
    }
    char *usedB = calloc((size_t)hh, 1);
    int ma[MAXD], mb[MAXD];
    int cnt = 0;
    for (int t = 0; t < hh && cnt < m; t++) {
        int a = perm[t];
        int j = rndi(d);
        int b = snb[a * d + j] - hh;
        if (usedB[b]) continue;
        usedB[b] = 1;
        ma[cnt] = a; mb[cnt] = b; cnt++;
    }
    free(perm); free(usedB);
    if (cnt < m) return 0;

    int h2 = hh + 1, N2 = 2 * h2;
    int *nn = malloc(sizeof(int) * (size_t)N2 * d);
    for (int a = 0; a < hh; a++)
        for (int j = 0; j < d; j++) nn[a * d + j] = snb[a * d + j] + 1;   /* B ids shift by one */
    for (int b = 0; b < hh; b++)
        for (int j = 0; j < d; j++) nn[(h2 + b) * d + j] = snb[(hh + b) * d + j];
    int newA = hh, newB = N2 - 1;
    for (int i = 0; i < m; i++) {
        int a = ma[i], b = mb[i];
        for (int j = 0; j < d; j++) if (nn[a * d + j] == h2 + b) { nn[a * d + j] = newB; break; }
        for (int j = 0; j < d; j++) if (nn[(h2 + b) * d + j] == a) { nn[(h2 + b) * d + j] = newA; break; }
    }
    for (int i = 0; i < m; i++) {
        nn[newA * d + i] = h2 + mb[i];
        nn[newB * d + i] = ma[i];
    }
    nn[newA * d + m] = newB;
    nn[newB * d + m] = newA;
    free(snb);
    snb = nn;
    salloc(h2);
    return 1;
}

/* Edge-switch annealing on the current state; returns 1 as soon as cost 0 is reached. */
static int sanneal(double tend, double T0, double T1, double tstart) {
    int h = sh, d = sdeg;
    if (h < 2) return 0;
    long long c = scost();
    if (c == 0) return 1;
    double span = tend - tstart;
    if (span < 1e-3) span = 1e-3;
    for (;;) {
        double tn = now();
        if (tn >= tend) break;
        double f = (tn - tstart) / span;
        if (f > 1.0) f = 1.0;
        double T = T0 * (1.0 - f) + T1 * f;
        int a1 = rndi(h), a2 = rndi(h - 1);
        if (a2 >= a1) a2++;
        int j1 = rndi(d), j2 = rndi(d);
        int b1 = snb[a1 * d + j1], b2 = snb[a2 * d + j2];
        if (b1 == b2) continue;
        if (shas(a1, b2) || shas(a2, b1)) continue;
        snb[a1 * d + j1] = b2;
        snb[a2 * d + j2] = b1;
        sreplace(b1, a1, a2);
        sreplace(b2, a2, a1);
        long long c2 = scost();
        if (c2 <= c || rndu() < exp(-(double)(c2 - c) / T)) {
            c = c2;
            if (c == 0) return 1;
        } else {
            snb[a1 * d + j1] = b1;
            snb[a2 * d + j2] = b2;
            sreplace(b1, a2, a1);
            sreplace(b2, a1, a2);
        }
    }
    return 0;
}

static void switch_main(double tend) {
    int d = d_;
    int h = sload(d);
    if (h < 2) { printf("0 0\n"); return; }
    if (scost() != 0) { printf("0 0\n"); return; }
    int bestH = h;
    int *bestNB = malloc(sizeof(int) * (size_t)2 * h * d);
    memcpy(bestNB, snb, sizeof(int) * (size_t)2 * h * d);
    while (now() < tend - 0.05) {
        double rem = tend - now();
        double att = rem * 0.5;
        if (att < 1.0) att = rem;
        free(snb);
        snb = malloc(sizeof(int) * (size_t)2 * bestH * d);
        memcpy(snb, bestNB, sizeof(int) * (size_t)2 * bestH * d);
        salloc(bestH);
        if (!sgrow()) continue;
        double ts = now();
        int ok = sanneal(ts + att, 6.0, 0.4, ts);
        if (ok) {
            bestH = sh;
            free(bestNB);
            bestNB = malloc(sizeof(int) * (size_t)2 * sh * d);
            memcpy(bestNB, snb, sizeof(int) * (size_t)2 * sh * d);
        }
    }
    printf("%d %d\n", 2 * bestH, bestH * d);
    for (int a = 0; a < bestH; a++)
        for (int j = 0; j < d; j++)
            printf("%d %d\n", a, bestNB[a * d + j]);
}

int main(int argc, char **argv) {
    if (argc < 6) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    int minN = atoi(argv[5]);
    int mode = argc > 6 ? atoi(argv[6]) : 0;
    if (minN < 2) minN = 2;
    if (d_ < 3 || D_ < 3 || d_ > MAXD) { printf("0 0\n"); return 0; }
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    double tend = now() + tl;
    if (mode == 1) {
        switch_main(tend);
        return 0;
    }
    group_main(tend, tl, minN);
    return 0;
}
'''


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _degree_regular(n, edges, d):
    """True if every vertex has degree exactly d."""
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
    return all(x == d for x in deg)


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

    budget = max(0.5, min(0.85 * time_limit, time_limit - 8.0))

    # Phase 1: group-lift search (C mode 0) gives a regular valid start graph.
    g_budget = round(0.45 * budget, 2)
    group = None
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, g_budget, best_n + 1, 0],
                        timeout=g_budget + 6.0)
        n, e = lib.parse_graph_text(out)
        if n > 0 and lib.is_valid(n, e, d, D):
            group = (n, e)
            consider(n, e)
    except Exception:
        pass

    # Phase 2: grow the regular start by vertex insertion + edge-switch annealing (C mode 1).
    remaining = budget - (time.monotonic() - t0)
    if group is not None and remaining > 1.0 and _degree_regular(group[0], group[1], d):
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed + 1, round(remaining, 2), 0, 1],
                            stdin_graph=group, timeout=remaining + 6.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
