import time

import lib


# Engine 1: the parent's group-lift search (semidirect Z_m x| Z_k2 voltage lifts).
GROUP_SOURCE = r'''
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


# Engine 2 (new): grow a valid graph by adding vertex pairs and repairing it.
# Degree-preserving 2-switches plus deficit-filling moves, annealed on the number
# of unreached ordered pairs (bitset BFS to depth D). Every time a cost-0 state
# is reached, it is saved and a new (A, B) vertex pair is added.
GROW_SOURCE = r'''
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

static int d, D, NC, W, N;
static int *adj, *deg, *side, *dA, *dB, *qbuf, *bestadj, *bestdeg;
static unsigned char *M;
static u64 *R1, *R2;
static int bestN = 0, haveBest = 0;
static int nlog = 0, lu[4], lv[4], lt[4];

static void rawAdd(int u, int v) {
    adj[u * d + deg[u]++] = v;
    adj[v * d + deg[v]++] = u;
    M[(size_t)u * NC + v] = 1;
    M[(size_t)v * NC + u] = 1;
}

static void dropFrom(int u, int v) {
    int *r = adj + (size_t)u * d;
    int k = deg[u];
    for (int j = 0; j < k; j++)
        if (r[j] == v) { r[j] = r[k - 1]; deg[u] = k - 1; return; }
}

static void rawDel(int u, int v) {
    dropFrom(u, v);
    dropFrom(v, u);
    M[(size_t)u * NC + v] = 0;
    M[(size_t)v * NC + u] = 0;
}

static void logAdd(int u, int v) { lu[nlog] = u; lv[nlog] = v; lt[nlog] = 1; nlog++; rawAdd(u, v); }
static void logDel(int u, int v) { lu[nlog] = u; lv[nlog] = v; lt[nlog] = 0; nlog++; rawDel(u, v); }

static void undoLog(void) {
    for (int i = nlog - 1; i >= 0; i--) {
        if (lt[i]) rawDel(lu[i], lv[i]);
        else rawAdd(lu[i], lv[i]);
    }
    nlog = 0;
}

/* Ordered count of vertex pairs at distance > D (0 means valid). */
static long long evalcost(void) {
    int Wn = (N + 63) >> 6;
    for (int v = 0; v < N; v++) {
        u64 *r = R1 + (size_t)v * W;
        for (int w = 0; w < Wn; w++) r[w] = 0;
        r[v >> 6] |= 1ULL << (v & 63);
    }
    for (int t = 0; t < D; t++) {
        for (int v = 0; v < N; v++) {
            u64 *o = R2 + (size_t)v * W;
            const u64 *c = R1 + (size_t)v * W;
            for (int w = 0; w < Wn; w++) o[w] = c[w];
            for (int j = 0; j < deg[v]; j++) {
                const u64 *x = R1 + (size_t)adj[v * d + j] * W;
                for (int w = 0; w < Wn; w++) o[w] |= x[w];
            }
        }
        u64 *sw = R1; R1 = R2; R2 = sw;
    }
    long long cnt = 0;
    for (int v = 0; v < N; v++) {
        const u64 *r = R1 + (size_t)v * W;
        for (int w = 0; w < Wn; w++) cnt += popc(r[w]);
    }
    return (long long)N * N - cnt;
}

static int pickSide(int s) {
    for (int t = 0; t < 64; t++) {
        int v = rndi(N);
        if (side[v] == s && deg[v] > 0) return v;
    }
    return -1;
}

/* Propose one move (logged). Returns 0 if nothing was changed. */
static int proposeMove(void) {
    nlog = 0;
    int nA = 0, nB = 0;
    for (int v = 0; v < N; v++) {
        if (deg[v] < d) {
            if (side[v] == 0) dA[nA++] = v;
            else dB[nB++] = v;
        }
    }
    int r = rndi(100);
    if (nA > 0 && nB > 0 && r < 40) {
        /* Direct fill: add a missing edge between two deficient vertices. */
        int p = dA[rndi(nA)], q = dB[rndi(nB)];
        if (!M[(size_t)p * NC + q]) { logAdd(p, q); return 1; }
    }
    if (nA > 0 && nB > 0 && r < 75) {
        /* Deficit switch: (x,y) -> (x,q), (p,y); moves one unit of deficit to p and q. */
        int x = pickSide(0);
        if (x < 0) return 0;
        int y = adj[x * d + rndi(deg[x])];
        int p = dA[rndi(nA)], q = dB[rndi(nB)];
        if (p == x || q == y) return 0;
        if (M[(size_t)x * NC + q] || M[(size_t)p * NC + y]) return 0;
        logDel(x, y);
        logAdd(x, q);
        logAdd(p, y);
        return 1;
    }
    /* Degree-preserving 2-switch: (x,y),(p,q) -> (x,q),(p,y). */
    int x = pickSide(0);
    if (x < 0) return 0;
    int p = pickSide(0);
    if (p < 0 || p == x) return 0;
    int y = adj[x * d + rndi(deg[x])];
    int q = adj[p * d + rndi(deg[p])];
    if (M[(size_t)x * NC + q] || M[(size_t)p * NC + y] || y == q) return 0;
    logDel(x, y);
    logDel(p, q);
    logAdd(x, q);
    logAdd(p, y);
    return 1;
}

static void saveBest(void) {
    bestN = N;
    haveBest = 1;
    memcpy(bestadj, adj, sizeof(int) * (size_t)NC * d);
    memcpy(bestdeg, deg, sizeof(int) * (size_t)NC);
}

static int growPair(void) {
    if (N + 2 > NC) return 0;
    side[N] = 0;
    side[N + 1] = 1;
    deg[N] = 0;
    deg[N + 1] = 0;
    N += 2;
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 6) { printf("0 0\n"); return 0; }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    int maxadd = atoi(argv[5]);
    if (d < 3 || D < 2 || d > 16 || maxadd < 0) { printf("0 0\n"); return 0; }
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    double tend = now() + tl;

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { n0 = 0; m0 = 0; }
    if (n0 < 0 || m0 < 0) { n0 = 0; m0 = 0; }
    int *eu = NULL, *ev = NULL;
    if (n0 == 0) {
        n0 = 2 * d;
        m0 = d * d;
        eu = malloc(sizeof(int) * (size_t)m0);
        ev = malloc(sizeof(int) * (size_t)m0);
        int c = 0;
        for (int i = 0; i < d; i++)
            for (int j = 0; j < d; j++) { eu[c] = i; ev[c] = d + j; c++; }
    } else {
        eu = malloc(sizeof(int) * (size_t)(m0 + 1));
        ev = malloc(sizeof(int) * (size_t)(m0 + 1));
        for (int i = 0; i < m0; i++) {
            if (scanf("%d %d", &eu[i], &ev[i]) != 2) { m0 = i; break; }
        }
    }

    NC = n0 + 2 * maxadd + 2;
    W = (NC + 63) >> 6;
    adj = malloc(sizeof(int) * (size_t)NC * d);
    deg = calloc((size_t)NC, sizeof(int));
    side = malloc(sizeof(int) * (size_t)NC);
    dA = malloc(sizeof(int) * (size_t)NC);
    dB = malloc(sizeof(int) * (size_t)NC);
    qbuf = malloc(sizeof(int) * (size_t)NC);
    bestadj = malloc(sizeof(int) * (size_t)NC * d);
    bestdeg = malloc(sizeof(int) * (size_t)NC);
    M = calloc((size_t)NC * NC, 1);
    R1 = calloc((size_t)NC * W, sizeof(u64));
    R2 = calloc((size_t)NC * W, sizeof(u64));

    N = n0;
    for (int i = 0; i < m0; i++) {
        int u = eu[i], v = ev[i];
        if (u < 0 || v < 0 || u >= N || v >= N || u == v) continue;
        if (M[(size_t)u * NC + v]) continue;
        if (deg[u] >= d || deg[v] >= d) continue;
        rawAdd(u, v);
    }
    for (int v = 0; v < NC; v++) side[v] = -1;
    for (int s = 0; s < N; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int qh = 0, qt = 0;
        qbuf[qt++] = s;
        while (qh < qt) {
            int u = qbuf[qh++];
            for (int j = 0; j < deg[u]; j++) {
                int w = adj[u * d + j];
                if (side[w] < 0) {
                    side[w] = 1 - side[u];
                    qbuf[qt++] = w;
                }
            }
        }
    }

    long long cost = evalcost();
    if (cost == 0) saveBest();

    int stage_it = 0;
    double T0 = 2.0 + 0.01 * (double)cost;
    long long it = 0;
    const int STAGE = 20000;
    while (1) {
        if ((it & 127) == 0 && now() > tend) break;
        it++;
        if (stage_it >= STAGE) {
            stage_it = 0;
            T0 = 2.0 + 0.01 * (double)cost;
        }
        double frac = (double)stage_it / (double)STAGE;
        double T = T0 * (1.0 - frac) + 0.05;
        stage_it++;
        if (!proposeMove()) continue;
        long long c2 = evalcost();
        if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / T)) {
            cost = c2;
        } else {
            undoLog();
        }
        if (cost == 0) {
            saveBest();
            if (!growPair()) break;
            cost = evalcost();
            stage_it = 0;
            T0 = 2.0 + 0.01 * (double)cost;
        }
    }

    if (!haveBest) { printf("0 0\n"); return 0; }
    long long m = 0;
    for (int u = 0; u < bestN; u++) m += bestdeg[u];
    m /= 2;
    printf("%d %lld\n", bestN, m);
    for (int u = 0; u < bestN; u++)
        for (int j = 0; j < bestdeg[u]; j++) {
            int v = bestadj[u * d + j];
            if (u < v) printf("%d %d\n", u, v);
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

    # Total search time, leaving a margin for compilation and process overhead.
    total = max(3.0, time_limit - 8.0)

    # Phase 1: group-lift search (the parent's construction), about half the time.
    g_budget = max(0.5, 0.5 * total)
    try:
        out = lib.run_c(GROUP_SOURCE, [d, D, seed, round(g_budget, 2), best_n + 1],
                        timeout=g_budget + 3.0)
        n, e = lib.parse_graph_text(out)
        if n > 0:
            consider(n, e)
    except Exception:
        pass

    # Phase 2: grow the best valid graph by adding vertex pairs and repairing.
    elapsed = time.monotonic() - start
    g2 = min(total - elapsed, time_limit - elapsed - 5.0)
    if g2 >= 0.5:
        try:
            out = lib.run_c(GROW_SOURCE, [d, D, seed, round(g2, 2), 150],
                            stdin_graph=best, timeout=g2 + 3.0)
            n, e = lib.parse_graph_text(out)
            if n > 0:
                consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
