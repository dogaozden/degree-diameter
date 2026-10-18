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
    /* Per-group time slice: keeps one unlucky group from eating the budget. */
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


C_REPAIR = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

#define MAXN 2048
#define MAXDEG 16
#define MAXW ((MAXN + 63) / 64)
#define MAXE (MAXN * MAXDEG)
#define PHASE 20000

typedef u64 Row[MAXW];

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

static int NV, DEG, DIA, W;
static int side[MAXN], deg_[MAXN], adj_[MAXN][MAXDEG];
static int lst[2][MAXN], cntS[2];
static Row RA[MAXN], RB[MAXN];
static int bestE[2 * MAXE];
static int bestM = 0, bestNv = 0;
static long long cur_cost;
static int qbuf[MAXN];

/* Count ordered pairs at distance > DIA, halved. */
static long long evalcost(void) {
    Row *cur = RA, *nxt = RB;
    for (int v = 0; v < NV; v++) {
        for (int w = 0; w < W; w++) cur[v][w] = 0;
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int t = 0; t < DIA; t++) {
        for (int v = 0; v < NV; v++) {
            for (int w = 0; w < W; w++) nxt[v][w] = cur[v][w];
            for (int i = 0; i < deg_[v]; i++) {
                int u = adj_[v][i];
                for (int w = 0; w < W; w++) nxt[v][w] |= cur[u][w];
            }
        }
        Row *sw = cur; cur = nxt; nxt = sw;
    }
    long long tot = 0;
    for (int v = 0; v < NV; v++)
        for (int w = 0; w < W; w++) tot += popc(cur[v][w]);
    return ((long long)NV * NV - tot) / 2;
}

static int isadj(int a, int b) {
    for (int i = 0; i < deg_[a]; i++) if (adj_[a][i] == b) return 1;
    return 0;
}
static void addE(int a, int b) {
    adj_[a][deg_[a]++] = b;
    adj_[b][deg_[b]++] = a;
}
static void delOne(int a, int b) {
    for (int i = 0; i < deg_[a]; i++)
        if (adj_[a][i] == b) { adj_[a][i] = adj_[a][--deg_[a]]; return; }
}
static void delE(int a, int b) { delOne(a, b); delOne(b, a); }

/* Random vertex of side s with positive degree, or -1. */
static int pick_nonzero(int s) {
    if (cntS[s] == 0) return -1;
    for (int t = 0; t < 40; t++) {
        int v = lst[s][rndi(cntS[s])];
        if (deg_[v] > 0) return v;
    }
    return -1;
}

typedef struct { int kind, a1, b1, a2, b2; } Mv;

static void applyMv(const Mv *m) {
    switch (m->kind) {
    case 0: delE(m->a1, m->b1); delE(m->a2, m->b2); addE(m->a1, m->b2); addE(m->a2, m->b1); break;
    case 1: addE(m->a1, m->b1); break;
    case 2: delE(m->a1, m->b1); addE(m->a2, m->b1); break;
    default: delE(m->a1, m->b1); addE(m->a1, m->b2); break;
    }
}

static void undoMv(const Mv *m) {
    switch (m->kind) {
    case 0: delE(m->a1, m->b2); delE(m->a2, m->b1); addE(m->a1, m->b1); addE(m->a2, m->b2); break;
    case 1: delE(m->a1, m->b1); break;
    case 2: delE(m->a2, m->b1); addE(m->a1, m->b1); break;
    default: delE(m->a1, m->b2); addE(m->a1, m->b1); break;
    }
}

/* Degree-preserving 2-opt, degree-moving shifts into deficient vertices, or a fill edge. */
static int propose(Mv *m) {
    static int defA[MAXN], defB[MAXN];
    int nA = 0, nB = 0;
    for (int i = 0; i < cntS[0]; i++) { int v = lst[0][i]; if (deg_[v] < DEG) defA[nA++] = v; }
    for (int i = 0; i < cntS[1]; i++) { int v = lst[1][i]; if (deg_[v] < DEG) defB[nB++] = v; }

    if (nA && nB && rndu() < 0.5) {
        int a = defA[rndi(nA)], b = defB[rndi(nB)];
        if (!isadj(a, b)) { m->kind = 1; m->a1 = a; m->b1 = b; return 1; }
    }
    if ((nA || nB) && rndu() < 0.5) {
        if (nA && (!nB || rndu() < 0.5)) {
            int a2 = defA[rndi(nA)];
            int a1 = pick_nonzero(0);
            if (a1 < 0 || a1 == a2) return 0;
            int b1 = adj_[a1][rndi(deg_[a1])];
            if (isadj(a2, b1)) return 0;
            m->kind = 2; m->a1 = a1; m->b1 = b1; m->a2 = a2;
            return 1;
        } else {
            int b2 = defB[rndi(nB)];
            int b1 = pick_nonzero(1);
            if (b1 < 0 || b1 == b2) return 0;
            int a1 = adj_[b1][rndi(deg_[b1])];
            if (isadj(a1, b2)) return 0;
            m->kind = 3; m->a1 = a1; m->b1 = b1; m->b2 = b2;
            return 1;
        }
    }
    int a1 = pick_nonzero(0), a2 = pick_nonzero(0);
    if (a1 < 0 || a2 < 0 || a1 == a2) return 0;
    int b1 = adj_[a1][rndi(deg_[a1])];
    int b2 = adj_[a2][rndi(deg_[a2])];
    if (b1 == b2 || isadj(a1, b2) || isadj(a2, b1)) return 0;
    m->kind = 0; m->a1 = a1; m->b1 = b1; m->a2 = a2; m->b2 = b2;
    return 1;
}

static void add_pair(void) {
    int a = NV, b = NV + 1;
    side[a] = 0; side[b] = 1;
    deg_[a] = 0; deg_[b] = 0;
    lst[0][cntS[0]++] = a;
    lst[1][cntS[1]++] = b;
    NV += 2;
    W = (NV + 63) / 64;
}

static void save_best(void) {
    int m = 0;
    for (int i = 0; i < cntS[0]; i++) {
        int a = lst[0][i];
        for (int j = 0; j < deg_[a]; j++) {
            bestE[2 * m] = a;
            bestE[2 * m + 1] = adj_[a][j];
            m++;
        }
    }
    bestM = m;
    bestNv = NV;
}

static int read_graph(void) {
    int n, m;
    if (scanf("%d %d", &n, &m) != 2) return 0;
    if (n <= 0 || n > MAXN - 2 || m < 0) return 0;
    NV = n;
    for (int v = 0; v < n; v++) deg_[v] = 0;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return 0;
        if (u < 0 || u >= n || v < 0 || v >= n || u == v) return 0;
        if (deg_[u] >= DEG || deg_[v] >= DEG) return 0;
        if (isadj(u, v)) return 0;
        addE(u, v);
    }
    for (int v = 0; v < n; v++) side[v] = -1;
    for (int s = 0; s < n; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int qh = 0, qt = 0;
        qbuf[qt++] = s;
        while (qh < qt) {
            int v = qbuf[qh++];
            for (int i = 0; i < deg_[v]; i++) {
                int u = adj_[v][i];
                if (side[u] < 0) { side[u] = 1 - side[v]; qbuf[qt++] = u; }
                else if (side[u] == side[v]) return 0;
            }
        }
    }
    cntS[0] = cntS[1] = 0;
    for (int v = 0; v < n; v++) lst[side[v]][cntS[side[v]]++] = v;
    W = (NV + 63) / 64;
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    DEG = atoi(argv[1]);
    DIA = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    if (DEG < 2 || DEG > MAXDEG || DIA < 1) { printf("0 0\n"); return 0; }
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (!read_graph()) { printf("0 0\n"); return 0; }

    double tend = now() + tl;
    cur_cost = evalcost();
    double T0 = 3.0, T1 = 0.1;
    int step = 0;
    long long iters = 0;

    while (1) {
        if (cur_cost == 0) {
            save_best();
            if (NV + 2 > MAXN) break;
            add_pair();
            cur_cost = evalcost();
            step = 0;
        }
        if ((iters & 127) == 0 && now() > tend) break;
        iters++;
        Mv mv;
        if (!propose(&mv)) continue;
        applyMv(&mv);
        long long nc = evalcost();
        double T = T0 * pow(T1 / T0, (double)step / PHASE);
        if (nc <= cur_cost || rndu() < exp(-(double)(nc - cur_cost) / T)) {
            cur_cost = nc;
        } else {
            undoMv(&mv);
        }
        step++;
        if (step >= PHASE) step = 0;
    }

    if (bestM == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", bestNv, bestM);
    for (int i = 0; i < bestM; i++) printf("%d %d\n", bestE[2 * i], bestE[2 * i + 1]);
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

    total = max(0.5, min(0.8 * time_limit, time_limit - 10.0))
    b1 = 0.4 * total

    # Stage 1: group-lift search (known to reach the record for d=6, D=5).
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(b1, 2), best_n + 1],
                        timeout=b1 + 6.0)
        n, e = lib.parse_graph_text(out)
        if n > 0:
            consider(n, e)
    except Exception:
        pass

    # Stage 2: unstructured repair. Start from the best graph so far, add vertex
    # pairs, and anneal over edge swaps to minimise pairs at distance > D.
    b2 = max(0.5, total - b1 - 1.0)
    try:
        out = lib.run_c(C_REPAIR, [d, D, seed, round(b2, 2)],
                        stdin_graph=best, timeout=b2 + 6.0)
        n, e = lib.parse_graph_text(out)
        if n > 0:
            consider(n, e)
    except Exception:
        pass

    _ = time.monotonic() - start
    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
