import time

import lib


# ---------------------------------------------------------------------------
# Phase 1: group-lift search (voltage lifts over Z_m x| Z_k2 with k blocks).
# Breakout local search: the cost is a weighted count of unreached
# (representative, block) pairs. When the search stalls, the weights of the
# pairs that are still unreached are raised, so the landscape changes instead
# of restarting from scratch.
# ---------------------------------------------------------------------------
C_GROUP = r'''
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
static int *bE = NULL;
static int bEc = 0, bestN = 0;
static long long last_true = 0;
static long long W[2 * MAXK][2 * MAXK];

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

/* Weighted cost = sum of weights over unreached (rep, vertex) pairs + 1000 per duplicate dart.
   Also sets last_true = unweighted unreached count + 1000 per duplicate dart (0 iff valid). */
static long long evalcost(void) {
    int N = N_, G = G_, k = K_, d = d_, B = 2 * k;
    for (int v = 0; v < N; v++) rch[v] = 0;
    for (int b = 0; b < B; b++) rch[(size_t)b * G] = 1ULL << b;
    for (int t = 0; t < D_; t++) {
        for (int v = 0; v < N; v++) {
            u64 x = rch[v];
            for (int l = 0; l < d; l++) x |= rch[nb[l * N + v]];
            tmpr[v] = x;
        }
        u64 *sw = rch; rch = tmpr; tmpr = sw;
    }
    long long unr = 0, wsum = 0;
    for (int v = 0; v < N; v++) {
        u64 x = rch[v];
        int c = v / G;
        for (int b = 0; b < B; b++)
            if (!((x >> b) & 1ULL)) { unr++; wsum += W[b][c]; }
    }
    long long dup = 0;
    for (int i = 0; i < k; i++)
        for (int l = 0; l < d; l++)
            for (int l2 = l + 1; l2 < d; l2++)
                if (lay[l][i] == lay[l2][i] && VS[l][i] == VS[l2][i]) dup++;
    last_true = unr + 1000 * dup;
    return wsum + 1000 * dup;
}

/* Breakout step: raise the weight of every (representative, block) pair that is
   still unreached in the current state. */
static void bump_weights(void) {
    int N = N_, G = G_, B = 2 * K_;
    int flag[2 * MAXK][2 * MAXK];
    memset(flag, 0, sizeof flag);
    evalcost();
    for (int v = 0; v < N; v++) {
        u64 x = rch[v];
        int c = v / G;
        for (int b = 0; b < B; b++)
            if (!((x >> b) & 1ULL)) flag[b][c] = 1;
    }
    for (int b = 0; b < B; b++)
        for (int c = 0; c < B; c++)
            if (flag[b][c]) W[b][c]++;
}

/* Breakout local search. Returns 1 when the current state is a valid graph. */
static int search(double tend, int iters, int patience) {
    int k = K_, d = d_, G = G_, N = N_, B = 2 * k;
    u64 full = (1ULL << B) - 1;
    for (int b = 0; b < B; b++)
        for (int c = 0; c < B; c++) W[b][c] = 1;
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
    long long tcur = last_true;
    double c0 = (double)(cost > 0 ? cost : 1);
    long long bestc = cost;
    int last = 0;

    for (int t = 0; t < iters && tcur != 0; t++) {
        if ((t & 63) == 0 && now() > tend) break;
        if (t - last > patience) {
            bump_weights();
            cost = evalcost();
            tcur = last_true;
            bestc = cost;
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
            long long tc2 = last_true;
            if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                tcur = tc2;
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
            long long tc2 = last_true;
            if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                tcur = tc2;
            } else {
                VS[l][i] = old;
                apply_dart(l, i);
            }
        }
        if (cost < bestc) { bestc = cost; last = t; }
    }
    return tcur == 0;
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
        int ok = search(tend, 60000, 1500);
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


# ---------------------------------------------------------------------------
# Phase 2: simulated annealing on general bipartite graphs.
# Starts from a valid graph, adds vertex pairs and fills degrees with
# compound "sew" moves, then anneals with degree-preserving 2-switches
# using the number of unreached pairs (distance > D) as the cost.
# ---------------------------------------------------------------------------
C_SA = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

#define MAXN 2400
#define MAXW 38
#define MAXDEG 8
#define MAXE (MAXN * MAXDEG / 2)

static u64 rs = 1234567ULL;
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

static int d_, D_, N_, nA_, ne_;
static int deg_[MAXN];
static int nb_[MAXN][MAXDEG];
static unsigned char adj_[MAXN][MAXN];
static int side_[MAXN];
static int ea_[MAXE + 4], eb_[MAXE + 4];      /* edge e joins A-vertex ea_ and B-vertex eb_ */
static u64 RA[MAXN][MAXW], RB[MAXN][MAXW];
static int bestN = 0, bestM = 0;
static int bestEa[MAXE + 4], bestEb[MAXE + 4];
static int listA[MAXN], listB[MAXN];

static void rep(int v, int oldv, int newv) {
    int dv = deg_[v];
    for (int j = 0; j < dv; j++)
        if (nb_[v][j] == oldv) { nb_[v][j] = newv; return; }
}

static void addedge(int a, int b) {
    nb_[a][deg_[a]++] = b;
    nb_[b][deg_[b]++] = a;
    adj_[a][b] = 1;
    adj_[b][a] = 1;
    ea_[ne_] = a;
    eb_[ne_] = b;
    ne_++;
}

/* Edges e1=(a1,b1), e2=(a2,b2) become (a1,b2), (a2,b1). Applying it twice restores. */
static void switch_e(int e1, int e2) {
    int a1 = ea_[e1], b1 = eb_[e1], a2 = ea_[e2], b2 = eb_[e2];
    rep(a1, b1, b2);
    rep(b1, a1, a2);
    rep(a2, b2, b1);
    rep(b2, a2, a1);
    adj_[a1][b1] = 0; adj_[b1][a1] = 0;
    adj_[a2][b2] = 0; adj_[b2][a2] = 0;
    adj_[a1][b2] = 1; adj_[b2][a1] = 1;
    adj_[a2][b1] = 1; adj_[b1][a2] = 1;
    eb_[e1] = b2;
    eb_[e2] = b1;
}

/* Cost = number of unordered vertex pairs at distance > D_. */
static long long evalcost(void) {
    int N = N_, W = (N + 63) >> 6;
    u64 (*R)[MAXW] = RA;
    u64 (*T)[MAXW] = RB;
    for (int v = 0; v < N; v++) {
        for (int w = 0; w < W; w++) R[v][w] = 0;
        R[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int t = 0; t < D_; t++) {
        for (int v = 0; v < N; v++) {
            for (int w = 0; w < W; w++) T[v][w] = R[v][w];
            int dv = deg_[v];
            for (int j = 0; j < dv; j++) {
                const u64 *src = R[nb_[v][j]];
                for (int w = 0; w < W; w++) T[v][w] |= src[w];
            }
        }
        u64 (*sw)[MAXW] = R;
        R = T;
        T = sw;
    }
    long long cnt = 0;
    for (int v = 0; v < N; v++)
        for (int w = 0; w < W; w++) cnt += popc(R[v][w]);
    return ((long long)N * N - cnt) / 2;
}

static void save_best(void) {
    bestN = N_;
    bestM = ne_;
    memcpy(bestEa, ea_, sizeof(int) * (size_t)ne_);
    memcpy(bestEb, eb_, sizeof(int) * (size_t)ne_);
}

/* Compound "sew" move: x (A, slack) and y (B, slack); replace edge (a1,b1)
   by (x,b1) and (a1,y), which raises the total edge count by one. */
static int grow_once(int x, int y) {
    if (ne_ + 2 >= MAXE) return 0;
    if (!adj_[x][y]) { addedge(x, y); return 1; }
    for (int t = 0; t < 200; t++) {
        int e = rndi(ne_);
        int a1 = ea_[e], b1 = eb_[e];
        if (adj_[x][b1] || adj_[a1][y]) continue;
        rep(b1, a1, x);
        rep(a1, b1, y);
        adj_[a1][b1] = 0; adj_[b1][a1] = 0;
        adj_[x][b1] = 1; adj_[b1][x] = 1;
        adj_[a1][y] = 1; adj_[y][a1] = 1;
        nb_[x][deg_[x]++] = b1;
        nb_[y][deg_[y]++] = a1;
        ea_[e] = x;
        eb_[e] = b1;
        ea_[ne_] = a1;
        eb_[ne_] = y;
        ne_++;
        return 1;
    }
    return 0;
}

static void fill(void) {
    int fails = 0;
    while (fails < 3000) {
        int na = 0, nbb = 0;
        for (int v = 0; v < N_; v++) {
            if (deg_[v] < d_) {
                if (side_[v] == 0) listA[na++] = v;
                else listB[nbb++] = v;
            }
        }
        if (na == 0 || nbb == 0) break;
        int x = listA[rndi(na)];
        int y = listB[rndi(nbb)];
        if (!grow_once(x, y)) fails++;
    }
}

static void add_pair(void) {
    int x = N_, y = N_ + 1;
    side_[x] = 0;
    side_[y] = 1;
    deg_[x] = 0;
    deg_[y] = 0;
    N_ += 2;
}

int main(int argc, char **argv) {
    if (argc < 6) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    nA_ = atoi(argv[5]);
    if (d_ < 3 || d_ > MAXDEG || D_ < 3) { printf("0 0\n"); return 0; }
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    int n, m;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN - 4 || m < 0 || m > MAXE) {
        printf("0 0\n");
        return 0;
    }
    N_ = n;
    ne_ = 0;
    for (int v = 0; v < n; v++) {
        side_[v] = (v < nA_) ? 0 : 1;
        deg_[v] = 0;
    }
    int bad = 0;
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { bad = 1; break; }
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) { bad = 1; continue; }
        if (side_[u] == side_[v]) { bad = 1; continue; }
        int a = (side_[u] == 0) ? u : v;
        int b = (side_[u] == 0) ? v : u;
        if (deg_[a] >= d_ || deg_[b] >= d_ || adj_[a][b]) { bad = 1; continue; }
        addedge(a, b);
    }
    if (bad || ne_ == 0) { printf("0 0\n"); return 0; }

    double tend = now() + tl;
    long long cost = evalcost();
    if (cost == 0) save_best();
    fill();
    cost = evalcost();
    if (cost == 0) save_best();

    long long it = 0, stage = 0;
    const long long PER = 20000;
    for (;;) {
        it++;
        if ((it & 127) == 0 && now() > tend) break;
        if (cost == 0) {
            save_best();
            if (N_ + 2 > MAXN - 4) break;
            add_pair();
            fill();
            cost = evalcost();
            stage = 0;
            continue;
        }
        stage++;
        double phase = (double)(stage % PER) / (double)PER;
        double T = 0.15 + 0.85 * (1.0 - phase);
        int e1 = rndi(ne_), e2 = rndi(ne_);
        if (e1 == e2) continue;
        int a1 = ea_[e1], b1 = eb_[e1], a2 = ea_[e2], b2 = eb_[e2];
        if (a1 == a2 || b1 == b2 || adj_[a1][b2] || adj_[a2][b1]) continue;
        switch_e(e1, e2);
        long long c2 = evalcost();
        long long dl = c2 - cost;
        if (dl <= 0 || rndu() < exp(-(double)dl / T)) {
            cost = c2;
        } else {
            switch_e(e1, e2);
        }
    }

    if (bestN == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", bestN, bestM);
    for (int e = 0; e < bestM; e++) printf("%d %d\n", bestEa[e], bestEb[e]);
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

    # Budget: the group-lift search (now with breakout weighting) gets the
    # larger share; annealing polishes its result with the remaining time.
    budget = max(0.5, min(0.9 * time_limit, time_limit - 6.0))
    g_budget = 0.75 * budget

    # Phase 1: group-lift search gives a valid start graph.
    try:
        out = lib.run_c(C_GROUP, [d, D, seed, round(g_budget, 2), best_n + 1],
                        timeout=g_budget + 6.0)
        n, e = lib.parse_graph_text(out)
        if n > 0:
            consider(n, e)
    except Exception:
        pass

    # Phase 2: annealing growth from the best valid graph so far.
    # All starts have A = first half of the vertices (PG incidence, K_{d,d}, group lifts).
    remaining = budget - (time.monotonic() - start)
    sa_budget = min(remaining - 1.0, budget - g_budget)
    if sa_budget >= 1.0:
        try:
            out = lib.run_c(C_SA, [d, D, seed, round(sa_budget, 2), best_n // 2],
                            stdin_graph=best, timeout=sa_budget + 6.0)
            n, e = lib.parse_graph_text(out)
            if n > 0:
                consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
