import time

import lib


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


C_REPAIR = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;
#define MAXN 2400
#define MAXW 38
#define MAXDEG 16

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

static int d_, D_, N_, W_;
static int col[MAXN], deg[MAXN], nb[MAXN][MAXDEG];
static int listA[MAXN], nA_, listB[MAXN], nB_;
static u64 BUF1[MAXN * MAXW], BUF2[MAXN * MAXW];
static int bestN = 0, bestM = 0;
static int bestE[2 * MAXN * MAXDEG];

static int adjq(int u, int v) {
    for (int k = 0; k < deg[u]; k++) if (nb[u][k] == v) return 1;
    return 0;
}
static void addE(int u, int v) { nb[u][deg[u]++] = v; nb[v][deg[v]++] = u; }
static void remAt(int u, int v) {
    for (int k = 0; k < deg[u]; k++)
        if (nb[u][k] == v) { nb[u][k] = nb[u][--deg[u]]; return; }
}
static void remE(int u, int v) { remAt(u, v); remAt(v, u); }

/* Ordered unreached pairs within distance D (0 = valid graph). */
static long long evalbad(void) {
    int N = N_, W = W_;
    u64 *cur = BUF1, *nxt = BUF2;
    memset(cur, 0, sizeof(u64) * (size_t)N * W);
    for (int v = 0; v < N; v++) cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int t = 0; t < D_; t++) {
        for (int v = 0; v < N; v++) {
            u64 *o = nxt + (size_t)v * W;
            const u64 *c = cur + (size_t)v * W;
            for (int w = 0; w < W; w++) o[w] = c[w];
            for (int k = 0; k < deg[v]; k++) {
                const u64 *c2 = cur + (size_t)nb[v][k] * W;
                for (int w = 0; w < W; w++) o[w] |= c2[w];
            }
        }
        u64 *sw = cur; cur = nxt; nxt = sw;
    }
    long long cnt = 0;
    for (size_t i = 0; i < (size_t)N * W; i++) cnt += popc(cur[i]);
    return (long long)N * N - cnt;
}

static int pick(const int *L, int cnt, int want_def) {
    for (int t = 0; t < 60; t++) {
        int v = L[rndi(cnt)];
        if (want_def ? (deg[v] < d_) : (deg[v] > 0)) return v;
    }
    return -1;
}

/* Undo log for one proposed move. */
static int opT[8], opU[8], opV[8], nop;
static void doAdd(int u, int v) { addE(u, v); opT[nop] = 0; opU[nop] = u; opV[nop] = v; nop++; }
static void doRem(int u, int v) { remE(u, v); opT[nop] = 1; opU[nop] = u; opV[nop] = v; nop++; }
static void undoAll(void) {
    while (nop > 0) {
        nop--;
        if (opT[nop] == 0) remE(opU[nop], opV[nop]);
        else addE(opU[nop], opV[nop]);
    }
}

/* Propose a degree-respecting move; applies it only when it returns 1. */
static int proposeMove(void) {
    nop = 0;
    double r = rndu();
    if (r < 0.2) {
        int a = pick(listA, nA_, 1), b = pick(listB, nB_, 1);
        if (a < 0 || b < 0 || adjq(a, b)) return 0;
        doAdd(a, b);
        return 1;
    }
    if (r < 0.6) {
        if (rndu() < 0.5) {
            int a = pick(listA, nA_, 0);
            if (a < 0) return 0;
            int b = nb[a][rndi(deg[a])];
            int a2 = pick(listA, nA_, 1);
            if (a2 < 0 || a2 == a || adjq(a2, b)) return 0;
            doRem(a, b);
            doAdd(a2, b);
            return 1;
        } else {
            int b = pick(listB, nB_, 0);
            if (b < 0) return 0;
            int a = nb[b][rndi(deg[b])];
            int b2 = pick(listB, nB_, 1);
            if (b2 < 0 || b2 == b || adjq(a, b2)) return 0;
            doRem(a, b);
            doAdd(a, b2);
            return 1;
        }
    }
    int a1 = pick(listA, nA_, 0), a2 = pick(listA, nA_, 0);
    if (a1 < 0 || a2 < 0 || a1 == a2) return 0;
    int b1 = nb[a1][rndi(deg[a1])], b2 = nb[a2][rndi(deg[a2])];
    if (b1 == b2 || adjq(a1, b2) || adjq(a2, b1)) return 0;
    doRem(a1, b1);
    doRem(a2, b2);
    doAdd(a1, b2);
    doAdd(a2, b1);
    return 1;
}

static void saveBest(void) {
    int m = 0;
    for (int v = 0; v < N_; v++)
        for (int k = 0; k < deg[v]; k++)
            if (nb[v][k] > v) {
                bestE[2 * m] = v;
                bestE[2 * m + 1] = nb[v][k];
                m++;
            }
    bestN = N_;
    bestM = m;
}

/* Add one A-vertex and one B-vertex with degree 0. */
static int grow(void) {
    if (N_ + 2 > MAXN) return 0;
    int a = N_, b = N_ + 1;
    col[a] = 0; col[b] = 1;
    deg[a] = 0; deg[b] = 0;
    listA[nA_++] = a;
    listB[nB_++] = b;
    N_ += 2;
    W_ = (N_ + 63) / 64;
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    if (d_ < 1 || d_ > MAXDEG || D_ < 1) { printf("0 0\n"); return 0; }
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    double tEnd = now() + tl;

    int n, m;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN - 2) { printf("0 0\n"); return 0; }
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { printf("0 0\n"); return 0; }
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) { printf("0 0\n"); return 0; }
        if (deg[u] >= d_ || deg[v] >= d_ || adjq(u, v)) { printf("0 0\n"); return 0; }
        addE(u, v);
    }

    /* Bipartition by BFS; reject non-bipartite input. */
    for (int v = 0; v < n; v++) col[v] = -1;
    static int q[MAXN];
    for (int s = 0; s < n; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int h = 0, t = 0;
        q[t++] = s;
        while (h < t) {
            int u = q[h++];
            for (int k = 0; k < deg[u]; k++) {
                int w = nb[u][k];
                if (col[w] < 0) { col[w] = 1 - col[u]; q[t++] = w; }
                else if (col[w] == col[u]) { printf("0 0\n"); return 0; }
            }
        }
    }
    N_ = n;
    nA_ = nB_ = 0;
    for (int v = 0; v < n; v++) {
        if (col[v] == 0) listA[nA_++] = v;
        else listB[nB_++] = v;
    }
    W_ = (N_ + 63) / 64;

    long long cost = evalbad();
    long long since = 0;
    double T0 = 3.0;
    while (now() < tEnd) {
        if (cost == 0) {
            saveBest();
            if (!grow()) break;
            cost = evalbad();
            since = 0;
            T0 = 3.0;
            continue;
        }
        since++;
        if (!proposeMove()) continue;
        long long c2 = evalbad();
        long long delta = c2 - cost;
        double T = T0 * exp(-(double)(since % 100000) / 3000.0) + 0.05;
        if (delta <= 0 || rndu() < exp(-(double)delta / T)) cost = c2;
        else undoAll();
    }
    if (cost == 0) saveBest();

    if (bestN == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", bestN, bestM);
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

    avail = max(0.5, time_limit - 7.0)

    # Phase 1: voltage-lift search (the strong known engine).
    lift_budget = round(avail * 0.55, 2)
    try:
        out = lib.run_c(C_LIFT, [d, D, seed, lift_budget, best_n + 1],
                        timeout=lift_budget + 4.0)
        n, e = lib.parse_graph_text(out)
        if n > 0:
            consider(n, e)
    except Exception:
        pass

    # Phase 2: bold change. Start from the best graph found so far and run
    # annealing over edge moves that adds vertex pairs while keeping diameter D.
    rep_budget = round(max(0.5, avail - lift_budget - 1.0), 2)
    try:
        out = lib.run_c(C_REPAIR, [d, D, seed, rep_budget], stdin_graph=best,
                        timeout=rep_budget + 4.0)
        n, e = lib.parse_graph_text(out)
        if n > 0:
            consider(n, e)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
