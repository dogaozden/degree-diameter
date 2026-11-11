import time

import lib


# Parent search engine (group-lift simulated annealing), used for the first phase.
C_SEARCH = r'''
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


# Growth engine: start from a valid bipartite graph, add two vertices (one per side),
# then repair with simulated annealing on the number of pairs at distance > D.
# Moves: add an edge between deficient vertices, move an edge onto a deficient
# A-vertex, or switch two edges. Degrees never exceed d. On failure, roll back
# to the best valid graph and retry.
C_GROW = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

#define CAP 2600
#define WMAX 41
#define MAXD 16
#define ITERS 8000

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

static int d_, D_, N_;
static int side_[CAP];
static int deg_[CAP];
static int adj_[CAP * MAXD];
static unsigned char am_[CAP * CAP];
static u64 RA[CAP * WMAX], RB[CAP * WMAX];
static int defA[CAP], defB[CAP], stk[CAP];
static int bestN = 0, bestE_cnt = 0;
static int bestE[2 * CAP * MAXD];

static void add_edge(int a, int b) {
    am_[a * CAP + b] = 1; am_[b * CAP + a] = 1;
    adj_[a * MAXD + deg_[a]++] = b;
    adj_[b * MAXD + deg_[b]++] = a;
}

static void rm_from(int a, int b) {
    int *L = adj_ + a * MAXD;
    for (int i = 0; i < deg_[a]; i++)
        if (L[i] == b) { L[i] = L[deg_[a] - 1]; deg_[a]--; return; }
}

static void del_edge(int a, int b) {
    am_[a * CAP + b] = 0; am_[b * CAP + a] = 0;
    rm_from(a, b); rm_from(b, a);
}

/* Number of ordered (v, w) pairs with dist(v, w) > D_. Zero iff valid (given degrees and bipartiteness). */
static long long cost_now(void) {
    int N = N_;
    int WW = (N + 63) / 64;
    u64 *cur = RA, *nxt = RB;
    for (int v = 0; v < N; v++) {
        u64 *r = cur + (size_t)v * WMAX;
        for (int w = 0; w < WW; w++) r[w] = 0;
        r[v >> 6] |= 1ULL << (v & 63);
    }
    for (int t = 0; t < D_; t++) {
        for (int v = 0; v < N; v++) {
            u64 *dst = nxt + (size_t)v * WMAX;
            const u64 *src = cur + (size_t)v * WMAX;
            for (int w = 0; w < WW; w++) dst[w] = src[w];
            int dg = deg_[v];
            const int *L = adj_ + v * MAXD;
            for (int i = 0; i < dg; i++) {
                const u64 *s2 = cur + (size_t)L[i] * WMAX;
                for (int w = 0; w < WW; w++) dst[w] |= s2[w];
            }
        }
        u64 *tmp = cur; cur = nxt; nxt = tmp;
    }
    long long cnt = 0;
    for (int v = 0; v < N; v++) {
        const u64 *r = cur + (size_t)v * WMAX;
        for (int w = 0; w < WW; w++) cnt += popc(r[w]);
    }
    return (long long)N * N - cnt;
}

/* Random vertex on side s with at least one edge; -1 on failure. */
static int pick_side_vertex(int s) {
    for (int tries = 0; tries < 200; tries++) {
        int v = rndi(N_);
        if (side_[v] == s && deg_[v] > 0) return v;
    }
    return -1;
}

/* Annealing on the current state. Returns 1 if the state is valid at the end. */
static int anneal(double tend, int iters, double T0) {
    long long cur = cost_now();
    for (int t = 0; t < iters && cur > 0; t++) {
        if ((t & 31) == 0 && now() > tend) break;
        double T = T0 * (1.0 - (double)t / iters);
        if (T < 0.1) T = 0.1;

        int nA = 0, nB = 0;
        for (int v = 0; v < N_; v++) {
            if (deg_[v] < d_) {
                if (side_[v] == 0) defA[nA++] = v;
                else defB[nB++] = v;
            }
        }

        double r = rndu();
        int kind = 3;
        if (r < 0.2 && nA > 0 && nB > 0) kind = 1;
        else if (r < 0.6 && nA > 0) kind = 2;

        if (kind == 1) {
            /* Add an edge between a deficient A-vertex and a deficient B-vertex. Never raises cost. */
            int x = -1, y = -1;
            for (int tr = 0; tr < 30; tr++) {
                int xx = defA[rndi(nA)], yy = defB[rndi(nB)];
                if (!am_[xx * CAP + yy]) { x = xx; y = yy; break; }
            }
            if (x >= 0) {
                add_edge(x, y);
                cur = cost_now();
                continue;
            }
            kind = (nA > 0) ? 2 : 3;
        }

        if (kind == 2) {
            /* Move an edge (a, b) to (x, b), where x is a deficient A-vertex. */
            int x = defA[rndi(nA)];
            int a = pick_side_vertex(0);
            if (a < 0 || a == x) continue;
            int b = adj_[a * MAXD + rndi(deg_[a])];
            if (am_[x * CAP + b]) continue;
            del_edge(a, b);
            add_edge(x, b);
            long long c = cost_now();
            if (c <= cur || rndu() < exp(-(double)(c - cur) / T)) {
                cur = c;
            } else {
                del_edge(x, b);
                add_edge(a, b);
            }
        } else {
            /* Switch: (a, b), (a2, b2) -> (a, b2), (a2, b). Degrees preserved. */
            int a = pick_side_vertex(0);
            int a2 = pick_side_vertex(0);
            if (a < 0 || a2 < 0 || a == a2) continue;
            int b = adj_[a * MAXD + rndi(deg_[a])];
            int b2 = adj_[a2 * MAXD + rndi(deg_[a2])];
            if (b == b2 || am_[a * CAP + b2] || am_[a2 * CAP + b]) continue;
            del_edge(a, b);
            del_edge(a2, b2);
            add_edge(a, b2);
            add_edge(a2, b);
            long long c = cost_now();
            if (c <= cur || rndu() < exp(-(double)(c - cur) / T)) {
                cur = c;
            } else {
                del_edge(a, b2);
                del_edge(a2, b);
                add_edge(a, b);
                add_edge(a2, b2);
            }
        }
    }
    return cur == 0;
}

static void save_best(void) {
    int c = 0;
    for (int v = 0; v < N_; v++)
        for (int i = 0; i < deg_[v]; i++) {
            int u = adj_[v * MAXD + i];
            if (u > v) {
                bestE[2 * c] = v;
                bestE[2 * c + 1] = u;
                c++;
            }
        }
    bestE_cnt = c;
    bestN = N_;
}

static void rebuild_from_best(void) {
    for (int v = 0; v < N_; v++) {
        for (int i = 0; i < deg_[v]; i++) am_[v * CAP + adj_[v * MAXD + i]] = 0;
        deg_[v] = 0;
    }
    N_ = bestN;
    for (int i = 0; i < bestE_cnt; i++) add_edge(bestE[2 * i], bestE[2 * i + 1]);
}

static int read_graph(void) {
    int n, m;
    if (scanf("%d %d", &n, &m) != 2) return 0;
    if (n <= 0 || n > CAP - 64 || m < 0) return 0;
    N_ = n;
    for (int v = 0; v < n; v++) { deg_[v] = 0; side_[v] = -1; }
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return 0;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) return 0;
        if (am_[u * CAP + v]) continue;
        if (deg_[u] >= d_ || deg_[v] >= d_) return 0;
        add_edge(u, v);
    }
    /* 2-colour: fails if the graph is not bipartite. */
    for (int s = 0; s < n; s++) {
        if (side_[s] >= 0) continue;
        side_[s] = 0;
        int sp = 0;
        stk[sp++] = s;
        while (sp) {
            int u = stk[--sp];
            for (int i = 0; i < deg_[u]; i++) {
                int v = adj_[u * MAXD + i];
                if (side_[v] < 0) {
                    side_[v] = 1 - side_[u];
                    stk[sp++] = v;
                } else if (side_[v] == side_[u]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    if (d_ < 3 || D_ < 3 || d_ > MAXD) { printf("0 0\n"); return 0; }
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    double tend = now() + tl;
    if (!read_graph()) { printf("0 0\n"); return 0; }
    if (cost_now() != 0) {
        if (!anneal(tend, 4 * ITERS, 3.0)) { printf("0 0\n"); return 0; }
    }
    save_best();

    while (now() < tend && N_ + 2 <= CAP - 2) {
        side_[N_] = 0; deg_[N_] = 0; N_++;
        side_[N_] = 1; deg_[N_] = 0; N_++;
        if (anneal(tend, ITERS, 3.0)) save_best();
        else rebuild_from_best();
    }

    printf("%d %d\n", bestN, bestE_cnt);
    for (int i = 0; i < bestE_cnt; i++) printf("%d %d\n", bestE[2 * i], bestE[2 * i + 1]);
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
    t_start = time.time()
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

    # Reserve a few seconds for compilation and Python glue.
    budget = max(1.0, time_limit - 6.0)

    # Phase 1: group-lift search for a large starting graph.
    search_budget = 0.5 * budget
    try:
        out = lib.run_c(C_SEARCH, [d, D, seed, round(search_budget, 2), best_n + 1],
                        timeout=search_budget + 3.0)
        n, e = lib.parse_graph_text(out)
        if n > 0:
            consider(n, e)
    except Exception:
        pass

    # Phase 2: grow the best valid graph by annealing vertex-pair insertions.
    remaining = budget - (time.time() - t_start)
    if remaining > 2.0:
        grow_budget = remaining - 1.0
        try:
            out = lib.run_c(C_GROW, [d, D, seed, round(grow_budget, 2)],
                            stdin_graph=best, timeout=grow_budget + 3.0)
            n, e = lib.parse_graph_text(out)
            if n > 0:
                consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
