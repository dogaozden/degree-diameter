import time

import lib


# Stage A: the group-lift search from the parent program (produces a valid start graph).
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


# Stage B: edge-level annealing on arbitrary (non-lifted) bipartite graphs.
# Starts from a valid graph, adds one vertex per side, and repeatedly searches
# for a valid graph with more vertices. Cost = number of vertex pairs at distance > D.
C_SA = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

#define MAXD 16
#define MAXN 1400
#define MAXW ((MAXN + 63) / 64)

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
static int deg[MAXN], col[MAXN];
static int nb[MAXN][MAXD];
static unsigned char adj[MAXN][MAXN];
static u64 bufA[MAXN * MAXW], bufB[MAXN * MAXW];
static int cand[MAXN], dcand[MAXN], acand[MAXN];
static int bestE[MAXN * MAXD][2];
static int bestN = 0, bestM = 0;

typedef struct {
    int nr, na;
    int ra[2], rb[2], aa[2], ab[2];
} Move;

/* Number of ordered-pair-unreached / 2 for radius D_. */
static long long evalcost(void) {
    int N = N_, W = (N + 63) / 64;
    u64 *cur = bufA, *nxt = bufB;
    memset(cur, 0, sizeof(u64) * (size_t)N * W);
    for (int v = 0; v < N; v++) cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int t = 0; t < D_; t++) {
        for (int v = 0; v < N; v++) {
            u64 *dst = nxt + (size_t)v * W;
            const u64 *src = cur + (size_t)v * W;
            for (int w = 0; w < W; w++) dst[w] = src[w];
            for (int j = 0; j < deg[v]; j++) {
                const u64 *s2 = cur + (size_t)nb[v][j] * W;
                for (int w = 0; w < W; w++) dst[w] |= s2[w];
            }
        }
        u64 *tmp = cur; cur = nxt; nxt = tmp;
    }
    long long cnt = 0;
    for (size_t i = 0; i < (size_t)N * W; i++) cnt += popc(cur[i]);
    return ((long long)N * N - cnt) / 2;
}

static void delfrom(int a, int b) {
    for (int j = 0; j < deg[a]; j++)
        if (nb[a][j] == b) { nb[a][j] = nb[a][deg[a] - 1]; deg[a]--; return; }
}
static void addE(int a, int b) {
    adj[a][b] = adj[b][a] = 1;
    nb[a][deg[a]++] = b;
    nb[b][deg[b]++] = a;
}
static void remE(int a, int b) {
    adj[a][b] = adj[b][a] = 0;
    delfrom(a, b);
    delfrom(b, a);
}

static void applyMove(const Move *m) {
    for (int i = 0; i < m->nr; i++) remE(m->ra[i], m->rb[i]);
    for (int i = 0; i < m->na; i++) addE(m->aa[i], m->ab[i]);
}
static void undoMove(const Move *m) {
    for (int i = 0; i < m->na; i++) remE(m->aa[i], m->ab[i]);
    for (int i = 0; i < m->nr; i++) addE(m->ra[i], m->rb[i]);
}

/* Random vertex with side (or any if side < 0) and deg>0 (needdef=0) or deg<d (needdef=1). */
static int pick_vertex(int side, int needdef) {
    int nc = 0;
    for (int v = 0; v < N_; v++) {
        if (side >= 0 && col[v] != side) continue;
        if (needdef ? (deg[v] < d_) : (deg[v] > 0)) cand[nc++] = v;
    }
    return nc ? cand[rndi(nc)] : -1;
}

/* 2-switch on bipartite edges: (a1,b1),(a2,b2) -> (a1,b2),(a2,b1). Degrees preserved. */
static int gen_switch(Move *m) {
    int a1 = pick_vertex(0, 0), a2 = pick_vertex(0, 0);
    if (a1 < 0 || a2 < 0 || a1 == a2) return 0;
    int b1 = nb[a1][rndi(deg[a1])], b2 = nb[a2][rndi(deg[a2])];
    if (b1 == b2 || adj[a1][b2] || adj[a2][b1]) return 0;
    m->nr = 2;
    m->ra[0] = a1; m->rb[0] = b1;
    m->ra[1] = a2; m->rb[1] = b2;
    m->na = 2;
    m->aa[0] = a1; m->ab[0] = b2;
    m->aa[1] = a2; m->ab[1] = b1;
    return 1;
}

/* Move edge endpoint (a,b) -> (a,x) where x is a deficient vertex on b's side. */
static int gen_rewire(Move *m) {
    int a = pick_vertex(-1, 0);
    if (a < 0) return 0;
    int b = nb[a][rndi(deg[a])];
    int nc = 0, bc = col[b];
    for (int x = 0; x < N_; x++)
        if (col[x] == bc && x != b && deg[x] < d_ && !adj[a][x]) cand[nc++] = x;
    if (!nc) return 0;
    int x = cand[rndi(nc)];
    m->nr = 1; m->ra[0] = a; m->rb[0] = b;
    m->na = 1; m->aa[0] = a; m->ab[0] = x;
    return 1;
}

/* Attach a deficient vertex v to an opposite-side u; if u is full, drop one of u's edges. */
static int gen_attach(Move *m) {
    int v = pick_vertex(-1, 1);
    if (v < 0) return 0;
    int oc = 1 - col[v];
    int nd = 0, na_ = 0;
    for (int x = 0; x < N_; x++) {
        if (col[x] != oc || adj[v][x]) continue;
        if (deg[x] < d_) dcand[nd++] = x;
        else acand[na_++] = x;
    }
    int u;
    if (nd && (na_ == 0 || rndu() < 0.8)) u = dcand[rndi(nd)];
    else if (na_) u = acand[rndi(na_)];
    else return 0;
    m->na = 1; m->aa[0] = v; m->ab[0] = u;
    if (deg[u] < d_) { m->nr = 0; return 1; }
    int w = nb[u][rndi(deg[u])];
    m->nr = 1; m->ra[0] = u; m->rb[0] = w;
    return 1;
}

static int gen_move(Move *m) {
    double r = rndu();
    if (r < 0.3 && gen_attach(m)) return 1;
    if (r < 0.65) return gen_switch(m);
    return gen_rewire(m);
}

static void save_best(void) {
    int m = 0;
    for (int v = 0; v < N_; v++)
        for (int j = 0; j < deg[v]; j++) {
            int u = nb[v][j];
            if (v < u) { bestE[m][0] = v; bestE[m][1] = u; m++; }
        }
    bestN = N_;
    bestM = m;
}

/* Add one new vertex on each side (both isolated). */
static void grow(void) {
    int N = N_;
    col[N] = 0; deg[N] = 0;
    col[N + 1] = 1; deg[N + 1] = 0;
    N_ = N + 2;
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    if (d_ < 3 || d_ > MAXD || D_ < 2) { printf("0 0\n"); return 0; }
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    double tend = now() + tl;

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { printf("0 0\n"); return 0; }
    if (n0 < 2 || n0 > MAXN - 2 || m0 < 0) { printf("0 0\n"); return 0; }
    N_ = n0;
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { printf("0 0\n"); return 0; }
        if (u < 0 || v < 0 || u >= n0 || v >= n0 || u == v || adj[u][v]
            || deg[u] >= d_ || deg[v] >= d_) { printf("0 0\n"); return 0; }
        addE(u, v);
    }

    /* Bipartition by BFS; reject non-bipartite input. */
    for (int v = 0; v < N_; v++) col[v] = -1;
    static int q[MAXN];
    for (int s = 0; s < N_; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int h = 0, t = 0;
        q[t++] = s;
        while (h < t) {
            int x = q[h++];
            for (int j = 0; j < deg[x]; j++) {
                int y = nb[x][j];
                if (col[y] < 0) { col[y] = 1 - col[x]; q[t++] = y; }
                else if (col[y] == col[x]) { printf("0 0\n"); return 0; }
            }
        }
    }

    long long cost = evalcost();
    int it = 0;
    const int cyc = 20000;
    const double Tmax = 2.5, Tmin = 0.15;

    while (1) {
        if ((it & 31) == 0 && now() > tend) break;
        if (cost == 0) {
            save_best();
            if (N_ + 2 > MAXN) break;
            grow();
            cost = evalcost();
            continue;
        }
        double frac = (double)(it % cyc) / cyc;
        double T = Tmax * pow(Tmin / Tmax, frac);
        it++;
        Move mv;
        if (!gen_move(&mv)) continue;
        applyMove(&mv);
        long long c2 = evalcost();
        if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / T)) cost = c2;
        else undoMove(&mv);
    }

    if (bestN == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", bestN, bestM);
    for (int i = 0; i < bestM; i++) printf("%d %d\n", bestE[i][0], bestE[i][1]);
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
    deadline = t0 + min(0.85 * time_limit, time_limit - 8.0)

    def remaining():
        return deadline - time.monotonic()

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

    if d < 3 or D < 3 or remaining() < 3.0:
        return best

    # Stage A: lift search for a strong valid start graph.
    budget_a = max(1.0, 0.4 * remaining())
    try:
        out = lib.run_c(C_LIFT, [d, D, seed, round(budget_a, 2), best_n + 1],
                        timeout=budget_a + 6.0)
        n, e = lib.parse_graph_text(out)
        if n > 0:
            consider(n, e)
    except Exception:
        pass

    # Stage B: edge-level annealing that tries to add vertices to the start graph.
    budget_b = remaining() - 1.0
    if budget_b >= 2.0:
        try:
            out = lib.run_c(C_SA, [d, D, seed + 1, round(budget_b, 2)],
                            stdin_graph=best, timeout=budget_b + 8.0)
            n, e = lib.parse_graph_text(out)
            if n > 0:
                consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
