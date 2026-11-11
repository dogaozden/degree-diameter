import time

import lib


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

static int search(double tend, int iters, int patience, int maxkick) {
    int k = K_, d = d_, G = G_;
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
                int start = rndi(N_), v = -1;
                for (int q = 0; q < N_; q++) {
                    int w = (start + q) % N_;
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

/* Unstructured annealing over bipartite graphs with degree <= d and diameter <= D.
   Moves: degree-preserving double-edge swaps, cost = unordered pairs at distance > D.
   Growth: when valid, remove d edges with distinct endpoints and attach two new vertices
   (A-side and B-side) to their freed ends, keeping all degrees. Reads a start graph on stdin. */

typedef uint64_t u64;
#define MAXN 2048
#define WCAP 32
#define MAXDEG 16
#define STAGE 20000

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
static int adj[MAXN][MAXDEG];
static int deg[MAXN];
static int col[MAXN];
static u64 RA[MAXN][WCAP], RB[MAXN][WCAP];
static int sadj[MAXN][MAXDEG], sdeg[MAXN], scol[MAXN], sN = 0;
static int have_snap = 0;

static void snapshot(void) {
    memcpy(sadj, adj, sizeof adj);
    memcpy(sdeg, deg, sizeof deg);
    memcpy(scol, col, sizeof col);
    sN = N_;
    have_snap = 1;
}

static void restore_snapshot(void) {
    memcpy(adj, sadj, sizeof adj);
    memcpy(deg, sdeg, sizeof deg);
    memcpy(col, scol, sizeof col);
    N_ = sN;
}

static int has_edge(int x, int y) {
    for (int j = 0; j < deg[x]; j++) if (adj[x][j] == y) return 1;
    return 0;
}
static void replace_nb(int x, int old, int nw) {
    for (int j = 0; j < deg[x]; j++) if (adj[x][j] == old) { adj[x][j] = nw; return; }
}
static void add_nb(int x, int y) { adj[x][deg[x]++] = y; }
static void del_nb(int x, int y) {
    for (int j = 0; j < deg[x]; j++)
        if (adj[x][j] == y) { adj[x][j] = adj[x][deg[x] - 1]; deg[x]--; return; }
}
static void add_edge(int x, int y) { add_nb(x, y); add_nb(y, x); }
static void del_edge(int x, int y) { del_nb(x, y); del_nb(y, x); }

/* Unordered pairs at distance > D_. */
static long long badpairs(void) {
    int N = N_, W = (N + 63) >> 6;
    for (int v = 0; v < N; v++) {
        for (int w = 0; w < W; w++) RA[v][w] = 0;
        RA[v][v >> 6] |= 1ULL << (v & 63);
    }
    u64 (*P)[WCAP] = RA;
    u64 (*Q)[WCAP] = RB;
    for (int t = 0; t < D_; t++) {
        for (int v = 0; v < N; v++) {
            for (int w = 0; w < W; w++) Q[v][w] = P[v][w];
            for (int j = 0; j < deg[v]; j++) {
                int u = adj[v][j];
                for (int w = 0; w < W; w++) Q[v][w] |= P[u][w];
            }
        }
        u64 (*T)[WCAP] = P; P = Q; Q = T;
    }
    long long cnt = 0;
    for (int v = 0; v < N; v++)
        for (int w = 0; w < W; w++) cnt += popc(P[v][w]);
    long long tot = (long long)N * N;
    return (tot - cnt) / 2;
}

static int pick_side(int side) {
    for (int tries = 0; tries < 100000; tries++) {
        int v = rndi(N_);
        if (col[v] == side && deg[v] > 0) return v;
    }
    return -1;
}

/* Double-edge swap: a-b, c-e  ->  a-e, c-b  (a, c on side 0; b, e on side 1). */
static int try_swap(double T, long long *cost) {
    int a = pick_side(0), c = pick_side(0);
    if (a < 0 || c < 0 || a == c) return 0;
    int ia = rndi(deg[a]), ic = rndi(deg[c]);
    int b = adj[a][ia], e = adj[c][ic];
    if (b == e) return 0;
    if (has_edge(a, e) || has_edge(c, b)) return 0;
    adj[a][ia] = e;
    adj[c][ic] = b;
    replace_nb(b, a, c);
    replace_nb(e, c, a);
    long long nc = badpairs();
    if (nc <= *cost || rndu() < exp(-(double)(nc - *cost) / T)) {
        *cost = nc;
        return 1;
    }
    adj[a][ia] = b;
    adj[c][ic] = e;
    replace_nb(b, c, a);
    replace_nb(e, a, c);
    return 0;
}

/* Remove d edges with distinct endpoints; attach new A-vertex to their B-ends and new B-vertex to
   their A-ends. Degrees are preserved, bipartiteness is preserved. */
static int grow2(void) {
    int d = d_;
    int ea[MAXDEG], eb[MAXDEG], k = 0;
    for (int tries = 0; k < d && tries < 200000; tries++) {
        int a = rndi(N_);
        if (col[a] != 0 || deg[a] == 0) continue;
        int b = adj[a][rndi(deg[a])];
        int bad = 0;
        for (int i = 0; i < k; i++)
            if (ea[i] == a || eb[i] == b) { bad = 1; break; }
        if (bad) continue;
        ea[k] = a; eb[k] = b; k++;
    }
    if (k < d) return 0;
    if (N_ + 2 > MAXN) return 0;
    for (int i = 0; i < k; i++) del_edge(ea[i], eb[i]);
    int A = N_, B = N_ + 1;
    N_ += 2;
    col[A] = 0; col[B] = 1;
    deg[A] = 0; deg[B] = 0;
    for (int i = 0; i < k; i++) {
        add_edge(A, eb[i]);
        add_edge(B, ea[i]);
    }
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    if (d_ < 3 || d_ > MAXDEG || D_ < 3) { printf("0 0\n"); return 0; }
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) { printf("0 0\n"); return 0; }
    if (n <= 1 || n > MAXN - 2 || m < 0) { printf("0 0\n"); return 0; }
    int *eu = malloc(sizeof(int) * (size_t)(m + 1));
    int *ev = malloc(sizeof(int) * (size_t)(m + 1));
    N_ = n;
    for (int v = 0; v < n; v++) { deg[v] = 0; col[v] = -1; }
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { printf("0 0\n"); return 0; }
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) { printf("0 0\n"); return 0; }
        if (deg[u] >= d_ || deg[v] >= d_) { printf("0 0\n"); return 0; }
        if (has_edge(u, v)) { printf("0 0\n"); return 0; }
        eu[i] = u; ev[i] = v;
        add_edge(u, v);
    }
    /* 2-colour by BFS (input must be bipartite). */
    int *q = malloc(sizeof(int) * (size_t)n);
    for (int s = 0; s < n; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int qh = 0, qt = 0;
        q[qt++] = s;
        while (qh < qt) {
            int x = q[qh++];
            for (int j = 0; j < deg[x]; j++) {
                int y = adj[x][j];
                if (col[y] < 0) { col[y] = 1 - col[x]; q[qt++] = y; }
                else if (col[y] == col[x]) { printf("0 0\n"); return 0; }
            }
        }
    }
    free(q); free(eu); free(ev);

    double tend = now() + tl;
    long long cost = badpairs();
    if (cost == 0) snapshot();
    double T0 = 0.3;
    int stage_it = 0;

    while (now() < tend) {
        if (cost == 0) {
            snapshot();
            if (!grow2()) break;
            cost = badpairs();
            T0 = 0.3 + 0.05 * (double)cost;
            stage_it = 0;
            continue;
        }
        if (stage_it >= STAGE) {
            if (!have_snap) break;
            restore_snapshot();
            cost = 0;
            stage_it = 0;
            continue;
        }
        double T = T0 * (1.0 - (double)stage_it / STAGE);
        if (T < 0.05) T = 0.05;
        try_swap(T, &cost);
        stage_it++;
    }
    if (cost == 0) snapshot();

    if (!have_snap) { printf("0 0\n"); return 0; }
    int M = 0;
    for (int v = 0; v < sN; v++) if (scol[v] == 0) M += sdeg[v];
    printf("%d %d\n", sN, M);
    for (int v = 0; v < sN; v++) {
        if (scol[v] != 0) continue;
        for (int j = 0; j < sdeg[v]; j++) printf("%d %d\n", v, sadj[v][j]);
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

    # Phase 1: structured group-lift search (proven source of valid graphs).
    # Phase 2: unstructured annealing that grows the best valid graph by two vertices at a time.
    # Reserve time for compiling the two C programs and Python glue.
    avail = max(2.0, time_limit - 6.0)
    b1 = round(0.6 * avail, 2)
    try:
        out = lib.run_c(C_GROUP, [d, D, seed, b1, best_n + 1], timeout=b1 + 3.0)
        n, e = lib.parse_graph_text(out)
        if n > 0:
            consider(n, e)
    except Exception:
        pass

    b2 = max(1.0, avail - b1)
    try:
        out = lib.run_c(C_GROW, [d, D, seed, b2], stdin_graph=best, timeout=b2 + 3.0)
        n, e = lib.parse_graph_text(out)
        if n > 0:
            consider(n, e)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
