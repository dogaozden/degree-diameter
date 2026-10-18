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

/* ===================== group-lift engine (mode 0) ===================== */

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

static int group_main(int argc, char **argv) {
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

/* ===================== edge-repair engine (mode 1) ===================== */
/* Input: bipartite graph with even ids on side A and odd ids on side B.
   Grows by inserting a vertex pair (rewiring d edges), then anneals with
   degree-preserving double edge swaps to minimise bad pairs (distance > D). */

#define RMAXN 2400
#define RMAXE (RMAXN * MAXD / 2)
#define RW ((RMAXN + 63) / 64)

static int rN = 0, rM = 0;
static int rdeg[RMAXN];
static int rnbr[RMAXN][MAXD];
static unsigned char rmat[(size_t)RMAXN * RMAXN];
static int rEa[RMAXE], rEb[RMAXE];
static int sEa[RMAXE], sEb[RMAXE], sM = 0, sN = 0;
static int tEa[RMAXE], tEb[RMAXE];
static u64 rRa[(size_t)RMAXN * RW], rRb[(size_t)RMAXN * RW];

static int radj(int a, int b) { return rmat[(size_t)a * RMAXN + b]; }

static void radd(int a, int b) {
    rmat[(size_t)a * RMAXN + b] = 1;
    rmat[(size_t)b * RMAXN + a] = 1;
    rnbr[a][rdeg[a]++] = b;
    rnbr[b][rdeg[b]++] = a;
}

static void rdel_one(int a, int b) {
    for (int j = 0; j < rdeg[a]; j++)
        if (rnbr[a][j] == b) {
            rnbr[a][j] = rnbr[a][rdeg[a] - 1];
            rdeg[a]--;
            return;
        }
}

static void rdel(int a, int b) {
    rmat[(size_t)a * RMAXN + b] = 0;
    rmat[(size_t)b * RMAXN + a] = 0;
    rdel_one(a, b);
    rdel_one(b, a);
}

static void rebuild(int N, int M, const int *Ea, const int *Eb) {
    memset(rmat, 0, sizeof rmat);
    memset(rdeg, 0, sizeof rdeg);
    rN = N;
    rM = 0;
    for (int e = 0; e < M; e++) {
        rEa[e] = Ea[e];
        rEb[e] = Eb[e];
        radd(Ea[e], Eb[e]);
    }
    rM = M;
}

static long long rcost(void) {
    int N = rN, W = (N + 63) >> 6;
    u64 *cur = rRa, *nxt = rRb;
    for (int v = 0; v < N; v++) {
        for (int w = 0; w < W; w++) cur[(size_t)v * RW + w] = 0;
        cur[(size_t)v * RW + (v >> 6)] |= 1ULL << (v & 63);
    }
    for (int t = 0; t < D_; t++) {
        for (int v = 0; v < N; v++) {
            u64 *dst = nxt + (size_t)v * RW;
            const u64 *src = cur + (size_t)v * RW;
            for (int w = 0; w < W; w++) dst[w] = src[w];
            for (int j = 0; j < rdeg[v]; j++) {
                const u64 *s2 = cur + (size_t)rnbr[v][j] * RW;
                for (int w = 0; w < W; w++) dst[w] |= s2[w];
            }
        }
        u64 *sw = cur; cur = nxt; nxt = sw;
    }
    long long bad = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(cur[(size_t)v * RW + w]);
        bad += N - c;
    }
    return bad / 2;
}

static void rsnap(void) {
    sN = rN;
    sM = rM;
    memcpy(sEa, rEa, sizeof(int) * (size_t)rM);
    memcpy(sEb, rEb, sizeof(int) * (size_t)rM);
}

/* Add edges between random deficient A/B vertices (never increases cost). */
static int rfill(int tries) {
    int added = 0, half = rN / 2;
    for (int t = 0; t < tries && rM < RMAXE; t++) {
        int a = 2 * rndi(half), b = 2 * rndi(half) + 1;
        if (rdeg[a] < d_ && rdeg[b] < d_ && !radj(a, b)) {
            radd(a, b);
            rEa[rM] = a; rEb[rM] = b; rM++;
            added++;
        }
    }
    return added;
}

/* Insert a new vertex pair (na even, nb odd): take d_ edges with distinct ends,
   rewire (a,b) -> (a,nb) and (na,b). Degrees of old vertices are preserved. */
static int rgrow(void) {
    int idx[MAXD];
    if (rN + 2 > RMAXN || rM < d_ || rM + d_ > RMAXE) return 0;
    int found = 0;
    for (int tr = 0; tr < 5000 && !found; tr++) {
        for (int q = 0; q < d_; q++) idx[q] = rndi(rM);
        found = 1;
        for (int p = 0; p < d_ && found; p++)
            for (int q = p + 1; q < d_; q++)
                if (idx[p] == idx[q] || rEa[idx[p]] == rEa[idx[q]] || rEb[idx[p]] == rEb[idx[q]]) {
                    found = 0;
                    break;
                }
    }
    if (!found) return 0;
    int na = rN, nbv = rN + 1;
    for (int q = 0; q < d_; q++) {
        int e = idx[q];
        int a = rEa[e], b = rEb[e];
        rdel(a, b);
        radd(a, nbv);
        radd(na, b);
        rEb[e] = nbv;
        rEa[rM] = na; rEb[rM] = b; rM++;
    }
    rN += 2;
    return 1;
}

static int repair_main(int argc, char **argv) {
    (void)argc;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    if (d_ < 3 || D_ < 3 || d_ > MAXD) { printf("0 0\n"); return 0; }

    int n, m;
    if (scanf("%d %d", &n, &m) != 2) { printf("0 0\n"); return 0; }
    if (n < 2 || n > RMAXN - 2 || (n & 1) || m < 0 || m > RMAXE) { printf("0 0\n"); return 0; }
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { printf("0 0\n"); return 0; }
        if (u < 0 || v < 0 || u >= n || v >= n) { printf("0 0\n"); return 0; }
        if ((u & 1) == 0 && (v & 1) == 1) { tEa[e] = u; tEb[e] = v; }
        else if ((u & 1) == 1 && (v & 1) == 0) { tEa[e] = v; tEb[e] = u; }
        else { printf("0 0\n"); return 0; }
    }
    memset(rmat, 0, sizeof rmat);
    memset(rdeg, 0, sizeof rdeg);
    rN = n;
    rM = 0;
    for (int e = 0; e < m; e++) {
        int a = tEa[e], b = tEb[e];
        if (radj(a, b) || rdeg[a] >= d_ || rdeg[b] >= d_) { printf("0 0\n"); return 0; }
        radd(a, b);
        rEa[e] = a; rEb[e] = b;
        rM++;
    }
    if (rcost() != 0) { printf("0 0\n"); return 0; }
    rsnap();

    double tend = now() + tl;
    while (now() < tend) {
        if (!rgrow()) { rebuild(sN, sM, sEa, sEb); continue; }
        long long cost = rcost();
        int maxit = 4000;
        for (int it = 0; it < maxit && cost > 0; it++) {
            if ((it & 31) == 0 && now() > tend) break;
            if (it % 8 == 0) {
                if (rfill(64) > 0) cost = rcost();
                continue;
            }
            if (rM < 2) break;
            double frac = (double)it / maxit;
            double T = 2.0 * (1.0 - frac) + 0.05;
            int i = rndi(rM), j = rndi(rM);
            if (i == j) continue;
            int a1 = rEa[i], b1 = rEb[i], a2 = rEa[j], b2 = rEb[j];
            if (a1 == a2 || b1 == b2 || radj(a1, b2) || radj(a2, b1)) continue;
            rdel(a1, b1);
            rdel(a2, b2);
            radd(a1, b2);
            radd(a2, b1);
            rEb[i] = b2;
            rEb[j] = b1;
            long long c2 = rcost();
            if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                rdel(a1, b2);
                rdel(a2, b1);
                radd(a1, b1);
                radd(a2, b2);
                rEb[i] = b1;
                rEb[j] = b2;
            }
        }
        if (cost == 0) rsnap();
        else rebuild(sN, sM, sEa, sEb);
    }

    printf("%d %d\n", sN, sM);
    for (int e = 0; e < sM; e++) printf("%d %d\n", sEa[e], sEb[e]);
    return 0;
}

int main(int argc, char **argv) {
    if (argc >= 7 && atoi(argv[6]) == 1) return repair_main(argc, argv);
    return group_main(argc, argv);
}
'''


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _parity_relabel(n, edges):
    """Relabel a bipartite graph so side-A vertices are even and side-B vertices odd.

    Returns (n', edges') with n' = 2*(side size), or None if not bipartite or sides differ in size.
    """
    adj = lib.adjacency(n, edges)
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
                elif color[v] == color[u]:
                    return None
    side0 = [v for v in range(n) if color[v] == 0]
    side1 = [v for v in range(n) if color[v] == 1]
    if not side0 or len(side0) != len(side1):
        return None
    new = [0] * n
    for i, v in enumerate(side0):
        new[v] = 2 * i
    for i, v in enumerate(side1):
        new[v] = 2 * i + 1
    return 2 * len(side0), [(new[u], new[v]) for u, v in edges]


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

    avail = max(1.0, min(0.85 * time_limit, time_limit - 8.0))

    # Stage 1: group-lift search (proven engine), most of the budget.
    group_t = 0.6 * avail
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(group_t, 2), best_n + 1, 0],
                        timeout=group_t + 6.0)
        n, e = lib.parse_graph_text(out)
        if n > 0:
            consider(n, e)
    except Exception:
        pass

    # Stage 2: general edge-repair growth starting from the best graph so far.
    rem = avail - (time.monotonic() - start) - 1.0
    if rem >= 2.0:
        rel = _parity_relabel(best[0], best[1])
        if rel is not None:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed + 1, round(rem, 2), 0, 1],
                                stdin_graph=rel, timeout=rem + 6.0)
                n, e = lib.parse_graph_text(out)
                if n > 0:
                    consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
