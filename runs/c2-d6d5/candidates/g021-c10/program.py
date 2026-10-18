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
#define MAXGROW 600

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

static int d_ = 0, D_ = 0;

/* ===================== Phase A: group-lift search ===================== */
/* Group Z_m x| Z_k2 with (a,b)(c,e) = (a + r^b c, b + e). Element a*k2+b. */
static int *gMT = NULL, *gRS = NULL, *gnb = NULL;
static u64 *grch = NULL, *gtmp = NULL;
static int gKc = 1, gGc = 1, gNc = 2;
static int glay[MAXD][MAXK], gVS[MAXD][MAXK];
static int gBL[MAXD][MAXK], gBV[MAXD][MAXK];
static int *gE = NULL, gEc = 0, gbestN = 0, gminN = 2;

static int build_group(int m, int k2, int r) {
    int G = m * k2;
    if (G > GMAX) return 0;
    gGc = G;
    free(gMT); free(gRS);
    gMT = malloc(sizeof(int) * (size_t)G * G);
    gRS = malloc(sizeof(int) * (size_t)G * G);
    int *pwr = malloc(sizeof(int) * (size_t)k2);
    pwr[0] = 1 % m;
    for (int t = 1; t < k2; t++) pwr[t] = (int)((long long)pwr[t - 1] * r % m);
    for (int x = 0; x < G; x++) {
        int a = x / k2, b = x % k2;
        for (int y = 0; y < G; y++) {
            int c = y / k2, e = y % k2;
            int aa = (int)((a + (long long)pwr[b] * c) % m);
            gMT[x * G + y] = aa * k2 + (b + e) % k2;
        }
    }
    for (int g = 0; g < G; g++)
        for (int s = 0; s < G; s++)
            gRS[s * G + gMT[g * G + s]] = g;
    free(pwr);
    return 1;
}

static void alloc_gstate(void) {
    free(gnb); free(grch); free(gtmp);
    gNc = 2 * gKc * gGc;
    gnb = malloc(sizeof(int) * (size_t)d_ * gNc);
    grch = malloc(sizeof(u64) * (size_t)gNc);
    gtmp = malloc(sizeof(u64) * (size_t)gNc);
}

/* Dart (l, i, j, s): A_{i,g} ~ B_{j, g*s}. */
static void gsetdart(int l, int i, int j, int s) {
    int G = gGc, k = gKc, N = gNc;
    int *row = gnb + (size_t)l * N;
    for (int g = 0; g < G; g++) {
        row[i * G + g] = (k + j) * G + gMT[g * G + s];
        row[(k + j) * G + g] = i * G + gRS[s * G + g];
    }
}
static void gapply(int l, int i) { gsetdart(l, i, glay[l][i], gVS[l][i]); }

static void gsnapshot(void) {
    memcpy(gBL, glay, sizeof glay);
    memcpy(gBV, gVS, sizeof gVS);
}
static void grestore(void) {
    for (int l = 0; l < d_; l++)
        for (int i = 0; i < gKc; i++) { glay[l][i] = gBL[l][i]; gVS[l][i] = gBV[l][i]; }
    for (int l = 0; l < d_; l++)
        for (int i = 0; i < gKc; i++) gapply(l, i);
}

static long long gevalcost(void) {
    int N = gNc, G = gGc, k = gKc, d = d_;
    for (int v = 0; v < N; v++) grch[v] = 0;
    for (int b = 0; b < 2 * k; b++) grch[(size_t)b * G] = 1ULL << b;
    for (int t = 0; t < D_; t++) {
        for (int v = 0; v < N; v++) {
            u64 x = grch[v];
            for (int l = 0; l < d; l++) x |= grch[gnb[(size_t)l * N + v]];
            gtmp[v] = x;
        }
        u64 *sw = grch; grch = gtmp; gtmp = sw;
    }
    long long cnt = 0;
    for (int v = 0; v < N; v++) cnt += popc(grch[v]);
    long long unreached = (long long)2 * k * N - cnt;
    long long dup = 0;
    for (int i = 0; i < k; i++)
        for (int l = 0; l < d; l++)
            for (int l2 = l + 1; l2 < d; l2++)
                if (glay[l][i] == glay[l2][i] && gVS[l][i] == gVS[l2][i]) dup++;
    return unreached + 1000 * dup;
}

static int gsearch(double tend, int iters, int patience, int maxkick) {
    int k = gKc, d = d_, G = gGc;
    u64 full = (1ULL << (2 * k)) - 1;
    for (int l = 0; l < d; l++) {
        int perm[MAXK];
        for (int i = 0; i < k; i++) perm[i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rndi(i + 1);
            int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
        }
        for (int i = 0; i < k; i++) { glay[l][i] = perm[i]; gVS[l][i] = rndi(G); }
    }
    for (int l = 0; l < d; l++)
        for (int i = 0; i < k; i++) gapply(l, i);
    long long cost = gevalcost();
    double c0 = (double)(cost > 0 ? cost : 1);
    long long bestc = cost;
    gsnapshot();
    int last = 0, kicks = 0;

    for (int t = 0; t < iters && cost != 0; t++) {
        if ((t & 63) == 0 && now() > tend) break;
        if (t - last > patience) {
            if (kicks >= maxkick) break;
            kicks++;
            grestore();
            for (int q = 0; q < 3; q++) {
                int l = rndi(d), i = rndi(k);
                gVS[l][i] = rndi(G);
                gapply(l, i);
            }
            cost = gevalcost();
            if (cost < bestc) { bestc = cost; gsnapshot(); }
            last = t;
            continue;
        }
        double temp = 0.02 * c0 * (1.0 - (double)t / iters);
        if (temp < 0.3) temp = 0.3;

        if (k >= 2 && rndu() < 0.25) {
            int l = rndi(d);
            int i1 = rndi(k), i2 = rndi(k - 1);
            if (i2 >= i1) i2++;
            int t1 = glay[l][i1], t2 = glay[l][i2];
            glay[l][i1] = t2; glay[l][i2] = t1;
            gapply(l, i1);
            gapply(l, i2);
            long long c2 = gevalcost();
            if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
            } else {
                glay[l][i1] = t1; glay[l][i2] = t2;
                gapply(l, i1);
                gapply(l, i2);
            }
        } else {
            int l = 0, i = 0, picked = 0;
            if (rndu() < 0.4) {
                int start = rndi(gNc), v = -1;
                for (int q = 0; q < gNc; q++) {
                    int w = (start + q) % gNc;
                    if (grch[w] != full) { v = w; break; }
                }
                if (v >= 0) {
                    int b = v / G;
                    l = rndi(d);
                    if (b < k) i = b;
                    else {
                        int jb = b - k;
                        i = -1;
                        for (int ii = 0; ii < k; ii++)
                            if (glay[l][ii] == jb) { i = ii; break; }
                        if (i < 0) i = rndi(k);
                    }
                    picked = 1;
                }
            }
            if (!picked) { l = rndi(d); i = rndi(k); }
            int old = gVS[l][i];
            int nw = rndi(G);
            if (nw == old) continue;
            gVS[l][i] = nw;
            gapply(l, i);
            long long c2 = gevalcost();
            if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
            } else {
                gVS[l][i] = old;
                gapply(l, i);
            }
        }
        if (cost < bestc) { bestc = cost; last = t; gsnapshot(); }
    }
    return cost == 0;
}

static void group_phase(double tend) {
    static const int Ks[10] = {1, 1, 1, 2, 2, 2, 3, 3, 4, 5};
    static const int K2s[13] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12};
    static int cand[GMAX + 5];
    while (now() < tend) {
        int k = Ks[rndi(10)];
        if (k > MAXK) k = MAXK;
        int Gmin = (gminN + 2 * k - 1) / (2 * k);
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
        gKc = k;
        alloc_gstate();
        int ok = gsearch(tend, 20000, 3000, 6);
        if (ok && gNc > gbestN) {
            int kG = gKc * gGc;
            int cnt = kG * d_;
            int *ne = malloc(sizeof(int) * 2 * (size_t)cnt);
            int p = 0;
            for (int u = 0; u < kG; u++)
                for (int l = 0; l < d_; l++) {
                    ne[2 * p] = u;
                    ne[2 * p + 1] = gnb[(size_t)l * gNc + u];
                    p++;
                }
            free(gE);
            gE = ne;
            gEc = cnt;
            gbestN = gNc;
            gminN = gNc + 1;
        }
    }
}

/* ============ Phase B: explicit vertex insertion + double-edge-swap annealing ============
   The graph stays d-regular and bipartite (A = side 0, B = side 1).
   Insertion adds an A-vertex x and a B-vertex y: pick a matching (a_i,b_i) of d edges,
   delete them, join x to every b_i and y to every a_i. Degrees and bipartiteness are kept.
   Cost = ordered pairs at distance > D (via bitsets). Double-edge swaps anneal it to 0. */
static int xN = 0, xCap = 0, xCapW = 1, savN = 0, xstampc = 0;
static int *xadj = NULL, *xstamp = NULL, *savadj = NULL;
static unsigned char *xside = NULL, *savside = NULL;
static u64 *xR = NULL, *xT = NULL;

static int xhas(int u, int v) {
    const int *row = xadj + (size_t)u * d_;
    for (int j = 0; j < d_; j++) if (row[j] == v) return 1;
    return 0;
}

static void xrep(int u, int oldv, int newv) {
    int *row = xadj + (size_t)u * d_;
    for (int j = 0; j < d_; j++) if (row[j] == oldv) { row[j] = newv; return; }
}

static long long xcost(void) {
    int N = xN, d = d_, W = (N + 63) >> 6;
    u64 *R = xR, *T = xT;
    memset(R, 0, sizeof(u64) * (size_t)N * W);
    for (int v = 0; v < N; v++) R[(size_t)v * W + (v >> 6)] = 1ULL << (v & 63);
    for (int t = 0; t < D_; t++) {
        for (int v = 0; v < N; v++) {
            u64 *out = T + (size_t)v * W;
            const u64 *src = R + (size_t)v * W;
            for (int w = 0; w < W; w++) out[w] = src[w];
            const int *row = xadj + (size_t)v * d;
            for (int j = 0; j < d; j++) {
                const u64 *s2 = R + (size_t)row[j] * W;
                for (int w = 0; w < W; w++) out[w] |= s2[w];
            }
        }
        u64 *sw = R; R = T; T = sw;
    }
    long long cnt = 0;
    size_t tot = (size_t)N * W;
    for (size_t q = 0; q < tot; q++) cnt += popc(R[q]);
    return (long long)N * N - cnt;
}

static int xswap(int *A1, int *A2, int *B1, int *B2) {
    int d = d_;
    int a1, a2;
    do { a1 = rndi(xN); } while (xside[a1] != 0);
    do { a2 = rndi(xN); } while (xside[a2] != 0 || a2 == a1);
    int b1 = xadj[(size_t)a1 * d + rndi(d)];
    int b2 = xadj[(size_t)a2 * d + rndi(d)];
    if (b1 == b2 || xhas(a1, b2) || xhas(a2, b1)) return 0;
    xrep(a1, b1, b2);
    xrep(a2, b2, b1);
    xrep(b1, a1, a2);
    xrep(b2, a2, a1);
    *A1 = a1; *A2 = a2; *B1 = b1; *B2 = b2;
    return 1;
}

static void xundo(int a1, int a2, int b1, int b2) {
    xrep(a1, b2, b1);
    xrep(a2, b1, b2);
    xrep(b1, a2, a1);
    xrep(b2, a1, a2);
}

static int xinsert(void) {
    int N = xN, d = d_;
    if (N + 2 > xCap) return 0;
    xstampc++;
    int pa[MAXD], pb[MAXD], cnt = 0;
    for (int tr = 0; tr < 400 * d && cnt < d; tr++) {
        int a = rndi(N);
        if (xside[a] != 0) continue;
        int b = xadj[(size_t)a * d + rndi(d)];
        if (xstamp[a] == xstampc || xstamp[b] == xstampc) continue;
        xstamp[a] = xstampc;
        xstamp[b] = xstampc;
        pa[cnt] = a; pb[cnt] = b; cnt++;
    }
    if (cnt < d) return 0;
    int x = N, y = N + 1;
    xside[x] = 0;
    xside[y] = 1;
    for (int i = 0; i < d; i++) {
        int a = pa[i], b = pb[i];
        xrep(a, b, y);
        xrep(b, a, x);
        xadj[(size_t)x * d + i] = b;
        xadj[(size_t)y * d + i] = a;
    }
    xN = N + 2;
    return 1;
}

static int xanneal(int maxit, double tend, long long *outc) {
    long long cost = xcost();
    for (int it = 0; it < maxit && cost > 0; it++) {
        if ((it & 15) == 0 && now() > tend) break;
        double T = 6.0 * (1.0 - (double)it / maxit) + 0.25;
        int a1, a2, b1, b2;
        if (!xswap(&a1, &a2, &b1, &b2)) continue;
        long long c2 = xcost();
        long long delta = c2 - cost;
        if (delta <= 0 || rndu() < exp(-(double)delta / T)) cost = c2;
        else xundo(a1, a2, b1, b2);
    }
    *outc = cost;
    return cost == 0;
}

static void save_state(void) {
    savN = xN;
    memcpy(savadj, xadj, sizeof(int) * (size_t)xN * d_);
    memcpy(savside, xside, (size_t)xN);
}

static void load_state(void) {
    xN = savN;
    memcpy(xadj, savadj, sizeof(int) * (size_t)savN * d_);
    memcpy(xside, savside, (size_t)savN);
}

static int load_group_graph(void) {
    int N = gbestN, d = d_;
    xCap = N + MAXGROW;
    xCapW = (xCap + 63) >> 6;
    xadj = malloc(sizeof(int) * (size_t)xCap * d);
    xside = malloc((size_t)xCap);
    xstamp = calloc((size_t)xCap, sizeof(int));
    xR = malloc(sizeof(u64) * (size_t)xCap * xCapW);
    xT = malloc(sizeof(u64) * (size_t)xCap * xCapW);
    savadj = malloc(sizeof(int) * (size_t)xCap * d);
    savside = malloc((size_t)xCap);
    int *deg = calloc((size_t)N, sizeof(int));
    for (int v = 0; v < N; v++) xside[v] = (v >= N / 2) ? 1 : 0;
    for (int p = 0; p < gEc; p++) {
        int u = gE[2 * p], v = gE[2 * p + 1];
        if (deg[u] >= d || deg[v] >= d) { free(deg); return 0; }
        xadj[(size_t)u * d + deg[u]++] = v;
        xadj[(size_t)v * d + deg[v]++] = u;
    }
    for (int v = 0; v < N; v++)
        if (deg[v] != d) { free(deg); return 0; }
    free(deg);
    xN = N;
    return 1;
}

static void expansion_phase(double tend) {
    save_state();
    while (now() < tend && savN + 2 <= xCap) {
        load_state();
        if (!xinsert()) continue;
        long long c;
        if (xanneal(2500, tend, &c)) save_state();
    }
}

static void print_saved(void) {
    int N = savN, d = d_;
    long long m = 0;
    for (int u = 0; u < N; u++) if (savside[u] == 0) m += d;
    printf("%d %lld\n", N, m);
    for (int u = 0; u < N; u++)
        if (savside[u] == 0)
            for (int j = 0; j < d; j++)
                printf("%d %d\n", u, savadj[(size_t)u * d + j]);
}

static void print_group(void) {
    printf("%d %d\n", gbestN, gEc);
    for (int p = 0; p < gEc; p++) printf("%d %d\n", gE[2 * p], gE[2 * p + 1]);
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

    double t0 = now();
    group_phase(t0 + 0.55 * tl);
    if (gbestN == 0) { printf("0 0\n"); return 0; }
    if (!load_group_graph()) { print_group(); return 0; }
    expansion_phase(t0 + tl - 0.6);
    print_saved();
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

    budget = max(0.5, min(0.8 * time_limit, time_limit - 8.0))
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                        timeout=budget + 6.0)
        n, e = lib.parse_graph_text(out)
        if n > 0:
            consider(n, e)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
