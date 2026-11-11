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
#define MAXV 1500
#define MAXDG 16
#define MAXW 24

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

/* ---------- Phase 2: general bipartite graph annealing that adds vertex pairs ---------- */

typedef u64 row_t[MAXW];
static int gadj[MAXV][MAXDG], gdeg[MAXV];
static int sl[2][MAXV], nsl[2];
static int gN = 0;
static int bestAdj[MAXV][MAXDG], bestDeg[MAXV];
static int bestNg = 0;
static row_t GR1[MAXV], GR2[MAXV];
static int gkind, gu1, gu2, gu3, gu4;

static int g_has(int a, int b) {
    for (int i = 0; i < gdeg[a]; i++) if (gadj[a][i] == b) return 1;
    return 0;
}
static void g_add(int a, int b) { gadj[a][gdeg[a]++] = b; gadj[b][gdeg[b]++] = a; }
static void g_delh(int a, int b) {
    for (int i = 0; i < gdeg[a]; i++)
        if (gadj[a][i] == b) { gadj[a][i] = gadj[a][--gdeg[a]]; return; }
}
static void g_del(int a, int b) { g_delh(a, b); g_delh(b, a); }

static long long g_cost(void) {
    int N = gN, W = (N + 63) / 64;
    row_t *cur = GR1, *nxt = GR2, *tmp;
    for (int v = 0; v < N; v++) {
        for (int w = 0; w < W; w++) cur[v][w] = 0;
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int t = 0; t < D_; t++) {
        for (int v = 0; v < N; v++) {
            for (int w = 0; w < W; w++) nxt[v][w] = cur[v][w];
            for (int i = 0; i < gdeg[v]; i++) {
                int u = gadj[v][i];
                for (int w = 0; w < W; w++) nxt[v][w] |= cur[u][w];
            }
        }
        tmp = cur; cur = nxt; nxt = tmp;
    }
    long long cnt = 0;
    for (int v = 0; v < N; v++)
        for (int w = 0; w < W; w++) cnt += popc(cur[v][w]);
    return ((long long)N * N - cnt) / 2;
}

static int g_pick(int s) {
    for (int t = 0; t < 60; t++) {
        int v = sl[s][rndi(nsl[s])];
        if (gdeg[v] > 0) return v;
    }
    return -1;
}

/* Double-edge swap between two side-0 vertices: keeps all degrees. */
static int g_swap(void) {
    int a = g_pick(0); if (a < 0) return 0;
    int b = gadj[a][rndi(gdeg[a])];
    int c = g_pick(0); if (c < 0) return 0;
    int e = gadj[c][rndi(gdeg[c])];
    if (a == c || b == e || g_has(a, e) || g_has(c, b)) return 0;
    g_del(a, b); g_del(c, e); g_add(a, e); g_add(c, b);
    gkind = 0; gu1 = a; gu2 = b; gu3 = c; gu4 = e;
    return 1;
}

/* Move one deficient vertex's missing edge: remove (a,b), add (x,b). */
static int g_transfer(void) {
    int s = rndi(2);
    int gc[MAXV], nc = 0;
    for (int i = 0; i < nsl[s]; i++) {
        int v = sl[s][i];
        if (gdeg[v] < d_) gc[nc++] = v;
    }
    if (!nc) return 0;
    int x = gc[rndi(nc)];
    int a = g_pick(s); if (a < 0 || a == x) return 0;
    int b = gadj[a][rndi(gdeg[a])];
    if (g_has(x, b)) return 0;
    g_del(a, b); g_add(x, b);
    gkind = 1; gu1 = x; gu2 = a; gu3 = b;
    return 1;
}

static void g_undo(void) {
    if (gkind == 0) {
        g_del(gu1, gu4); g_del(gu3, gu2);
        g_add(gu1, gu2); g_add(gu3, gu4);
    } else {
        g_del(gu1, gu3); g_add(gu2, gu3);
    }
}

static void g_save(void) {
    memcpy(bestAdj, gadj, sizeof gadj);
    memcpy(bestDeg, gdeg, sizeof gdeg);
    bestNg = gN;
}

static void g_grow(void) {
    int a = gN, b = gN + 1;
    gdeg[a] = gdeg[b] = 0;
    sl[0][nsl[0]++] = a;
    sl[1][nsl[1]++] = b;
    gN += 2;
}

static void grow_phase(const int *E, int Ec, int n, double T_end) {
    gN = n;
    int kG = n / 2;
    memset(gdeg, 0, sizeof gdeg);
    nsl[0] = nsl[1] = 0;
    for (int v = 0; v < n; v++) {
        int s = v < kG ? 0 : 1;
        sl[s][nsl[s]++] = v;
    }
    for (int p = 0; p < Ec; p++) g_add(E[2 * p], E[2 * p + 1]);
    long long cost = g_cost();
    if (cost != 0) return;
    g_save();

    const double T0 = 2.0, T1 = 0.1;
    double ts = now();
    double span = T_end - ts;
    if (span <= 0) return;
    while (1) {
        double tn = now();
        if (tn >= T_end) break;
        if (cost == 0) {
            g_save();
            if (gN + 2 > MAXV - 2) break;
            g_grow();
            cost = g_cost();
            ts = now();
            span = T_end - ts;
            if (span <= 0) break;
            continue;
        }
        double fr = (tn - ts) / span;
        if (fr > 1.0) fr = 1.0;
        double temp = T0 * pow(T1 / T0, fr);
        int ok = (rndu() < 0.5) ? g_swap() : g_transfer();
        if (!ok) continue;
        long long nc = g_cost();
        if (nc <= cost || rndu() < exp(-(double)(nc - cost) / temp)) cost = nc;
        else g_undo();
    }
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

    double T_all = now() + tl;
    double tend = now() + 0.4 * tl;
    double slice = (tend - now()) / 6.0;
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
    int groupN = bestN;
    if (bestN <= MAXV - 4 && bEc > 0)
        grow_phase(bE, bEc, bestN, T_all);

    if (bestNg > groupN) {
        long long cnt = 0;
        for (int v = 0; v < bestNg; v++)
            for (int i = 0; i < bestDeg[v]; i++)
                if (bestAdj[v][i] > v) cnt++;
        printf("%d %lld\n", bestNg, cnt);
        for (int v = 0; v < bestNg; v++)
            for (int i = 0; i < bestDeg[v]; i++)
                if (bestAdj[v][i] > v) printf("%d %d\n", v, bestAdj[v][i]);
        return 0;
    }
    printf("%d %d\n", bestN, bEc);
    for (int p = 0; p < bEc; p++) printf("%d %d\n", bE[2 * p], bE[2 * p + 1]);
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

    budget = max(0.5, min(0.85 * time_limit, time_limit - 8.0))
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), best_n + 1],
                        timeout=budget + 6.0)
        n, e = lib.parse_graph_text(out)
        if n > 0:
            consider(n, e)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
