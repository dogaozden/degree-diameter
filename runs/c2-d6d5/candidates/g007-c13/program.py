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
#define NMAX 1600
#define WMAX 26

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

static int d_, D_;

/* ===================== Phase 1: group voltage lift search ===================== */
static int K_, G_, N_;
static int *MT = NULL, *RS = NULL;
static int *nb = NULL;
static u64 *rch = NULL, *tmpr = NULL;
static int lay[MAXD][MAXK], VS[MAXD][MAXK];
static int BL[MAXD][MAXK], BV[MAXD][MAXK];
static int *bE = NULL;
static int bEc = 0, bestN = 0, bestSplit = 0;

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

static void s1_snapshot(void) {
    memcpy(BL, lay, sizeof lay);
    memcpy(BV, VS, sizeof VS);
}

static void s1_restore(void) {
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
    s1_snapshot();
    int last = 0, kicks = 0;

    for (int t = 0; t < iters && cost != 0; t++) {
        if ((t & 63) == 0 && now() > tend) break;
        if (t - last > patience) {
            if (kicks >= maxkick) break;
            kicks++;
            s1_restore();
            for (int q = 0; q < 3; q++) {
                int l = rndi(d), i = rndi(k);
                VS[l][i] = rndi(G);
                apply_dart(l, i);
            }
            cost = evalcost();
            if (cost < bestc) { bestc = cost; s1_snapshot(); }
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
        if (cost < bestc) { bestc = cost; last = t; s1_snapshot(); }
    }
    return cost == 0;
}

static void phase1(double tend, int minN) {
    double tl = tend - now();
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
            bestSplit = kG;
            minN = N_ + 1;
        }
    }
}

/* ===================== Phase 2: vertex insertion + edge-rewiring repair ===================== */
static int p2n;
static int p2sd[NMAX], p2deg[NMAX];
static int p2adj[NMAX][MAXD];
static u64 RA[NMAX * WMAX], RB[NMAX * WMAX];
static int p2badc[NMAX];
static int snapN = 0, snapE = 0;
static int snapU[NMAX * MAXD], snapV[NMAX * MAXD];

/* Returns number of unordered pairs at distance > D_; fills p2badc (ordered counts). */
static long long p2eval(void) {
    int n = p2n, W = (n + 63) >> 6;
    u64 *cur = RA, *nxt = RB;
    memset(cur, 0, sizeof(u64) * (size_t)n * W);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int t = 0; t < D_; t++) {
        for (int v = 0; v < n; v++) {
            u64 *dst = nxt + (size_t)v * W;
            const u64 *src = cur + (size_t)v * W;
            for (int w = 0; w < W; w++) dst[w] = src[w];
            for (int j = 0; j < p2deg[v]; j++) {
                const u64 *s2 = cur + (size_t)p2adj[v][j] * W;
                for (int w = 0; w < W; w++) dst[w] |= s2[w];
            }
        }
        u64 *sw = cur; cur = nxt; nxt = sw;
    }
    long long tot = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        const u64 *src = cur + (size_t)v * W;
        for (int w = 0; w < W; w++) c += popc(src[w]);
        p2badc[v] = n - c;
        tot += n - c;
    }
    return tot / 2;
}

static int p2isadj(int a, int b) {
    if (p2deg[a] > p2deg[b]) { int t = a; a = b; b = t; }
    for (int j = 0; j < p2deg[a]; j++) if (p2adj[a][j] == b) return 1;
    return 0;
}

static void p2addE(int a, int b) {
    p2adj[a][p2deg[a]++] = b;
    p2adj[b][p2deg[b]++] = a;
}

static void p2delE1(int a, int b) {
    for (int j = 0; j < p2deg[a]; j++)
        if (p2adj[a][j] == b) { p2adj[a][j] = p2adj[a][--p2deg[a]]; return; }
}

static void p2remE(int a, int b) { p2delE1(a, b); p2delE1(b, a); }

typedef struct { int nr, na; int ru[2], rv[2], au[2], av[2]; } MoveRec;

static void mrem(MoveRec *m, int a, int b) {
    p2remE(a, b);
    m->ru[m->nr] = a; m->rv[m->nr] = b; m->nr++;
}

static void madd(MoveRec *m, int a, int b) {
    p2addE(a, b);
    m->au[m->na] = a; m->av[m->na] = b; m->na++;
}

static void mundo(MoveRec *m) {
    for (int i = m->na - 1; i >= 0; i--) p2remE(m->au[i], m->av[i]);
    for (int i = 0; i < m->nr; i++) p2addE(m->ru[i], m->rv[i]);
    m->nr = m->na = 0;
}

static int p2ok(int v, int mode) { return mode == 0 ? p2deg[v] > 0 : p2deg[v] < d_; }

/* Uniform random vertex on `side` satisfying mode (0: has edges, 1: has spare degree). */
static int p2pick(int side, int mode) {
    int cnt = 0;
    for (int v = 0; v < p2n; v++) if (p2sd[v] == side && p2ok(v, mode)) cnt++;
    if (!cnt) return -1;
    int r = rndi(cnt);
    for (int v = 0; v < p2n; v++)
        if (p2sd[v] == side && p2ok(v, mode)) { if (r == 0) return v; r--; }
    return -1;
}

static int p2pickvertex(void) {
    for (int t = 0; t < 30; t++) {
        int v = rndi(p2n);
        if (p2badc[v] > 0) return v;
    }
    return rndi(p2n);
}

/* One random bipartite-preserving move: swap (degree-preserving) or transfer (moves spare degree). */
static int p2move(MoveRec *m) {
    m->nr = m->na = 0;
    int x = p2pickvertex();
    if (p2deg[x] == 0) return 0;
    int y = p2adj[x][rndi(p2deg[x])];
    int a1 = (p2sd[x] == 0) ? x : y;
    int b1 = (p2sd[x] == 0) ? y : x;
    if (rndu() < 0.5) {
        int a2 = p2pick(0, 0);
        if (a2 < 0 || a2 == a1) return 0;
        int b2 = p2adj[a2][rndi(p2deg[a2])];
        if (b2 == b1) return 0;
        if (p2isadj(a1, b2) || p2isadj(a2, b1)) return 0;
        mrem(m, a1, b1); mrem(m, a2, b2);
        madd(m, a1, b2); madd(m, a2, b1);
        return 1;
    }
    if (rndu() < 0.5) {
        int b2 = p2pick(1, 1);
        if (b2 < 0 || b2 == b1 || p2isadj(a1, b2)) return 0;
        mrem(m, a1, b1);
        madd(m, a1, b2);
        return 1;
    } else {
        int a2 = p2pick(0, 1);
        if (a2 < 0 || a2 == a1 || p2isadj(a2, b1)) return 0;
        mrem(m, a1, b1);
        madd(m, a2, b1);
        return 1;
    }
}

/* Add every edge between spare-degree vertices on opposite sides that is still missing. */
static int p2greedy(void) {
    int added = 0;
    for (int a = 0; a < p2n; a++) {
        if (p2sd[a] != 0 || p2deg[a] >= d_) continue;
        for (int b = 0; b < p2n && p2deg[a] < d_; b++) {
            if (p2sd[b] != 1 || p2deg[b] >= d_) continue;
            if (p2isadj(a, b)) continue;
            p2addE(a, b);
            added = 1;
        }
    }
    return added;
}

static void p2insert(void) {
    p2sd[p2n] = 0; p2sd[p2n + 1] = 1;
    p2deg[p2n] = 0; p2deg[p2n + 1] = 0;
    p2n += 2;
}

static void p2snapshot(void) {
    int c = 0;
    for (int u = 0; u < p2n; u++)
        for (int j = 0; j < p2deg[u]; j++) {
            int v = p2adj[u][j];
            if (u < v) { snapU[c] = u; snapV[c] = v; c++; }
        }
    snapN = p2n;
    snapE = c;
}

static void p2restore(void) {
    for (int v = 0; v < NMAX; v++) p2deg[v] = 0;
    p2n = snapN;
    for (int e = 0; e < snapE; e++) p2addE(snapU[e], snapV[e]);
}

static void phase2(double tend) {
    p2n = bestN;
    for (int v = 0; v < p2n; v++) { p2deg[v] = 0; p2sd[v] = (v >= bestSplit) ? 1 : 0; }
    for (int e = 0; e < bEc; e++) p2addE(bE[2 * e], bE[2 * e + 1]);
    long long cur = p2eval();
    if (cur != 0) { snapN = 0; return; }
    p2snapshot();
    if (p2n + 2 > NMAX) return;
    p2insert();
    cur = p2eval();

    const int PAT = 20000;
    int stall = 0;
    MoveRec mr;
    while (now() < tend) {
        if (cur == 0) {
            p2snapshot();
            if (p2n + 2 > NMAX) break;
            p2insert();
            cur = p2eval();
            stall = 0;
            continue;
        }
        if (p2greedy()) { cur = p2eval(); continue; }
        stall++;
        if (stall > PAT) {
            p2restore();
            if (p2n + 2 > NMAX) break;
            p2insert();
            for (int k = 0; k < 6; k++) p2move(&mr);
            mr.nr = mr.na = 0;
            cur = p2eval();
            stall = 0;
            continue;
        }
        double T = 2.0 * (1.0 - (double)stall / PAT);
        if (T < 0.05) T = 0.05;
        long long old = cur;
        if (!p2move(&mr)) continue;
        long long nc = p2eval();
        if (nc <= old || rndu() < exp(-(double)(nc - old) / T)) {
            cur = nc;
        } else {
            mundo(&mr);
        }
    }
    if (cur == 0) p2snapshot();
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

    double t0 = now();
    double tend = t0 + tl;
    double tend1 = t0 + 0.6 * tl;

    phase1(tend1, minN);
    if (bestN == 0) { printf("0 0\n"); return 0; }

    phase2(tend);

    if (snapN > 0) {
        printf("%d %d\n", snapN, snapE);
        for (int e = 0; e < snapE; e++) printf("%d %d\n", snapU[e], snapV[e]);
    } else {
        printf("%d %d\n", bestN, bEc);
        for (int p = 0; p < bEc; p++) printf("%d %d\n", bE[2 * p], bE[2 * p + 1]);
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

    budget = max(0.5, min(0.85 * time_limit, time_limit - 9.0))
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
