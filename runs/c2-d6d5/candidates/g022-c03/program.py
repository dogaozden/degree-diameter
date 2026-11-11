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
#define LIFT_FRAC 0.45

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

/* ---------- Stage 1: group-lift search (as in the parent) ---------- */

static int d_, D_, K_, G_, N_;
static int *MT = NULL, *RS = NULL;
static int *nb = NULL;
static u64 *rch = NULL, *tmpr = NULL;
static int lay[MAXD][MAXK], VS[MAXD][MAXK];
static int BL[MAXD][MAXK], BV[MAXD][MAXK];
static int bestN = 0, bestHalf = 0;
static int *bestA = NULL;

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

/* ---------- Stage 2: vertex splitting + double-edge-swap annealing ----------
   The lift gives a d-regular bipartite graph with 2n vertices (A = 0..n-1,
   B = n..2n-1 in output). Growth adds one A-vertex and one B-vertex by
   "splitting" d edges (a_i,b_i): a_i-b* and a*-b_i replace a_i-b_i. This keeps
   every degree equal to d and adds 2 vertices. The defects are then removed by
   annealing over degree-preserving double-edge swaps, with cost = unreached
   ordered pairs at distance > D. */

static int *GA = NULL, *GB = NULL;   /* working adjacency: GA[a*d+j]=b, GB[b*d+j]=a */
static int *BA = NULL, *BB = NULL;   /* last valid graph */
static int bgn = 0;
static u64 *gbits = NULL, *gtmp = NULL;
static size_t gbcap = 0;
static int *gbad = NULL;
static int gbadcap = 0;

static void ensure_bits(int n) {
    size_t W = (size_t)(2 * n + 63) / 64;
    size_t need = (size_t)2 * n * W;
    if (need > gbcap) {
        gbcap = need + need / 4 + 64;
        free(gbits); free(gtmp);
        gbits = malloc(sizeof(u64) * gbcap);
        gtmp = malloc(sizeof(u64) * gbcap);
    }
    if (2 * n > gbadcap) {
        gbadcap = 2 * n + 64;
        free(gbad);
        gbad = malloc(sizeof(int) * (size_t)gbadcap);
    }
}

static int contains_(const int *row, int d, int x) {
    for (int j = 0; j < d; j++) if (row[j] == x) return 1;
    return 0;
}

static void replace_(int *row, int d, int oldv, int newv) {
    for (int j = 0; j < d; j++) if (row[j] == oldv) { row[j] = newv; return; }
}

/* Unreached ordered pairs after D rounds of bitset BFS; fills gbad per vertex. */
static long long geval(int n, int d, int D) {
    int N2 = 2 * n;
    size_t W = (size_t)(N2 + 63) / 64;
    for (int v = 0; v < N2; v++) {
        u64 *r = gbits + (size_t)v * W;
        memset(r, 0, sizeof(u64) * W);
        r[v >> 6] |= 1ULL << (v & 63);
    }
    for (int t = 0; t < D; t++) {
        for (int v = 0; v < N2; v++) {
            u64 *dst = gtmp + (size_t)v * W;
            const u64 *src = gbits + (size_t)v * W;
            memcpy(dst, src, sizeof(u64) * W);
            for (int j = 0; j < d; j++) {
                int u = (v < n) ? n + GA[v * d + j] : GB[(v - n) * d + j];
                const u64 *s2 = gbits + (size_t)u * W;
                for (size_t w = 0; w < W; w++) dst[w] |= s2[w];
            }
        }
        u64 *sw = gbits; gbits = gtmp; gtmp = sw;
    }
    long long total = 0;
    for (int v = 0; v < N2; v++) {
        const u64 *r = gbits + (size_t)v * W;
        int c = 0;
        for (size_t w = 0; w < W; w++) c += popc(r[w]);
        gbad[v] = N2 - c;
        total += N2 - c;
    }
    return total;
}

/* Split d edges around a new vertex pair (a* = n in A, b* = n in B). */
static int gsplit(int n, int d) {
    int a[MAXD], jj[MAXD], b[MAXD];
    for (int i = 0; i < d; i++) {
        int ok;
        do {
            ok = 1;
            a[i] = rndi(n);
            for (int p = 0; p < i; p++) if (a[p] == a[i]) ok = 0;
        } while (!ok);
        jj[i] = rndi(d);
        b[i] = GA[a[i] * d + jj[i]];
        for (int p = 0; p < i; p++) if (b[p] == b[i]) return 0;
    }
    int ns = n;
    for (int i = 0; i < d; i++) GA[ns * d + i] = b[i];
    for (int i = 0; i < d; i++) {
        GA[a[i] * d + jj[i]] = ns;
        GB[ns * d + i] = a[i];
    }
    for (int i = 0; i < d; i++) replace_(GB + b[i] * d, d, a[i], ns);
    return 1;
}

/* Annealing over double-edge swaps; returns 1 if the state reaches cost 0. */
static int gsearch(int n, int d, int D, double tend, long long iters) {
    long long cur = geval(n, d, D);
    double c0 = cur > 0 ? (double)cur : 1.0;
    double T0 = 1.0 + 0.02 * c0, T1 = 0.1;
    for (long long t = 0; t < iters && cur != 0; t++) {
        if ((t & 31) == 0 && now() > tend) break;
        double T = T0 * pow(T1 / T0, (double)t / (double)iters);
        int a1 = -1;
        if (rndu() < 0.5) {
            for (int tries = 0; tries < 8; tries++) {
                int v = rndi(2 * n);
                if (gbad[v] > 0) {
                    a1 = (v < n) ? v : GB[(v - n) * d + rndi(d)];
                    break;
                }
            }
        }
        if (a1 < 0) a1 = rndi(n);
        int j1 = rndi(d);
        int a2 = rndi(n);
        if (a2 == a1) continue;
        int j2 = rndi(d);
        int b1 = GA[a1 * d + j1], b2 = GA[a2 * d + j2];
        if (b1 == b2) continue;
        if (contains_(GA + a1 * d, d, b2) || contains_(GA + a2 * d, d, b1)) continue;
        GA[a1 * d + j1] = b2;
        GA[a2 * d + j2] = b1;
        replace_(GB + b1 * d, d, a1, a2);
        replace_(GB + b2 * d, d, a2, a1);
        long long c2 = geval(n, d, D);
        if (c2 <= cur || rndu() < exp(-(double)(c2 - cur) / T)) {
            cur = c2;
        } else {
            GA[a1 * d + j1] = b1;
            GA[a2 * d + j2] = b2;
            replace_(GB + b1 * d, d, a2, a1);
            replace_(GB + b2 * d, d, a1, a2);
        }
    }
    return cur == 0;
}

static void growth(double tend, int d, int D) {
    int n = bgn;
    long long iters = 20000;
    while (now() < tend && n < 3000) {
        int ok = 0;
        for (int att = 0; att < 4 && !ok && now() < tend; att++) {
            int m = n + 1;
            GA = realloc(GA, sizeof(int) * (size_t)m * d);
            GB = realloc(GB, sizeof(int) * (size_t)m * d);
            memcpy(GA, BA, sizeof(int) * (size_t)n * d);
            memcpy(GB, BB, sizeof(int) * (size_t)n * d);
            ensure_bits(m);
            if (!gsplit(n, d)) continue;
            ok = gsearch(m, d, D, tend, iters);
        }
        if (!ok) break;
        n++;
        BA = realloc(BA, sizeof(int) * (size_t)n * d);
        BB = realloc(BB, sizeof(int) * (size_t)n * d);
        memcpy(BA, GA, sizeof(int) * (size_t)n * d);
        memcpy(BB, GB, sizeof(int) * (size_t)n * d);
        bgn = n;
    }
}

static void build_B(int n, int d, const int *A, int *B) {
    int *cnt = calloc((size_t)n, sizeof(int));
    for (int a = 0; a < n; a++)
        for (int j = 0; j < d; j++) {
            int b = A[a * d + j];
            if (cnt[b] < d) B[b * d + cnt[b]] = a;
            cnt[b]++;
        }
    free(cnt);
}

static void output_graph(int n, int d, const int *A) {
    printf("%d %d\n", 2 * n, n * d);
    for (int a = 0; a < n; a++)
        for (int j = 0; j < d; j++)
            printf("%d %d\n", a, n + A[a * d + j]);
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    int minN = argc > 5 ? atoi(argv[5]) : 2;
    if (minN < 2) minN = 2;
    if (d_ < 3 || D_ < 3 || d_ > MAXD) { printf("0 0\n"); return 0; }
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    double t0 = now();
    double tend = t0 + tl;
    double tlift = t0 + tl * LIFT_FRAC;

    static const int Ks[10] = {1, 1, 1, 2, 2, 2, 3, 3, 4, 5};
    static const int K2s[13] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12};
    static int cand[GMAX + 5];

    while (now() < tlift) {
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
        int ok = search(tlift, 20000, 3000, 6);
        if (ok && N_ > bestN) {
            int half = K_ * G_;
            free(bestA);
            bestA = malloc(sizeof(int) * (size_t)half * d_);
            for (int u = 0; u < half; u++)
                for (int l = 0; l < d_; l++)
                    bestA[u * d_ + l] = nb[(size_t)l * N_ + u] - half;
            bestN = N_;
            bestHalf = half;
            minN = N_ + 1;
        }
    }

    if (bestN == 0) { printf("0 0\n"); return 0; }

    BA = bestA;
    BB = malloc(sizeof(int) * (size_t)bestHalf * d_);
    build_B(bestHalf, d_, BA, BB);
    bgn = bestHalf;
    growth(tend, d_, D_);
    output_graph(bgn, d_, BA);
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

    # The C engine stops itself at `budget`; the subprocess timeout is a safety net.
    budget = max(0.5, time_limit - 3.0)
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), best_n + 1],
                        timeout=budget + 2.0)
        n, e = lib.parse_graph_text(out)
        if n > 0:
            consider(n, e)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
