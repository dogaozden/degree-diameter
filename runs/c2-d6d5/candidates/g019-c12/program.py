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
#define MAXH 1024
#define MAXE (MAXH * MAXD + 64)
#define MAXNN (2 * MAXH)
#define MAXW ((MAXNN + 63) / 64)

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

/* ---------------- Phase 1: group-lift search (Z_m x| Z_k2 voltage lifts) ---------------- */

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

static void lift_search(double tend, int minN) {
    static int cand[GMAX + 5];
    static const int Ks[10] = {1, 1, 1, 2, 2, 2, 3, 3, 4, 5};
    static const int K2s[13] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12};
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
}

/* ---------------- Phase 2: vertex insertion + edge-switch annealing ---------------- */
/* Bipartite graph: A vertices 0..h-1, B vertices 0..h-1 (global id h+b).
   Every vertex has degree d_ (regular). Cost = unordered pairs at distance > D_. */

static int ea[MAXE], eb[MAXE], M2, H2;
static int sea[MAXE], seb[MAXE], sM, sH;
static unsigned char adjm[MAXH * MAXH];
static u64 bufA[MAXNN * MAXW], bufB[MAXNN * MAXW];
static unsigned char usedA[MAXH], usedB[MAXH];

static void p2_rebuild(void) {
    memset(adjm, 0, sizeof adjm);
    for (int e = 0; e < M2; e++) adjm[ea[e] * MAXH + eb[e]] = 1;
}

static long long p2_cost(void) {
    int h = H2, N = 2 * h, W = (N + 63) >> 6;
    u64 *cur = bufA, *nxt = bufB;
    memset(cur, 0, sizeof(u64) * (size_t)N * W);
    for (int v = 0; v < N; v++) cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int t = 0; t < D_; t++) {
        memcpy(nxt, cur, sizeof(u64) * (size_t)N * W);
        for (int e = 0; e < M2; e++) {
            u64 *ra = nxt + (size_t)ea[e] * W;
            u64 *rb = nxt + (size_t)(h + eb[e]) * W;
            const u64 *ca = cur + (size_t)ea[e] * W;
            const u64 *cb = cur + (size_t)(h + eb[e]) * W;
            for (int w = 0; w < W; w++) { ra[w] |= cb[w]; rb[w] |= ca[w]; }
        }
        u64 *tp = cur; cur = nxt; nxt = tp;
    }
    long long cnt = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(cur[(size_t)v * W + w]);
        cnt += N - c;
    }
    return cnt / 2;
}

/* Insert one A vertex h and one B vertex h. Pick d edges with pairwise distinct
   endpoints (a_i, b_i); replace each by (h, b_i) and add (a_i, h). */
static int p2_grow(void) {
    int h = H2, d = D_;
    if (h + 1 >= MAXH) return 0;
    if (M2 + d > MAXE) return 0;
    memset(usedA, 0, sizeof usedA);
    memset(usedB, 0, sizeof usedB);
    int chosen[MAXD], nc = 0;
    for (int tr = 0; tr < 200000 && nc < d; tr++) {
        int e = rndi(M2);
        int a = ea[e], b = eb[e];
        if (usedA[a] || usedB[b]) continue;
        usedA[a] = 1; usedB[b] = 1;
        chosen[nc++] = e;
    }
    if (nc < d) return 0;
    for (int c = 0; c < nc; c++) {
        int e = chosen[c];
        int ai = ea[e], bi = eb[e];
        adjm[ai * MAXH + bi] = 0;
        ea[e] = h; eb[e] = bi;
        adjm[h * MAXH + bi] = 1;
        ea[M2] = ai; eb[M2] = h; M2++;
        adjm[ai * MAXH + h] = 1;
    }
    H2 = h + 1;
    return 1;
}

static void p2_save(void) {
    sH = H2; sM = M2;
    memcpy(sea, ea, sizeof(int) * (size_t)M2);
    memcpy(seb, eb, sizeof(int) * (size_t)M2);
}

static void p2_load_saved(void) {
    H2 = sH; M2 = sM;
    memcpy(ea, sea, sizeof(int) * (size_t)M2);
    memcpy(eb, seb, sizeof(int) * (size_t)M2);
    p2_rebuild();
}

static void augment(double tend) {
    long long cur = p2_cost();
    if (cur != 0) return;
    p2_save();
    const int STEPS = 4000;
    while (now() < tend) {
        p2_load_saved();
        if (!p2_grow()) break;
        cur = p2_cost();
        for (int st = 0; st < STEPS && cur > 0; st++) {
            if ((st & 127) == 0 && now() > tend) break;
            double T = 0.3 + 0.9 * (1.0 - (double)st / STEPS);
            int i = rndi(M2), j = rndi(M2);
            if (i == j) continue;
            int a1 = ea[i], b1 = eb[i], a2 = ea[j], b2 = eb[j];
            if (a1 == a2 || b1 == b2) continue;
            if (adjm[a1 * MAXH + b2] || adjm[a2 * MAXH + b1]) continue;
            adjm[a1 * MAXH + b1] = 0; adjm[a2 * MAXH + b2] = 0;
            adjm[a1 * MAXH + b2] = 1; adjm[a2 * MAXH + b1] = 1;
            ea[i] = a1; eb[i] = b2; ea[j] = a2; eb[j] = b1;
            long long c2 = p2_cost();
            if (c2 <= cur || rndu() < exp(-(double)(c2 - cur) / T)) {
                cur = c2;
            } else {
                adjm[a1 * MAXH + b2] = 0; adjm[a2 * MAXH + b1] = 0;
                adjm[a1 * MAXH + b1] = 1; adjm[a2 * MAXH + b2] = 1;
                ea[i] = a1; eb[i] = b1; ea[j] = a2; eb[j] = b2;
            }
        }
        if (cur == 0) p2_save();
    }
}

/* ---------------- main ---------------- */

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

    /* Phase 1: voltage-lift search gives a regular valid starting graph. */
    lift_search(t0 + 0.5 * tl, minN);

    /* Phase 2: grow that graph by vertex pairs and repair by edge switches. */
    if (bestN > 0 && bestN / 2 < MAXH - 2) {
        int h = bestN / 2, ok = 1;
        M2 = 0;
        for (int p = 0; p < bEc && ok; p++) {
            int u = bE[2 * p], v = bE[2 * p + 1];
            if (u > v) { int t = u; u = v; v = t; }
            if (!(u < h && v >= h) || M2 >= MAXE) ok = 0;
            else { ea[M2] = u; eb[M2] = v - h; M2++; }
        }
        if (ok) {
            H2 = h;
            p2_rebuild();
            augment(tend);
            if (sH > h) {
                int *ne = malloc(sizeof(int) * 2 * (size_t)sM);
                for (int p = 0; p < sM; p++) {
                    ne[2 * p] = sea[p];
                    ne[2 * p + 1] = sH + seb[p];
                }
                free(bE);
                bE = ne;
                bEc = sM;
                bestN = 2 * sH;
            }
        }
    }

    if (bestN == 0) { printf("0 0\n"); return 0; }
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

    # Use almost the whole limit; the C engine stops itself at `budget`.
    budget = max(0.5, time_limit - 6.0)
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), best_n + 1],
                        timeout=budget + 3.0)
        n, e = lib.parse_graph_text(out)
        if n > 0:
            consider(n, e)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
