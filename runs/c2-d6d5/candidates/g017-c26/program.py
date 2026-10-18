"""Lift search followed by vertex-pair insertion with edge-switch repair.

Phase 1 (C): the group-lift simulated annealing of the parent, run until a fraction of the
budget, keeping the largest valid lift found.

Phase 2 (C, new): take the valid d-regular bipartite graph and add one A-vertex x and one
B-vertex y. Pick d disjoint edges (a_i, b_i), replace each with (a_i, y) and (x, b_i). This
keeps the graph d-regular and bipartite and adds 2 vertices. Then anneal on the whole graph
with degree-preserving double-edge switches (a,b),(c,e) -> (a,e),(c,b), minimising the number
of ordered vertex pairs at distance > D (computed with bitset balls). If the cost reaches 0,
the larger graph is kept and insertion repeats. Otherwise the last valid graph is restored.
"""
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
#define NCAP 4000
#define WMAX (NCAP / 64 + 1)

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

/* ---------------- Phase 1: group-lift annealing ---------------- */

static int d_, D_, K_, G_, N_;
static int *MT = NULL, *RS = NULL;
static int *nb = NULL;
static u64 *rch = NULL, *tmpr = NULL;
static int lay[MAXD][MAXK], VS[MAXD][MAXK];
static int BL[MAXD][MAXK], BV[MAXD][MAXK];

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
            int l = rndi(d), i = rndi(k);
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

/* ---------------- Phase 2: vertex-pair insertion + edge-switch repair ---------------- */

static int P2adj[NCAP * MAXD];
static int P2side[NCAP];
static int SVadj[NCAP * MAXD];   /* last valid graph (best so far) */
static int SVside[NCAP];
static int SVN = 0;
static int stampA[NCAP], stampB[NCAP], stampc = 0;
static u64 R1[NCAP * WMAX], R2[NCAP * WMAX];
static int dfc[NCAP], dfcN[NCAP];

/* Ordered unreached pairs; fills per-vertex defect counts into dfout. */
static long long eval2(int N, int *dfout) {
    int d = d_, W = (N + 63) >> 6;
    u64 *A = R1, *B = R2;
    for (int v = 0; v < N; v++) {
        u64 *row = A + (size_t)v * WMAX;
        for (int w = 0; w < W; w++) row[w] = 0;
        row[v >> 6] |= 1ULL << (v & 63);
    }
    for (int t = 0; t < D_; t++) {
        for (int v = 0; v < N; v++) {
            u64 *dst = B + (size_t)v * WMAX;
            const u64 *src = A + (size_t)v * WMAX;
            for (int w = 0; w < W; w++) dst[w] = src[w];
            for (int l = 0; l < d; l++) {
                const u64 *s2 = A + (size_t)P2adj[v * d + l] * WMAX;
                for (int w = 0; w < W; w++) dst[w] |= s2[w];
            }
        }
        u64 *sw = A; A = B; B = sw;
    }
    long long tot = 0;
    for (int v = 0; v < N; v++) {
        const u64 *row = A + (size_t)v * WMAX;
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(row[w]);
        dfout[v] = N - c;
        tot += N - c;
    }
    return tot;
}

static int has_nb(int x, int y) {
    int d = d_;
    for (int l = 0; l < d; l++) if (P2adj[x * d + l] == y) return 1;
    return 0;
}

static int nb_idx(int x, int y) {
    int d = d_;
    for (int l = 0; l < d; l++) if (P2adj[x * d + l] == y) return l;
    return -1;
}

static int pick_side(int N, int s) {
    for (;;) {
        int v = rndi(N);
        if (P2side[v] == s) return v;
    }
}

/* Anneal with degree-preserving double-edge switches. Returns 0 when valid. */
static long long anneal2(int N, int iters, double tend) {
    int d = d_;
    long long cost = eval2(N, dfcN);
    memcpy(dfc, dfcN, sizeof(int) * (size_t)N);
    if (cost == 0) return 0;
    double T0 = 1.0 + 0.02 * (double)cost;
    for (int t = 0; t < iters; t++) {
        if ((t & 63) == 0 && now() > tend) break;
        double T = T0 * (1.0 - (double)t / iters) + 0.05;
        int a;
        if (rndu() < 0.5) {
            int start = rndi(N), v = -1;
            for (int q = 0; q < N; q++) {
                int w = (start + q) % N;
                if (dfc[w] > 0) { v = w; break; }
            }
            if (v < 0) break;
            if (P2side[v] == 0) a = v;
            else a = P2adj[v * d + rndi(d)];
        } else {
            a = pick_side(N, 0);
        }
        int la = rndi(d);
        int b = P2adj[a * d + la];
        int c = pick_side(N, 0);
        int lc = rndi(d);
        int e = P2adj[c * d + lc];
        if (c == a || e == b) continue;
        if (has_nb(a, e) || has_nb(c, b)) continue;
        int ib = nb_idx(b, a), ie = nb_idx(e, c);
        P2adj[a * d + la] = e;
        P2adj[c * d + lc] = b;
        P2adj[b * d + ib] = c;
        P2adj[e * d + ie] = a;
        long long c2 = eval2(N, dfcN);
        if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / T)) {
            cost = c2;
            memcpy(dfc, dfcN, sizeof(int) * (size_t)N);
            if (cost == 0) return 0;
        } else {
            P2adj[a * d + la] = b;
            P2adj[c * d + lc] = e;
            P2adj[b * d + ib] = a;
            P2adj[e * d + ie] = c;
        }
    }
    return cost;
}

/* Add one A-vertex N and one B-vertex N+1 by subdividing d disjoint edges. */
static int insert_pair(int N) {
    int d = d_;
    int x = N, y = N + 1;
    int pa[MAXD], pb[MAXD], pl[MAXD];
    int cnt = 0, tries = 0;
    stampc++;
    while (cnt < d && tries < 200000) {
        tries++;
        int a = rndi(N);
        if (P2side[a] != 0 || stampA[a] == stampc) continue;
        int l = rndi(d);
        int b = P2adj[a * d + l];
        if (stampB[b] == stampc) continue;
        stampA[a] = stampc;
        stampB[b] = stampc;
        pa[cnt] = a; pb[cnt] = b; pl[cnt] = l;
        cnt++;
    }
    if (cnt < d) return -1;
    P2side[x] = 0;
    P2side[y] = 1;
    for (int i = 0; i < d; i++) {
        int a = pa[i], b = pb[i], l = pl[i];
        int ib = nb_idx(b, a);
        P2adj[a * d + l] = y;
        P2adj[b * d + ib] = x;
        P2adj[x * d + i] = b;
        P2adj[y * d + i] = a;
    }
    return N + 2;
}

static void phase2(double tend) {
    int d = d_;
    int fails = 0;
    while (now() < tend) {
        int N = SVN;
        if (N + 2 > NCAP) break;
        int N2 = insert_pair(N);
        if (N2 < 0) { fails++; continue; }
        int iters = 20000 * (1 + fails);
        if (iters > 400000) iters = 400000;
        long long c = anneal2(N2, iters, tend);
        if (c == 0) {
            SVN = N2;
            memcpy(SVadj, P2adj, sizeof(int) * (size_t)N2 * d);
            memcpy(SVside, P2side, sizeof(int) * (size_t)N2);
            fails = 0;
        } else {
            memcpy(P2adj, SVadj, sizeof(int) * (size_t)N * d);
            fails++;
        }
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

    int d = d_;
    double t0 = now();
    double tend = t0 + tl;
    double tend1 = t0 + 0.45 * tl;
    static const int Ks[10] = {1, 1, 1, 2, 2, 2, 3, 3, 4, 5};
    static const int K2s[13] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12};
    static int cand[GMAX + 5];

    SVN = 0;
    while (now() < tend1) {
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
        if (2 * K_ * G_ > NCAP - 2) continue;
        alloc_state(2 * K_ * G_);
        int ok = search(tend1, 20000, 3000, 6);
        if (ok && N_ > SVN) {
            int N = N_, kG = K_ * G_;
            for (int v = 0; v < N; v++) {
                for (int l = 0; l < d; l++) SVadj[v * d + l] = nb[(size_t)l * N + v];
                SVside[v] = (v >= kG) ? 1 : 0;
            }
            SVN = N;
            minN = N_ + 1;
        }
    }

    if (SVN > 0) {
        memcpy(P2adj, SVadj, sizeof(int) * (size_t)SVN * d);
        memcpy(P2side, SVside, sizeof(int) * (size_t)SVN);
        phase2(tend);
    }

    if (SVN == 0) { printf("0 0\n"); return 0; }
    int N = SVN;
    int cnt = 0;
    for (int v = 0; v < N; v++)
        for (int l = 0; l < d; l++)
            if (v < SVadj[v * d + l]) cnt++;
    printf("%d %d\n", N, cnt);
    for (int v = 0; v < N; v++)
        for (int l = 0; l < d; l++) {
            int u = SVadj[v * d + l];
            if (v < u) printf("%d %d\n", v, u);
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

    budget = max(0.5, min(0.8 * time_limit, time_limit - 10.0))
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), best_n + 1],
                        timeout=budget + 5.0)
        n, e = lib.parse_graph_text(out)
        if n > 0:
            consider(n, e)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
