import math
import random
import time

import lib


# Engine A: bi-Cayley search over many finite groups. For a group G and a d-subset S,
# the bipartite double of Cay(G, S) has vertices A_g, B_h with A_g ~ B_{g s} for s in S.
# Left translations are automorphisms, so diameter <= D reduces to two BFS runs,
# from A_e and from B_e. Simulated annealing with iterated kicks searches S.
C_BICAYLEY = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

#define MAXD 16
#define MAXMM 1000

static u64 rs = 88172645463325252ULL;
static u64 rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int n) { return (int)(rnd64() % (u64)n); }
static double rndu(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
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

typedef struct { int M; int *mul; int *inv; } Group;

static int group_alloc(Group *g, int M) {
    g->M = M;
    g->mul = malloc(sizeof(int) * (size_t)M * (size_t)M);
    g->inv = malloc(sizeof(int) * (size_t)M);
    return g->mul && g->inv;
}
static void group_free(Group *g) {
    free(g->mul); free(g->inv);
    g->mul = NULL; g->inv = NULL; g->M = 0;
}

/* type 0: Z_m x| Z_k with (a,b)(c,e) = (a + r^b c, b + e), element a*k+b.
   type 1: Heisenberg group mod p, element (a*p+b)*p+c, (a,b,c)(a',b',c') = (a+a', b+b', c+c'+a b'). */
static int build_group(Group *g, int type, int a, int b, int c) {
    if (type == 0) {
        int m = a, k = b, r = c;
        if (m < 2 || k < 1) return 0;
        if (gcd_i(r, m) != 1 || powmod(r, k, m) != 1 % m) return 0;
        int M = m * k;
        if (M > MAXMM) return 0;
        if (!group_alloc(g, M)) return 0;
        int *pw = malloc(sizeof(int) * (size_t)k);
        pw[0] = 1 % m;
        for (int t = 1; t < k; t++) pw[t] = (int)((long long)pw[t - 1] * r % m);
        for (int x = 0; x < M; x++) {
            int a1 = x / k, b1 = x % k;
            for (int y = 0; y < M; y++) {
                int c1 = y / k, e1 = y % k;
                int aa = (int)((a1 + (long long)pw[b1] * c1) % m);
                g->mul[x * M + y] = aa * k + (b1 + e1) % k;
            }
        }
        free(pw);
    } else {
        int p = a;
        if (p < 2) return 0;
        int M = p * p * p;
        if (M > MAXMM) return 0;
        if (!group_alloc(g, M)) return 0;
        for (int x = 0; x < M; x++) {
            int a1 = x / (p * p), b1 = (x / p) % p, c1 = x % p;
            for (int y = 0; y < M; y++) {
                int a2 = y / (p * p), b2 = (y / p) % p, c2 = y % p;
                int aa = (a1 + a2) % p, bb = (b1 + b2) % p;
                int cc = (c1 + c2 + a1 * b2) % p;
                g->mul[x * M + y] = (aa * p + bb) * p + cc;
            }
        }
    }
    for (int x = 0; x < g->M; x++) {
        g->inv[x] = -1;
        for (int y = 0; y < g->M; y++)
            if (g->mul[x * g->M + y] == 0) { g->inv[x] = y; break; }
        if (g->inv[x] < 0) return 0;
    }
    return 1;
}

static int *seen = NULL;
static int stampv = 0;
static int *frA = NULL, *frB = NULL;

/* Number of vertices (of the 2M) reached from src within D steps. */
static int ball(const Group *G, const int *S, int d, int D, int src) {
    int M = G->M, N = 2 * M;
    if (stampv >= 0x3fffffff) { memset(seen, 0, sizeof(int) * (size_t)(2 * MAXMM)); stampv = 0; }
    stampv++;
    int *fr = frA, *nx = frB;
    int nf = 1, cnt = 1;
    fr[0] = src;
    seen[src] = stampv;
    (void)N;
    for (int lv = 0; lv < D && nf > 0; lv++) {
        int nn = 0;
        for (int i = 0; i < nf; i++) {
            int v = fr[i];
            if (v < M) {
                const int *row = G->mul + (size_t)v * M;
                for (int j = 0; j < d; j++) {
                    int w = M + row[S[j]];
                    if (seen[w] != stampv) { seen[w] = stampv; nx[nn++] = w; }
                }
            } else {
                int h = v - M;
                const int *row = G->mul + (size_t)h * M;
                for (int j = 0; j < d; j++) {
                    int w = row[G->inv[S[j]]];
                    if (seen[w] != stampv) { seen[w] = stampv; nx[nn++] = w; }
                }
            }
        }
        cnt += nn;
        int *t = fr; fr = nx; nx = t;
        nf = nn;
    }
    return cnt;
}

static int evalc(const Group *G, const int *S, int d, int D) {
    int N = 2 * G->M;
    int c1 = ball(G, S, d, D, 0);
    int c2 = ball(G, S, d, D, G->M);
    return (N - c1) + (N - c2);
}

static int in_set(const int *S, int cnt, int x) {
    for (int j = 0; j < cnt; j++) if (S[j] == x) return 1;
    return 0;
}

static int sa_group(const Group *G, int d, int D, double tend, int *outS) {
    int M = G->M;
    int S[MAXD], BS[MAXD];
    if (d > M) return 0;
    for (int j = 0; j < d; j++) {
        int x;
        do { x = rndi(M); } while (in_set(S, j, x));
        S[j] = x;
    }
    int cost = evalc(G, S, d, D);
    int bestc = cost;
    memcpy(BS, S, sizeof(int) * (size_t)d);
    if (cost == 0) { memcpy(outS, S, sizeof(int) * (size_t)d); return 1; }

    const long long L = 40000;
    const double T0 = 1.5, T1 = 0.1;
    long long it = 0;
    while (1) {
        if ((it & 255) == 0 && now() > tend) break;
        long long ph = it % L;
        if (it > 0 && ph == 0) {
            /* Iterated local search: restart the cycle from the best state with a small kick. */
            memcpy(S, BS, sizeof(int) * (size_t)d);
            int nk = 1 + rndi(2);
            for (int q = 0; q < nk; q++) {
                int j = rndi(d), x;
                do { x = rndi(M); } while (in_set(S, d, x));
                S[j] = x;
            }
            cost = evalc(G, S, d, D);
        }
        double T = T0 * pow(T1 / T0, (double)ph / (double)L);
        int j = rndi(d), x = rndi(M);
        it++;
        if (in_set(S, d, x)) continue;
        int old = S[j];
        S[j] = x;
        int c2 = evalc(G, S, d, D);
        if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / T)) {
            cost = c2;
            if (cost < bestc) { bestc = cost; memcpy(BS, S, sizeof(int) * (size_t)d); }
            if (cost == 0) { memcpy(outS, S, sizeof(int) * (size_t)d); return 1; }
        } else {
            S[j] = old;
        }
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 6) { printf("-1\n"); return 0; }
    int d = atoi(argv[1]), D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    int G = atoi(argv[5]);
    if (d < 1 || d > MAXD || D < 2 || G < 1 || argc < 6 + 4 * G) { printf("-1\n"); return 0; }
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd64();

    seen = calloc((size_t)(2 * MAXMM), sizeof(int));
    frA = malloc(sizeof(int) * (size_t)(2 * MAXMM));
    frB = malloc(sizeof(int) * (size_t)(2 * MAXMM));

    double tend = now() + tl;
    int bestIdx = -1, bestM = 0;
    int bestS[MAXD];
    for (int gi = 0; gi < G; gi++) {
        double remain = tend - now();
        if (remain <= 0) break;
        double slice = remain / (double)(G - gi);
        int type = atoi(argv[6 + 4 * gi]);
        int a = atoi(argv[7 + 4 * gi]);
        int b = atoi(argv[8 + 4 * gi]);
        int c = atoi(argv[9 + 4 * gi]);
        Group g;
        memset(&g, 0, sizeof g);
        if (!build_group(&g, type, a, b, c)) { group_free(&g); continue; }
        int S[MAXD];
        int ok = sa_group(&g, d, D, now() + slice, S);
        if (ok && g.M > bestM) {
            bestM = g.M;
            bestIdx = gi;
            memcpy(bestS, S, sizeof(int) * (size_t)d);
        }
        group_free(&g);
    }
    if (bestIdx < 0) { printf("-1\n"); return 0; }
    printf("%d", bestIdx);
    for (int j = 0; j < d; j++) printf(" %d", bestS[j]);
    printf("\n");
    return 0;
}
'''


# Engine B: the parent's voltage-lift annealer over semidirect groups, kept as a second stage.
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


RECORD_HINT = {(6, 5): 684}


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _heis_mul(p):
    """Multiplication for the Heisenberg group mod p, matching the C encoding."""
    def mul(x, y):
        a1, b1, c1 = x // (p * p), (x // p) % p, x % p
        a2, b2, c2 = y // (p * p), (y // p) % p, y % p
        return (((a1 + a2) % p) * p + (b1 + b2) % p) * p + (c1 + c2 + a1 * b2) % p
    return mul


def _candidate_groups(lo, hi, seed, cap):
    """Groups of order in [lo, hi]: Heisenberg groups mod p and semidirect products Z_m x| Z_k."""
    rng = random.Random(seed)
    cands = []
    for p in (2, 3, 5, 7, 11):
        M = p ** 3
        if lo <= M <= hi:
            cands.append((M, 1, p, 0, 0))
    for k in range(2, hi // 2 + 1):
        for m in range(max(2, lo // k), hi // k + 1):
            M = m * k
            if M < lo or M > hi:
                continue
            rs = [r for r in range(2, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
            for r in rng.sample(rs, min(2, len(rs))):
                cands.append((M, 0, m, k, r))
    rng.shuffle(cands)
    cands = cands[:cap]
    cands.sort()
    return cands


def _group_edges(M, mul, S):
    """Bipartite double of Cay(G, S): A_g = g, B_h = M + h, A_g ~ B_{g s}."""
    edges = []
    for g in range(M):
        for s in S:
            edges.append((g, M + mul(g, s)))
    return 2 * M, edges


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
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
    minN_parent = best_n + 1

    # Stage A: bi-Cayley search over group tables (a different construction family).
    tA = 0.5 * budget
    hint = RECORD_HINT.get((d, D))
    if hint:
        lo = hint // 2 + 1
    else:
        lo = max(2, (best_n + 1) // 2 + 1)
    hi = lo + 60
    groups = _candidate_groups(lo, hi, seed, cap=40)
    if groups:
        args = [d, D, seed, round(tA, 2), len(groups)]
        args += [x for g in groups for x in g[1:]]
        try:
            out = lib.run_c(C_BICAYLEY, args, timeout=tA + 5.0)
            tok = out.split()
            if len(tok) == 1 + d and tok[0] != "-1":
                gi = int(tok[0])
                S = [int(x) for x in tok[1:]]
                M, t, a, b, c = groups[gi]
                if t == 0:
                    mul = lib.semidirect_group(a, b, c)[1]
                else:
                    mul = _heis_mul(a)
                n, e = _group_edges(M, mul, S)
                consider(n, e)
        except Exception:
            pass

    # Stage B: the parent's voltage-lift annealer with the remaining time.
    remaining = budget - (time.monotonic() - t0)
    tB = max(0.5, remaining - 1.0)
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(tB, 2), minN_parent],
                        timeout=tB + 6.0)
        n, e = lib.parse_graph_text(out)
        if n > 0:
            consider(n, e)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
