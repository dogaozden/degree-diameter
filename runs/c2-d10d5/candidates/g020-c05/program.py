import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine A (new): single-block Haar / bi-Cayley search over metacyclic groups
# Z_m x|_r Z_k. Vertices A_x = x and B_y = G + y. Edge A_x ~ B_{x s} for s in S,
# |S| = DEG. Left multiplication is an automorphism, so the diameter test only
# needs BFS from A_1 and B_1. Cost = unreached vertices from both sources.
# Simulated annealing moves one element of S at a time.
# ----------------------------------------------------------------------------

C_HAAR = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define GMAX_HARD 300000
#define NCH 23
#define ITERS 4000
#define T0 3.0

static const int KCH[NCH] = {1,2,2,3,4,4,5,6,6,7,8,8,9,10,12,12,14,16,18,20,24,28,30};

static uint64_t rs;
static uint64_t rnd64(void) {
    uint64_t x = rs;
    x ^= x >> 12;
    x ^= x << 25;
    x ^= x >> 27;
    rs = x;
    return x * 2685821657736338717ULL;
}
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }

static int DEG, DIAM, M, K2, R, G, GMAXA;
static int64_t PWR[64];
static int *AA, *BB, *S, *Sinv, *bestS, *nbr, *mark, *qu;
static int stamp = 0;
static double TL, tstart;
static int timed_out = 0;

static double elapsed(void) { return (double)clock() / CLOCKS_PER_SEC - tstart; }

static int64_t powmod(int64_t b, int64_t e, int64_t m) {
    int64_t r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static int64_t gcd64(int64_t a, int64_t b) {
    while (b) {
        int64_t t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static void setup_group(void) {
    G = M * K2;
    for (int t = 0; t < K2; t++) PWR[t] = powmod(R, t, M);
    for (int x = 0; x < G; x++) {
        AA[x] = x / K2;
        BB[x] = x % K2;
    }
}

/* (a,b)(c,e) = (a + r^b c, b + e) */
static inline int gmul(int x, int y) {
    int bx = BB[x];
    int64_t a2 = (AA[x] + PWR[bx] * (int64_t)AA[y]) % M;
    int b2 = (bx + BB[y]) % K2;
    return (int)(a2 * K2 + b2);
}

/* inverse of (a,b) is (-r^{-b} a, -b) */
static inline int ginv(int x) {
    int b = BB[x];
    int nb = (K2 - b) % K2;
    int64_t a2 = (M - (PWR[nb] * (int64_t)AA[x]) % M) % M;
    return (int)(a2 * K2 + nb);
}

static int sample_group(long long lo, long long hi) {
    for (int att = 0; att < 300; att++) {
        int k2 = KCH[rndint(NCH)];
        long long mlo = (lo + k2 - 1) / k2, mhi = hi / k2;
        if (mlo < 2) mlo = 2;
        if (mhi < mlo) continue;
        long long m = mlo + (long long)rndint((int)(mhi - mlo + 1));
        long long r = 1;
        if (k2 >= 2 && m >= 3) {
            if (k2 % 2 == 0 && rnd01() < 0.3 && powmod(m - 1, k2, m) == 1 % m) {
                r = m - 1;
            } else {
                for (int tries = 0; tries < 400; tries++) {
                    long long c = 2 + rndint((int)(m - 2));
                    if (gcd64(c, m) == 1 && powmod(c, k2, m) == 1 % m) {
                        r = c;
                        break;
                    }
                }
            }
        }
        M = (int)m;
        K2 = k2;
        R = (int)r;
        setup_group();
        return 1;
    }
    return 0;
}

static void random_S(void) {
    for (int j = 0; j < DEG; j++) {
        int s;
        for (;;) {
            s = rndint(G);
            int dup = 0;
            for (int i = 0; i < j; i++)
                if (S[i] == s) { dup = 1; break; }
            if (!dup) break;
        }
        S[j] = s;
        Sinv[j] = ginv(s);
    }
}

static void set_column(int j) {
    int s = S[j], si = Sinv[j];
    for (int x = 0; x < G; x++) nbr[(size_t)x * DEG + j] = G + gmul(x, s);
    for (int y = 0; y < G; y++) nbr[(size_t)(G + y) * DEG + j] = gmul(y, si);
}

static int64_t bfs_unreached(int src) {
    int total = 2 * G;
    if (++stamp == 2000000000) {
        memset(mark, 0, sizeof(int) * (size_t)(2 * GMAXA));
        stamp = 1;
    }
    int head = 0, tail = 0;
    qu[tail++] = src;
    mark[src] = stamp;
    for (int depth = 0; depth < DIAM && head < tail && tail < total; depth++) {
        int end = tail;
        while (head < end) {
            const int *row = nbr + (size_t)qu[head++] * DEG;
            for (int j = 0; j < DEG; j++) {
                int u = row[j];
                if (mark[u] != stamp) {
                    mark[u] = stamp;
                    qu[tail++] = u;
                }
            }
        }
    }
    return total - tail;
}

static int64_t eval_cost(void) { return bfs_unreached(0) + bfs_unreached(G); }

static int64_t anneal(int iters, double t0) {
    int64_t cost = eval_cost();
    int64_t bestc = cost;
    memcpy(bestS, S, sizeof(int) * (size_t)DEG);
    for (int t = 0; t < iters && cost > 0; t++) {
        if ((t & 15) == 0 && elapsed() > TL) {
            timed_out = 1;
            break;
        }
        double temp = t0 * (1.0 - (double)t / iters) + 0.05;
        int j = rndint(DEG);
        int s = rndint(G);
        int dup = 0;
        for (int i = 0; i < DEG; i++)
            if (S[i] == s) { dup = 1; break; }
        if (dup) continue;
        int old = S[j], oldi = Sinv[j];
        S[j] = s;
        Sinv[j] = ginv(s);
        set_column(j);
        int64_t c2 = eval_cost();
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
            if (cost < bestc) {
                bestc = cost;
                memcpy(bestS, S, sizeof(int) * (size_t)DEG);
            }
        } else {
            S[j] = old;
            Sinv[j] = oldi;
            set_column(j);
        }
    }
    return bestc;
}

int main(int argc, char **argv) {
    if (argc < 7) {
        fprintf(stderr, "usage: d D best_n cap seed time\n");
        return 1;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    long long best_n = atoll(argv[3]);
    long long cap = atoll(argv[4]);
    unsigned long long seed = strtoull(argv[5], NULL, 10);
    TL = atof(argv[6]);
    tstart = (double)clock() / CLOCKS_PER_SEC;

    rs = (seed + 1) * 0x9E3779B97F4A7C15ULL ^ 0x8E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 8; i++) rnd64();

    if (DEG < 3 || DEG > 200 || DIAM < 3) {
        printf("0 0\n");
        return 0;
    }
    long long half_cap = cap / 2;
    long long gmax = half_cap < GMAX_HARD ? half_cap : GMAX_HARD;
    long long found = best_n / 2;
    if (gmax <= found + DEG + 1) {
        printf("0 0\n");
        return 0;
    }
    GMAXA = (int)gmax;
    AA = malloc(sizeof(int) * (size_t)GMAXA);
    BB = malloc(sizeof(int) * (size_t)GMAXA);
    S = malloc(sizeof(int) * (size_t)DEG);
    Sinv = malloc(sizeof(int) * (size_t)DEG);
    bestS = malloc(sizeof(int) * (size_t)DEG);
    nbr = malloc(sizeof(int) * (size_t)2 * GMAXA * DEG);
    mark = calloc((size_t)2 * GMAXA, sizeof(int));
    qu = malloc(sizeof(int) * (size_t)2 * GMAXA);
    if (!AA || !BB || !S || !Sinv || !bestS || !nbr || !mark || !qu) {
        printf("0 0\n");
        return 0;
    }

    int have = 0, bestM = 0, bestK = 0, bestR = 0;
    while (elapsed() < TL) {
        if (found >= gmax) break;
        long long span = found / 25;
        if (span < 3) span = 3;
        long long lo = found + 1, hi = found + span;
        if (hi > gmax) hi = gmax;
        if (!sample_group(lo, hi) && !sample_group(lo, gmax)) break;
        if (G < DEG + 1) continue;
        random_S();
        for (int j = 0; j < DEG; j++) set_column(j);
        int64_t c = anneal(ITERS, T0);
        if (c == 0) {
            have = 1;
            found = G;
            bestM = M;
            bestK = K2;
            bestR = R;
        }
        if (timed_out) break;
    }

    if (!have) {
        printf("0 0\n");
        return 0;
    }
    M = bestM;
    K2 = bestK;
    R = bestR;
    setup_group();
    for (int j = 0; j < DEG; j++) {
        S[j] = bestS[j];
        Sinv[j] = ginv(S[j]);
    }
    printf("%lld %lld\n", 2LL * G, (long long)G * DEG);
    for (int x = 0; x < G; x++)
        for (int j = 0; j < DEG; j++)
            printf("%d %d\n", x, G + gmul(x, S[j]));
    return 0;
}
"""


# ----------------------------------------------------------------------------
# C engine B (previous parent): bi-Cayley voltage annealing over Z_m x| Z_k2
# with iterated local search. Kept as the second stage.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXK 4
#define NCHOICE 20
#define PEN 1000

static uint64_t rs;
static uint64_t rnd64(void) {
    uint64_t x = rs;
    x ^= x >> 12;
    x ^= x << 25;
    x ^= x >> 27;
    rs = x;
    return x * 2685821657736338717ULL;
}
static double rnd01(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}
static int rndint(int n) {
    return (int)(rnd64() % (uint64_t)n);
}

static const int K2_CHOICES[NCHOICE] = {1,1,2,2,3,4,5,6,7,8,9,10,12,14,16,18,20,24,30,36};

static int DEG, DIAM, CAP;
static int K, K2, M, R, G, N;
static int64_t PWR[64];
static int *AA, *BB;
static int *nbr, *lay, *vol;
static int *snapL, *snapV;
static int64_t GBEST;
static uint8_t *cur, *scr, *tmpb;
static uint8_t POP[256];
static uint8_t FULL;
static int timed_out;
static double tstart;
static double TL;
static int *bestnbr;
static int best_stride, best_K, best_G;
static int have_best;
static int64_t LASTCOST;

static double elapsed(void) {
    return (double)clock() / CLOCKS_PER_SEC - tstart;
}

static int64_t powmod(int64_t b, int64_t e, int64_t m) {
    int64_t r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static int64_t gcd64(int64_t a, int64_t b) {
    while (b) {
        int64_t t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static int sample_group(int64_t target) {
    for (int attempt = 0; attempt < 200; attempt++) {
        int k2 = K2_CHOICES[rndint(NCHOICE)];
        int64_t m = (target + k2 - 1) / k2;
        if (m < 2) m = 2;
        int64_t r = -1;
        if (k2 == 1) {
            r = 1;
        } else if (k2 == 2 && rnd01() < 0.3) {
            r = m - 1;
            if (powmod(r, 2, m) != 1 % m) continue;
        } else {
            for (int tries = 0; tries < 60; tries++) {
                int64_t c = (m > 2) ? 2 + rndint((int)(m - 2)) : 1;
                if (gcd64(c, m) == 1 && powmod(c, k2, m) == 1 % m) {
                    r = c;
                    break;
                }
            }
            if (r < 0) continue;
        }
        M = (int)m;
        K2 = k2;
        R = (int)r;
        G = M * K2;
        return 1;
    }
    return 0;
}

static void setup_group(void) {
    for (int t = 0; t < K2; t++) PWR[t] = powmod(R, t, M);
    for (int x = 0; x < G; x++) {
        AA[x] = x / K2;
        BB[x] = x % K2;
    }
}

/* (a,b)(c,e) = (a + r^b c, b + e) */
static inline int gmul(int x, int y) {
    int bx = BB[x];
    int64_t a2 = (AA[x] + PWR[bx] * (int64_t)AA[y]) % M;
    int b2 = (bx + BB[y]) % K2;
    return (int)(a2 * K2 + b2);
}

/* inverse of (a,b) is (-r^{-b} a, -b) */
static inline int ginv(int x) {
    int b = BB[x];
    int nb = (K2 - b) % K2;
    int64_t a2 = (M - (PWR[nb] * (int64_t)AA[x]) % M) % M;
    return (int)(a2 * K2 + nb);
}

static void set_dart(int l, int i, int p, int s) {
    int is = ginv(s);
    int *row = nbr + (size_t)l * N;
    int Ab = i * G, Bb = (K + p) * G;
    for (int g = 0; g < G; g++) {
        row[Ab + g] = Bb + gmul(g, s);
        row[Bb + g] = Ab + gmul(g, is);
    }
}

static void compute_reach(uint8_t *out) {
    memset(out, 0, (size_t)N);
    for (int b = 0; b < 2 * K; b++) out[b * G] = (uint8_t)(1u << b);
    for (int t = 0; t < DIAM; t++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint8_t x = out[v];
            for (int l = 0; l < DEG; l++) x |= out[nbr[(size_t)l * N + v]];
            tmpb[v] = x;
            if (x != out[v]) changed = 1;
        }
        if (!changed) break;
        memcpy(out, tmpb, (size_t)N);
    }
}

static int64_t unreached(const uint8_t *r) {
    int64_t s = 0;
    for (int v = 0; v < N; v++) s += POP[r[v]];
    return (int64_t)2 * K * N - s;
}

static int dupcount(void) {
    int n = DEG * K, dup = 0;
    for (int e = 0; e < n; e++) {
        int i = e % K;
        for (int f = i; f < e; f += K) {
            if (lay[f] == lay[e] && vol[f] == vol[e]) {
                dup++;
                break;
            }
        }
    }
    return dup;
}

static int64_t total_cost(const uint8_t *r) {
    return unreached(r) + (int64_t)PEN * dupcount();
}

static void save_snap(int64_t cost) {
    int n = DEG * K;
    for (int e = 0; e < n; e++) {
        snapL[e] = lay[e];
        snapV[e] = vol[e];
    }
    GBEST = cost;
}

static void restore_kick(int nk) {
    int n = DEG * K;
    for (int e = 0; e < n; e++) {
        lay[e] = snapL[e];
        vol[e] = snapV[e];
    }
    for (int j = 0; j < nk; j++) vol[rndint(n)] = rndint(G);
}

static int run_trial(int iters, int patience, int reinit) {
    int n = DEG * K;
    timed_out = 0;
    if (reinit) {
        for (int l = 0; l < DEG; l++) {
            int perm[MAXK];
            for (int i = 0; i < K; i++) perm[i] = i;
            for (int i = K - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int t = perm[i];
                perm[i] = perm[j];
                perm[j] = t;
            }
            for (int i = 0; i < K; i++) lay[l * K + i] = perm[i];
        }
        for (int e = 0; e < n; e++) vol[e] = rndint(G);
    }
    for (int l = 0; l < DEG; l++)
        for (int i = 0; i < K; i++)
            set_dart(l, i, lay[l * K + i], vol[l * K + i]);

    compute_reach(cur);
    int64_t cost = total_cost(cur);
    if (reinit) GBEST = INT64_MAX;
    if (cost < GBEST) save_snap(cost);
    double c0 = cost > 1 ? (double)cost : 1.0;
    int64_t best_cost = cost;
    int last = 0;

    for (int t = 0; t < iters && cost != 0; t++) {
        if (t - last > patience) break;
        if ((t & 31) == 0 && elapsed() > TL) {
            timed_out = 1;
            break;
        }
        double temp = 0.01 * c0 * (1.0 - (double)t / iters);
        if (temp < 0.5) temp = 0.5;
        int64_t c2 = 0;

        if (K >= 2 && rnd01() < 0.25) {
            int l = rndint(DEG);
            int i1 = rndint(K);
            int i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            int e1 = l * K + i1, e2 = l * K + i2;
            int tp = lay[e1];
            lay[e1] = lay[e2];
            lay[e2] = tp;
            set_dart(l, i1, lay[e1], vol[e1]);
            set_dart(l, i2, lay[e2], vol[e2]);
            compute_reach(scr);
            c2 = total_cost(scr);
            if (!(c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp))) {
                tp = lay[e1];
                lay[e1] = lay[e2];
                lay[e2] = tp;
                set_dart(l, i1, lay[e1], vol[e1]);
                set_dart(l, i2, lay[e2], vol[e2]);
                continue;
            }
        } else {
            int l = 0, i = 0, u = -1;
            if (rnd01() < 0.4) {
                int cnt = 0;
                for (int v = 0; v < N; v++) {
                    if (cur[v] != FULL) {
                        cnt++;
                        if (rndint(cnt) == 0) u = v;
                    }
                }
            }
            if (u >= 0) {
                int block = u / G;
                l = rndint(DEG);
                i = -1;
                if (block < K) {
                    i = block;
                } else {
                    for (int j = 0; j < K; j++) {
                        if (lay[l * K + j] == block - K) {
                            i = j;
                            break;
                        }
                    }
                }
                if (i < 0) continue;
            } else {
                l = rndint(DEG);
                i = rndint(K);
            }
            int e = l * K + i;
            int old = vol[e];
            int nw = rndint(G);
            if (nw == old) continue;
            vol[e] = nw;
            set_dart(l, i, lay[e], nw);
            compute_reach(scr);
            c2 = total_cost(scr);
            if (!(c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp))) {
                vol[e] = old;
                set_dart(l, i, lay[e], old);
                continue;
            }
        }

        uint8_t *tb = cur;
        cur = scr;
        scr = tb;
        cost = c2;
        if (cost < GBEST) save_snap(cost);
        if (cost < best_cost) {
            best_cost = cost;
            last = t;
        }
    }
    LASTCOST = cost;
    return cost == 0;
}

static int pick_k(const double *tr, const double *wn) {
    if (rnd01() < 0.2) return 1 + rndint(MAXK);
    int bk = 1;
    double bv = -1.0;
    for (int k = 1; k <= MAXK; k++) {
        double v = (wn[k] + 1.0) / (tr[k] + 2.0) + 0.02 * rnd01();
        if (v > bv) {
            bv = v;
            bk = k;
        }
    }
    return bk;
}

int main(int argc, char **argv) {
    if (argc < 7) {
        fprintf(stderr, "usage: d D target cap seed time\n");
        return 1;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    long long best0 = atoll(argv[3]);
    CAP = atoi(argv[4]);
    unsigned long long seed = strtoull(argv[5], NULL, 10);
    TL = atof(argv[6]);
    tstart = (double)clock() / CLOCKS_PER_SEC;

    rs = (seed + 1) * 0x9E3779B97F4A7C15ULL ^ 0xD1B54A32D192ED03ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 8; i++) rnd64();
    for (int x = 0; x < 256; x++) {
        int c = 0;
        for (int y = x; y; y >>= 1) c += y & 1;
        POP[x] = (uint8_t)c;
    }

    if (DEG < 3 || DIAM < 3 || CAP < 8) {
        printf("0 0\n");
        return 0;
    }

    AA = malloc(sizeof(int) * (size_t)(CAP + 1));
    BB = malloc(sizeof(int) * (size_t)(CAP + 1));
    nbr = malloc(sizeof(int) * (size_t)DEG * CAP);
    lay = malloc(sizeof(int) * (size_t)DEG * MAXK);
    vol = malloc(sizeof(int) * (size_t)DEG * MAXK);
    snapL = malloc(sizeof(int) * (size_t)DEG * MAXK);
    snapV = malloc(sizeof(int) * (size_t)DEG * MAXK);
    cur = malloc((size_t)CAP);
    scr = malloc((size_t)CAP);
    tmpb = malloc((size_t)CAP);
    bestnbr = malloc(sizeof(int) * (size_t)DEG * CAP);
    if (!AA || !BB || !nbr || !lay || !vol || !snapL || !snapV || !cur || !scr || !tmpb || !bestnbr) {
        printf("0 0\n");
        return 0;
    }

    double tr[MAXK + 1] = {0}, wn[MAXK + 1] = {0};
    long long found = best0;

    while (elapsed() < TL) {
        if (found >= CAP) break;
        int k = pick_k(tr, wn);
        int64_t base = found / (2 * k);
        int64_t span = base / 8 + 1;
        if (span < 2) span = 2;
        int64_t target = base + 1 + rndint((int)span);
        if (target < 2) target = 2;
        if (!sample_group(target)) continue;
        long long Nn = 2LL * k * G;
        if (Nn <= found || Nn > CAP) continue;

        K = k;
        N = (int)Nn;
        FULL = (uint8_t)((1u << (2 * K)) - 1);
        setup_group();
        tr[k] += 1.0;
        int ok = run_trial(4000, 1200, 1);
        int extra = 0;
        while (!ok && !timed_out && extra < 6 && GBEST <= (int64_t)N / 4 && elapsed() < TL) {
            restore_kick(1 + rndint(3));
            ok = run_trial(6000, 1500, 0);
            extra++;
        }
        if (ok) {
            wn[k] += 1.0;
            found = N;
            memcpy(bestnbr, nbr, sizeof(int) * (size_t)DEG * N);
            best_stride = N;
            best_K = K;
            best_G = G;
            have_best = 1;
        }
        if (timed_out) break;
    }

    if (!have_best) {
        printf("0 0\n");
        return 0;
    }
    int KG = best_K * best_G;
    long long m = (long long)KG * DEG;
    printf("%d %lld\n", best_stride, m);
    for (int u = 0; u < KG; u++)
        for (int l = 0; l < DEG; l++)
            printf("%d %d\n", u, bestnbr[(size_t)l * best_stride + u]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact baselines.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Slack extension: add vertices using spare degree; only valid graphs are kept.
# ----------------------------------------------------------------------------

def _bipartition(n, adj):
    """Return the 2-colouring of the graph, or None if it is not bipartite."""
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
    return color


def _slack_extend(n, edges, d, D, rng, deadline):
    """Greedily add new vertices using spare degree; returns (n, edges), always valid."""
    edges = [tuple(e) for e in edges]
    adj = lib.adjacency(n, edges)
    color = _bipartition(n, adj)
    if color is None:
        return n, edges
    deg = [len(a) for a in adj]
    grew = True
    while grew and time.monotonic() < deadline:
        grew = False
        for side in (0, 1):
            spare = [v for v in range(n) if color[v] == side and deg[v] < d]
            if len(spare) < d:
                continue
            for _ in range(30):
                if time.monotonic() > deadline or len(spare) < d:
                    break
                pick = rng.sample(spare, d)
                w = n
                cand = edges + [(v, w) for v in pick]
                if lib.is_valid(n + 1, cand, d, D):
                    edges = cand
                    n += 1
                    color.append(1 - side)
                    deg.append(d)
                    for v in pick:
                        deg[v] += 1
                    spare = [v for v in spare if deg[v] < d]
                    grew = True
                    break
    return n, edges


# ----------------------------------------------------------------------------
# C stage runners.
# ----------------------------------------------------------------------------

def _run_haar(d, D, best_n, cap, seed, seconds):
    text = lib.run_c(C_HAAR, [d, D, best_n, cap, int(seed) & 0x7FFFFFFF, round(seconds, 2)],
                     timeout=seconds + 20.0)
    return lib.parse_graph_text(text)


def _run_parent(d, D, best_n, cap, seed, seconds):
    text = lib.run_c(C_SOURCE, [d, D, best_n, cap, int(seed) & 0x7FFFFFFF, round(seconds, 2)],
                     timeout=seconds + 20.0)
    return lib.parse_graph_text(text)


# ----------------------------------------------------------------------------
# Main build: exact constructions, then Haar Cayley search, then the voltage
# engine seeded with the best order so far, then slack extension.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    final_deadline = start + max(1.0, time_limit - 3.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
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
                return best

    if D >= 4 and time.monotonic() < start + budget:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    if d >= 3 and D >= 3:
        cap = int(min(lib.moore_bound(d, D), 10 ** 9))

        # Stage 1: single-block Cayley (Haar) search over metacyclic groups.
        remaining = start + budget - time.monotonic()
        if remaining > 2.0:
            try:
                n2, e2 = _run_haar(d, D, best_n, cap, seed, 0.55 * remaining)
                consider(n2, e2)
            except Exception:
                pass

        # Stage 2: multi-block voltage engine, seeded with the best order so far.
        remaining = start + budget - time.monotonic()
        if remaining > 2.0:
            try:
                pcap = int(min(cap, 10 ** 6))
                n2, e2 = _run_parent(d, D, best_n, pcap, seed, 0.8 * remaining)
                consider(n2, e2)
            except Exception:
                pass

    # Stage 3: use any spare degree in the best graph to add vertices.
    if time.monotonic() < final_deadline:
        n2, e2 = _slack_extend(best[0], best[1], d, D, rng, final_deadline)
        consider(n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
