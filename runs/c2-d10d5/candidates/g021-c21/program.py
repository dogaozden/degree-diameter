import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# NEW ENGINE: bi-Cayley graphs over non-abelian groups Z_m x| Z_k.
#
# Graph: vertices (g,0) and (g,1) for g in G, |G| = N, with (g,0) ~ (g*s,1)
# for s in S, |S| = DEG. Left multiplication is an automorphism, so the
# diameter check needs only two BFS runs: one from (e,0) and one from (e,1).
# Cost = unreached pairs needed for diameter <= DIAM. Simulated annealing
# changes one connection element at a time. Cost 0 gives a valid
# DEG-regular bipartite graph on 2N vertices.
# The group is non-abelian so that products of generators rarely collide.
# This is a different family from the block voltage lifts of the old engine.
# ----------------------------------------------------------------------------

BICAY_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

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

static int DEG, DIAM, CAP;
static double TL, tstart;
static int N, M, K2, R;
static int *AA, *BB, *PW;
static int *S, *SI, *RT, *RI;
static int *stamp, *qn;
static unsigned char *qd;
static int epoch;
static int *bestRT;
static int bestN, have_best;
static int timed_out;

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

/* element x = a*K2 + b, (a,b)(c,e) = (a + r^b c, b + e) */
static inline int gmul(int x, int y) {
    int bx = BB[x];
    int64_t a2 = (AA[x] + (int64_t)PW[bx] * AA[y]) % M;
    int b2 = (bx + BB[y]) % K2;
    return (int)(a2 * K2 + b2);
}

/* inverse of (a,b) is (-r^{-b} a, -b) */
static inline int ginv(int x) {
    int b = BB[x];
    int nb = (K2 - b) % K2;
    int64_t t = ((int64_t)PW[nb] * AA[x]) % M;
    int64_t a2 = (M - t) % M;
    return (int)(a2 * K2 + nb);
}

static void init_group(int m, int k, int r) {
    M = m;
    K2 = k;
    R = r;
    N = m * k;
    for (int t = 0; t < K2; t++) PW[t] = (int)powmod(R, t, M);
    for (int x = 0; x < N; x++) {
        AA[x] = x / K2;
        BB[x] = x % K2;
    }
}

/* Pick a random semidirect group Z_m x| Z_k of order n with r != 1, r^k = 1 mod m. */
static int choose_group(int n) {
    int divs[512];
    int nd = 0;
    for (int k = 2; k <= n / 3 && nd < 512; k++)
        if (n % k == 0) divs[nd++] = k;
    if (nd == 0) return 0;
    for (int tries = 0; tries < 60; tries++) {
        int k = divs[rndint(nd)];
        int m = n / k;
        int cnt = 0, pick = -1;
        for (int r = 2; r < m; r++) {
            if (gcd64(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            cnt++;
            if (rndint(cnt) == 0) pick = r;
        }
        if (pick >= 0) {
            init_group(m, k, pick);
            return 1;
        }
    }
    return 0;
}

static void set_gen(int j, int s) {
    S[j] = s;
    SI[j] = ginv(s);
    for (int g = 0; g < N; g++) {
        RT[j * N + g] = gmul(g, s);
        RI[j * N + g] = gmul(g, SI[j]);
    }
}

static int fresh_gen(int j) {
    (void)j;
    for (;;) {
        int s = 1 + rndint(N - 1);
        int ok = 1;
        for (int i = 0; i < DEG; i++) {
            if (S[i] == s) {
                ok = 0;
                break;
            }
        }
        if (ok) return s;
    }
}

/* BFS from node start (side 0: id < N, side 1: id = N + elem), depth <= DIAM. */
static void bfs_counts(int start, int *c0, int *c1) {
    if (++epoch == 0x7ffffff0) {
        memset(stamp, 0, sizeof(int) * (size_t)(2 * N));
        epoch = 1;
    }
    int head = 0, tail = 0, n0 = 0, n1 = 0;
    stamp[start] = epoch;
    qn[tail] = start;
    qd[tail] = 0;
    tail++;
    while (head < tail) {
        int u = qn[head];
        int du = qd[head];
        head++;
        if (u < N) n0++;
        else n1++;
        if (du >= DIAM) continue;
        if (u < N) {
            for (int j = 0; j < DEG; j++) {
                int v = N + RT[j * N + u];
                if (stamp[v] != epoch) {
                    stamp[v] = epoch;
                    qn[tail] = v;
                    qd[tail] = (unsigned char)(du + 1);
                    tail++;
                }
            }
        } else {
            int h = u - N;
            for (int j = 0; j < DEG; j++) {
                int v = RI[j * N + h];
                if (stamp[v] != epoch) {
                    stamp[v] = epoch;
                    qn[tail] = v;
                    qd[tail] = (unsigned char)(du + 1);
                    tail++;
                }
            }
        }
    }
    *c0 = n0;
    *c1 = n1;
}

/* Unreached pairs: (e,0) must reach all of side 0 and side 1; (e,1) must reach all of side 1. */
static int64_t evaluate(void) {
    int a0, a1, b0, b1;
    bfs_counts(0, &a0, &a1);
    bfs_counts(N, &b0, &b1);
    (void)b0;
    return (int64_t)(N - a0) + (int64_t)(N - a1) + (int64_t)(N - b1);
}

static int anneal(int iters) {
    for (int j = 0; j < DEG; j++) {
        int s;
        for (;;) {
            s = 1 + rndint(N - 1);
            int dup = 0;
            for (int i = 0; i < j; i++)
                if (S[i] == s) dup = 1;
            if (!dup) break;
        }
        set_gen(j, s);
    }
    int64_t c = evaluate();
    for (int t = 0; t < iters && c > 0; t++) {
        if ((t & 63) == 0 && elapsed() > TL) {
            timed_out = 1;
            return 0;
        }
        int j = rndint(DEG);
        int old = S[j];
        int nw = fresh_gen(j);
        set_gen(j, nw);
        int64_t c2 = evaluate();
        double temp = 1.2 * (1.0 - (double)t / iters) + 0.08;
        if (c2 <= c || rnd01() < exp(-(double)(c2 - c) / temp)) {
            c = c2;
        } else {
            set_gen(j, old);
        }
    }
    return c == 0;
}

int main(int argc, char **argv) {
    if (argc < 7) {
        fprintf(stderr, "usage: d D best cap seed time\n");
        return 1;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    long long best0 = atoll(argv[3]);
    CAP = atoi(argv[4]);
    unsigned long long seed = strtoull(argv[5], NULL, 10);
    TL = atof(argv[6]);
    tstart = (double)clock() / CLOCKS_PER_SEC;

    rs = (seed + 1) * 0x9E3779B97F4A7C15ULL ^ 0xA24BAED4963EE407ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 8; i++) rnd64();

    if (DEG < 3 || DIAM < 3 || CAP < 8) {
        printf("0 0\n");
        return 0;
    }

    int half = CAP / 2;
    size_t hs = (size_t)half + 2;
    AA = malloc(sizeof(int) * hs);
    BB = malloc(sizeof(int) * hs);
    PW = malloc(sizeof(int) * hs);
    S = malloc(sizeof(int) * (size_t)DEG);
    SI = malloc(sizeof(int) * (size_t)DEG);
    RT = malloc(sizeof(int) * (size_t)DEG * hs);
    RI = malloc(sizeof(int) * (size_t)DEG * hs);
    stamp = calloc(2 * hs, sizeof(int));
    qn = malloc(sizeof(int) * 2 * hs);
    qd = malloc(2 * hs);
    bestRT = malloc(sizeof(int) * (size_t)DEG * hs);
    if (!AA || !BB || !PW || !S || !SI || !RT || !RI || !stamp || !qn || !qd || !bestRT) {
        printf("0 0\n");
        return 0;
    }
    epoch = 0;
    have_best = 0;
    timed_out = 0;

    long long lowN = best0 / 2 + 1;
    if (lowN < DEG + 1) lowN = DEG + 1;

    while (elapsed() < TL) {
        if (lowN > half) break;
        long long span = lowN / 10 + 2;
        long long Nc = lowN + rndint((int)span);
        if (Nc > half) Nc = lowN;
        if (!choose_group((int)Nc)) continue;
        int ok = anneal(25000);
        if (timed_out) break;
        if (ok) {
            memcpy(bestRT, RT, sizeof(int) * (size_t)DEG * N);
            bestN = N;
            have_best = 1;
            lowN = (long long)N + 1;
        }
    }

    if (!have_best) {
        printf("0 0\n");
        return 0;
    }
    int V = 2 * bestN;
    long long m = (long long)bestN * DEG;
    printf("%d %lld\n", V, m);
    for (int g = 0; g < bestN; g++)
        for (int j = 0; j < DEG; j++)
            printf("%d %d\n", g, bestN + bestRT[j * bestN + g]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# OLD ENGINE (fallback): bi-Cayley voltage annealing over Z_m x| Z_k2 with
# iterated local search. Kept verbatim from the previous version so that the
# block-lift search still runs after the new engine.
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

/* Store the current layer/voltage state as the best seen for this group. */
static void save_snap(int64_t cost) {
    int n = DEG * K;
    for (int e = 0; e < n; e++) {
        snapL[e] = lay[e];
        snapV[e] = vol[e];
    }
    GBEST = cost;
}

/* Restore the best snapshot and re-draw nk random voltages (ILS kick). */
static void restore_kick(int nk) {
    int n = DEG * K;
    for (int e = 0; e < n; e++) {
        lay[e] = snapL[e];
        vol[e] = snapV[e];
    }
    for (int j = 0; j < nk; j++) vol[rndint(n)] = rndint(G);
}

/* reinit = 1: random permutations and voltages. reinit = 0: continue from the
   current lay/vol state (every rejected move was reverted, so it is consistent). */
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
            /* layer-swap move */
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
            /* voltage move, defect-targeted with probability 0.4 */
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

        /* accepted */
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
        /* Iterated local search: after a near miss, restart from the best
           snapshot of this group with a small random kick. */
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
# Safe baseline families.
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
# Slack extension: add new vertices using spare degree, accepting only
# graphs that pass lib.is_valid.
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


def _run_engine(source, args, timeout):
    """Run a C engine and parse its output. Returns (n, edges) or None on any failure."""
    try:
        text = lib.run_c(source, args, timeout=timeout)
        return lib.parse_graph_text(text)
    except Exception:
        return None


# ----------------------------------------------------------------------------
# Main build: exact constructions first, then the bi-Cayley search over
# non-abelian groups, then the old block-lift search, then slack.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    final_deadline = start + max(1.0, time_limit - 3.0)
    rng = random.Random(seed)
    seed_int = int(seed) & 0x7FFFFFFF

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

    # Exact constructions: return immediately (calibration-style cases).
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

    cap = lib.moore_bound(d, D)

    if d >= 3 and D >= 3:
        # New family: bi-Cayley graphs over non-abelian Z_m x| Z_k (about 60% of budget).
        remaining = start + 0.6 * budget - time.monotonic()
        if remaining > 2.0:
            res = _run_engine(BICAY_SOURCE,
                              [d, D, best_n, cap, seed_int, round(remaining, 2)],
                              remaining + 20.0)
            if res is not None:
                consider(*res)

        # Old family: block voltage lifts, started from the best graph so far.
        remaining = start + budget - time.monotonic()
        if remaining > 2.0:
            res = _run_engine(C_SOURCE,
                              [d, D, best_n, cap, seed_int, round(remaining, 2)],
                              remaining + 20.0)
            if res is not None:
                consider(*res)

    # Use any spare degree in the best graph to add vertices.
    if time.monotonic() < final_deadline:
        n2, e2 = _slack_extend(best[0], best[1], d, D, rng, final_deadline)
        consider(n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
