import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Combined program: bi-Cayley voltage annealing over Z_m x| Z_k2 (C engine),
# plus a NEW non-group search: annealed 2-lifts of the best graph.
#
# New in this version (LIFT_SOURCE):
#   A 2-lift (double cover) of a bipartite graph H doubles the order and keeps
#   the degree. Each base edge gets a sign s in {0,1}; lifted vertices are
#   (v,0),(v,1) and the edge joins (u,a)-(v,a XOR s). Every cover of a bipartite
#   graph is bipartite, so validity reduces to diameter. The search space is
#   2^m signings, not the group-voltage space used by the main engine. The C
#   annealer uses bitset balls of radius D and targets flips at base edges
#   incident to a lifted vertex that still misses some vertices within D.
#   Output is either a valid lift or "0 0".
#
# Python:
#   - exact constructions (PG(2,q), W(q)) as start graphs when they apply,
#   - K_{d,d} fallback,
#   - group-voltage C search (parent engine),
#   - 2-lift annealing on the best graph found,
#   - greedy slack extension; every candidate passes lib.is_valid.
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

/* Iterated-local-search memory: best near-miss state seen so far. */
static int have_near;
static int nr_K, nr_M, nr_K2, nr_R, nr_G, nr_N;
static int64_t nr_cost;
static int *nr_lay, *nr_vol;

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + (double)ts.tv_nsec * 1e-9;
}

static double elapsed(void) {
    return now_s() - tstart;
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
        double mv = rnd01();

        if (K >= 2 && mv < 0.25) {
            /* layer swap: exchange two permutation entries at one layer */
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
        } else if (DEG >= 2 && mv < 0.40) {
            /* voltage exchange: swap voltages of base vertex i between two layers. */
            int l1 = rndint(DEG);
            int l2 = rndint(DEG - 1);
            if (l2 >= l1) l2++;
            int i = rndint(K);
            int e1 = l1 * K + i, e2 = l2 * K + i;
            int v1 = vol[e1], v2 = vol[e2];
            if (v1 == v2) continue;
            vol[e1] = v2;
            vol[e2] = v1;
            set_dart(l1, i, lay[e1], v2);
            set_dart(l2, i, lay[e2], v1);
            compute_reach(scr);
            c2 = total_cost(scr);
            if (!(c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp))) {
                vol[e1] = v1;
                vol[e2] = v2;
                set_dart(l1, i, lay[e1], v1);
                set_dart(l2, i, lay[e2], v2);
                continue;
            }
        } else {
            /* single voltage change, defect-targeted with probability 0.4 */
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
        if (cost < best_cost) {
            best_cost = cost;
            last = t;
        }
    }
    LASTCOST = cost;
    return cost == 0;
}

/* Save the current (consistent) lay/vol state and its group as the near-miss memory. */
static void save_near(void) {
    have_near = 1;
    nr_K = K;
    nr_M = M;
    nr_K2 = K2;
    nr_R = R;
    nr_G = G;
    nr_N = N;
    nr_cost = LASTCOST;
    memcpy(nr_lay, lay, sizeof(int) * (size_t)DEG * MAXK);
    memcpy(nr_vol, vol, sizeof(int) * (size_t)DEG * MAXK);
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
    tstart = now_s();

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
    nr_lay = malloc(sizeof(int) * (size_t)DEG * MAXK);
    nr_vol = malloc(sizeof(int) * (size_t)DEG * MAXK);
    cur = malloc((size_t)CAP);
    scr = malloc((size_t)CAP);
    tmpb = malloc((size_t)CAP);
    bestnbr = malloc(sizeof(int) * (size_t)DEG * CAP);
    if (!AA || !BB || !nbr || !lay || !vol || !nr_lay || !nr_vol || !cur || !scr ||
        !tmpb || !bestnbr) {
        printf("0 0\n");
        return 0;
    }

    double tr[MAXK + 1] = {0}, wn[MAXK + 1] = {0};
    long long found = best0;

    while (elapsed() < TL) {
        if (found >= CAP) break;
        int k = 1;
        int ok = 0;

        if (have_near && nr_N > found && rnd01() < 0.5) {
            /* Iterated local search: kick the saved near-miss state and re-anneal it. */
            k = nr_K;
            K = nr_K;
            M = nr_M;
            K2 = nr_K2;
            R = nr_R;
            G = nr_G;
            N = nr_N;
            FULL = (uint8_t)((1u << (2 * K)) - 1);
            setup_group();
            memcpy(lay, nr_lay, sizeof(int) * (size_t)DEG * MAXK);
            memcpy(vol, nr_vol, sizeof(int) * (size_t)DEG * MAXK);
            int kicks = 2 + rndint(4);
            for (int q = 0; q < kicks; q++) {
                int l = rndint(DEG), i = rndint(K);
                vol[l * K + i] = rndint(G);
            }
            ok = run_trial(3000, 1000, 0);
        } else {
            k = pick_k(tr, wn);
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
            ok = run_trial(4000, 1200, 1);
        }

        /* Near miss: keep annealing the same group from its final state. */
        int extra = 0;
        while (!ok && !timed_out && extra < 3 && LASTCOST <= (int64_t)N / 2 && elapsed() < TL) {
            ok = run_trial(6000, 2000, 0);
            extra++;
        }

        /* Remember the best unsuccessful state for later kicks. */
        if (!ok && !timed_out && LASTCOST > 0) {
            if (!have_near || LASTCOST < nr_cost || nr_N <= found) save_near();
        }

        if (ok) {
            wn[k] += 1.0;
            found = N;
            memcpy(bestnbr, nbr, sizeof(int) * (size_t)DEG * N);
            best_stride = N;
            best_K = K;
            best_G = G;
            have_best = 1;
            have_near = 0;
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


LIFT_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

/* Annealed 2-lift search. argv: D seed time_limit. stdin: base graph "n m" + edges.
   Lifted vertex 2v+a, base edge e=(u,v) with sign sg[e] joins (u,a)-(v,a^sg[e]).
   Output: a valid lift (diameter <= D) or "0 0". */

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

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + (double)ts.tv_nsec * 1e-9;
}

static inline int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int DIAM_, N, W, n0, m0;
static int *eu, *ev, *off, *inc_e, *inc_w;
static unsigned char *sg;
static uint64_t *Tbuf;

/* Number of ordered pairs at distance > DIAM_ (0 = valid). R receives the balls. */
static int64_t eval_lift(uint64_t *R) {
    size_t words = (size_t)N * W;
    memset(R, 0, sizeof(uint64_t) * words);
    for (int x = 0; x < N; x++) R[(size_t)x * W + (x >> 6)] |= 1ULL << (x & 63);
    for (int t = 0; t < DIAM_; t++) {
        for (int x = 0; x < N; x++) {
            uint64_t *tx = Tbuf + (size_t)x * W;
            const uint64_t *rx = R + (size_t)x * W;
            memcpy(tx, rx, sizeof(uint64_t) * (size_t)W);
            int v = x >> 1, s = x & 1;
            for (int k = off[v]; k < off[v + 1]; k++) {
                int e = inc_e[k], w = inc_w[k];
                int y = 2 * w + (s ^ sg[e]);
                const uint64_t *ry = R + (size_t)y * W;
                for (int j = 0; j < W; j++) tx[j] |= ry[j];
            }
        }
        if (memcmp(Tbuf, R, sizeof(uint64_t) * words) == 0) break;
        memcpy(R, Tbuf, sizeof(uint64_t) * words);
    }
    int64_t tot = 0;
    for (size_t i = 0; i < words; i++) tot += pc64(R[i]);
    return (int64_t)N * N - tot;
}

int main(int argc, char **argv) {
    if (argc < 4) {
        printf("0 0\n");
        return 0;
    }
    DIAM_ = atoi(argv[1]);
    unsigned long long seed = strtoull(argv[2], NULL, 10);
    double TL = atof(argv[3]);
    double t0 = now_s();

    rs = (seed + 7) * 0x9E3779B97F4A7C15ULL ^ 0xA0761D6478BD642FULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 8; i++) rnd64();

    if (scanf("%d %d", &n0, &m0) != 2 || n0 <= 0 || m0 <= 0 || DIAM_ < 1) {
        printf("0 0\n");
        return 0;
    }
    eu = malloc(sizeof(int) * (size_t)m0);
    ev = malloc(sizeof(int) * (size_t)m0);
    if (!eu || !ev) {
        printf("0 0\n");
        return 0;
    }
    for (int e = 0; e < m0; e++) {
        if (scanf("%d %d", &eu[e], &ev[e]) != 2 || eu[e] < 0 || ev[e] < 0 ||
            eu[e] >= n0 || ev[e] >= n0 || eu[e] == ev[e]) {
            printf("0 0\n");
            return 0;
        }
    }

    int *deg = calloc((size_t)n0, sizeof(int));
    int *fill = calloc((size_t)n0, sizeof(int));
    off = malloc(sizeof(int) * (size_t)(n0 + 1));
    if (!deg || !fill || !off) {
        printf("0 0\n");
        return 0;
    }
    for (int e = 0; e < m0; e++) {
        deg[eu[e]]++;
        deg[ev[e]]++;
    }
    off[0] = 0;
    for (int v = 0; v < n0; v++) off[v + 1] = off[v] + deg[v];
    int tot = off[n0];
    inc_e = malloc(sizeof(int) * (size_t)(tot > 0 ? tot : 1));
    inc_w = malloc(sizeof(int) * (size_t)(tot > 0 ? tot : 1));
    if (!inc_e || !inc_w) {
        printf("0 0\n");
        return 0;
    }
    for (int e = 0; e < m0; e++) {
        int u = eu[e], v = ev[e];
        int k = off[u] + fill[u]++;
        inc_e[k] = e;
        inc_w[k] = v;
        k = off[v] + fill[v]++;
        inc_e[k] = e;
        inc_w[k] = u;
    }

    N = 2 * n0;
    W = (N + 63) / 64;
    size_t words = (size_t)N * W;
    if (words > 40000000ULL) {
        printf("0 0\n");
        return 0;
    }
    uint64_t *Ra = malloc(sizeof(uint64_t) * words);
    uint64_t *Rb = malloc(sizeof(uint64_t) * words);
    Tbuf = malloc(sizeof(uint64_t) * words);
    sg = malloc((size_t)m0);
    if (!Ra || !Rb || !Tbuf || !sg) {
        printf("0 0\n");
        return 0;
    }
    for (int e = 0; e < m0; e++) sg[e] = (unsigned char)rndint(2);

    uint64_t *cur = Ra, *nxt = Rb;
    int64_t cost = eval_lift(cur);

    while (cost > 0) {
        double el = now_s() - t0;
        if (el > TL) break;

        /* Pick a lifted vertex that misses some vertices within DIAM_. */
        int x = -1, cnt = 0;
        for (int y = 0; y < N; y++) {
            const uint64_t *ry = cur + (size_t)y * W;
            int c = 0;
            for (int j = 0; j < W; j++) c += pc64(ry[j]);
            if (c < N) {
                cnt++;
                if (rndint(cnt) == 0) x = y;
            }
        }
        if (x < 0) break;
        int v = x >> 1;
        int dv = off[v + 1] - off[v];
        if (dv == 0) continue;
        int e = inc_e[off[v] + rndint(dv)];

        sg[e] ^= 1;
        int64_t c2 = eval_lift(nxt);
        double frac = (now_s() - t0) / TL;
        double temp = 1.5 * (1.0 - frac) + 0.05;
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
            uint64_t *tp = cur;
            cur = nxt;
            nxt = tp;
            cost = c2;
        } else {
            sg[e] ^= 1;
        }
    }

    if (cost != 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %lld\n", N, 2LL * m0);
    for (int e = 0; e < m0; e++)
        for (int s = 0; s < 2; s++)
            printf("%d %d\n", 2 * eu[e] + s, 2 * ev[e] + (s ^ sg[e]));
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact constructions used as the start graph.
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


# ----------------------------------------------------------------------------
# New search stage: annealed 2-lift of the best graph (non-group double cover).
# ----------------------------------------------------------------------------

def _lift_search(n, edges, D, seed, seconds):
    """Run the C 2-lift annealer on (n, edges); returns (n2, e2), possibly (0, [])."""
    text = lib.run_c(LIFT_SOURCE, [D, int(seed) & 0x7FFFFFFF, round(seconds, 2)],
                     stdin_graph=(n, edges), timeout=seconds + 20.0)
    return lib.parse_graph_text(text)


# ----------------------------------------------------------------------------
# Main build: exact constructions first, then the C group-voltage search,
# then the 2-lift stage, then slack extension.
# ----------------------------------------------------------------------------

_MAX_CAP = 2_000_000  # keeps the C allocations and the int parsing safe


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

    # Exact constructions: return immediately on calibration-style cases.
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
        # Stage A: group-voltage search in C (about 75% of the budget).
        group_end = start + 0.75 * budget
        remaining = group_end - time.monotonic()
        if remaining > 2.0:
            cap = min(lib.moore_bound(d, D), _MAX_CAP)
            if cap > best_n:
                try:
                    text = lib.run_c(C_SOURCE,
                                     [d, D, best_n, cap, int(seed) & 0x7FFFFFFF, round(remaining, 2)],
                                     timeout=remaining + 20.0)
                    n2, e2 = lib.parse_graph_text(text)
                    consider(n2, e2)
                except Exception:
                    pass

        # Stage B: annealed 2-lift of the best graph (rest of the budget).
        rem2 = start + budget - time.monotonic()
        if rem2 > 2.0 and best_n >= 2:
            N2 = 2 * best_n
            if N2 * ((N2 + 63) // 64) <= 40_000_000 and N2 <= _MAX_CAP:
                try:
                    n3, e3 = _lift_search(best[0], best[1], D, int(seed) + 1, rem2)
                    consider(n3, e3)
                except Exception:
                    pass

    # Use spare degree in the best graph to add vertices.
    if time.monotonic() < final_deadline:
        try:
            n2, e2 = _slack_extend(best[0], best[1], d, D, rng, final_deadline)
            consider(n2, e2)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
