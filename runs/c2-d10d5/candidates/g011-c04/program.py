import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Engine 1 (unchanged from the parent): bi-Cayley voltage annealing over
# Z_m x| Z_k2. Produces the starting graph for the swap engine below.
# ----------------------------------------------------------------------------

VOLT_SOURCE = r"""
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
    cur = malloc((size_t)CAP);
    scr = malloc((size_t)CAP);
    tmpb = malloc((size_t)CAP);
    bestnbr = malloc(sizeof(int) * (size_t)DEG * CAP);
    if (!AA || !BB || !nbr || !lay || !vol || !cur || !scr || !tmpb || !bestnbr) {
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
        while (!ok && !timed_out && extra < 6 && LASTCOST <= (int64_t)N / 4 && elapsed() < TL) {
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
# Engine 2 (new, substantially different): unstructured edge-swap annealing.
#
# Input: a valid bipartite graph (stdin). The search leaves the algebra
# behind. It adds one new A-vertex and one new B-vertex, then anneals over
# degree-preserving 2-switches plus edge insertions between deficient
# vertices. Cost = number of unordered pairs at distance > D, computed exactly
# by multiword bitset BFS. When cost reaches 0 the graph is saved and the
# size grows by 2. Output is always a valid graph or "0 0".
# ----------------------------------------------------------------------------

SWAP_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static inline int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int DEG, DIAM, CAP, NV, W;
static double TL, tstart;
static int *side, *deg, *nb;
static int *listA, *listB, nA, nB;
static int *bnb, *bdeg;
static int *snb, *sdeg, snv;
static int have_sol;
static uint64_t *RA, *RB;

static double elapsed(void) { return (double)clock() / CLOCKS_PER_SEC - tstart; }

static int is_adj(int a, int b) {
    const int *row = nb + (size_t)a * DEG;
    for (int k = 0; k < deg[a]; k++)
        if (row[k] == b) return 1;
    return 0;
}

static void repl(int v, int old, int nw) {
    int *row = nb + (size_t)v * DEG;
    for (int k = 0; k < deg[v]; k++)
        if (row[k] == old) {
            row[k] = nw;
            return;
        }
}

static void add_e(int a, int b) {
    nb[(size_t)a * DEG + deg[a]++] = b;
    nb[(size_t)b * DEG + deg[b]++] = a;
}

static void del_e(int a, int b) {
    int *ra = nb + (size_t)a * DEG;
    for (int k = 0; k < deg[a]; k++)
        if (ra[k] == b) {
            ra[k] = ra[--deg[a]];
            break;
        }
    int *rb = nb + (size_t)b * DEG;
    for (int k = 0; k < deg[b]; k++)
        if (rb[k] == a) {
            rb[k] = rb[--deg[b]];
            break;
        }
}

/* Unordered pairs at distance > DIAM. */
static int64_t cost_full(void) {
    W = (NV + 63) / 64;
    size_t tot = (size_t)NV * W;
    memset(RA, 0, sizeof(uint64_t) * tot);
    for (int v = 0; v < NV; v++) RA[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    uint64_t *cur = RA, *nxt = RB;
    for (int t = 0; t < DIAM; t++) {
        for (int v = 0; v < NV; v++) {
            uint64_t *o = nxt + (size_t)v * W;
            memcpy(o, cur + (size_t)v * W, sizeof(uint64_t) * W);
            const int *row = nb + (size_t)v * DEG;
            for (int k = 0; k < deg[v]; k++) {
                const uint64_t *s = cur + (size_t)row[k] * W;
                for (int w = 0; w < W; w++) o[w] |= s[w];
            }
        }
        uint64_t *tmp = cur;
        cur = nxt;
        nxt = tmp;
    }
    int64_t cnt = 0;
    for (size_t i = 0; i < tot; i++) cnt += pc64(cur[i]);
    return ((int64_t)NV * NV - cnt) / 2;
}

static void save_best(void) {
    memcpy(bnb, nb, sizeof(int) * (size_t)NV * DEG);
    memcpy(bdeg, deg, sizeof(int) * (size_t)NV);
}

static void restore_best(void) {
    memcpy(nb, bnb, sizeof(int) * (size_t)NV * DEG);
    memcpy(deg, bdeg, sizeof(int) * (size_t)NV);
}

static void save_sol(void) {
    memcpy(snb, nb, sizeof(int) * (size_t)NV * DEG);
    memcpy(sdeg, deg, sizeof(int) * (size_t)NV);
    snv = NV;
    have_sol = 1;
}

static void grow(void) {
    int a = NV, b = NV + 1;
    side[a] = 0;
    side[b] = 1;
    deg[a] = 0;
    deg[b] = 0;
    listA[nA++] = a;
    listB[nB++] = b;
    NV += 2;
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: d D cap seed time\n");
        return 1;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    CAP = atoi(argv[3]);
    unsigned long long seed = strtoull(argv[4], NULL, 10);
    TL = atof(argv[5]);
    rs = (seed + 1) * 0x9E3779B97F4A7C15ULL ^ 0xD1B54A32D192ED03ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 8; i++) rnd64();
    tstart = (double)clock() / CLOCKS_PER_SEC;

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 < 2 || n0 > CAP - 2 || DEG < 2 || DIAM < 2) {
        printf("0 0\n");
        return 0;
    }
    size_t cap = (size_t)CAP + 2;
    side = malloc(sizeof(int) * cap);
    deg = calloc(cap, sizeof(int));
    nb = calloc(cap * (size_t)DEG, sizeof(int));
    listA = malloc(sizeof(int) * cap);
    listB = malloc(sizeof(int) * cap);
    bnb = malloc(sizeof(int) * cap * (size_t)DEG);
    bdeg = malloc(sizeof(int) * cap);
    snb = malloc(sizeof(int) * cap * (size_t)DEG);
    sdeg = malloc(sizeof(int) * cap);
    size_t Wmax = (cap + 63) / 64;
    RA = malloc(sizeof(uint64_t) * cap * Wmax);
    RB = malloc(sizeof(uint64_t) * cap * Wmax);
    int *stack = malloc(sizeof(int) * cap);
    if (!side || !deg || !nb || !listA || !listB || !bnb || !bdeg || !snb || !sdeg ||
        !RA || !RB || !stack) {
        printf("0 0\n");
        return 0;
    }

    NV = n0;
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) {
            printf("0 0\n");
            return 0;
        }
        if (u < 0 || v < 0 || u >= n0 || v >= n0 || u == v || deg[u] >= DEG ||
            deg[v] >= DEG || is_adj(u, v)) {
            printf("0 0\n");
            return 0;
        }
        add_e(u, v);
    }

    /* Bipartition by BFS. */
    for (int v = 0; v < NV; v++) side[v] = -1;
    for (int s = 0; s < NV; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int sp = 0;
        stack[sp++] = s;
        while (sp) {
            int u = stack[--sp];
            for (int k = 0; k < deg[u]; k++) {
                int v = nb[(size_t)u * DEG + k];
                if (side[v] < 0) {
                    side[v] = 1 - side[u];
                    stack[sp++] = v;
                } else if (side[v] == side[u]) {
                    printf("0 0\n");
                    return 0;
                }
            }
        }
    }
    nA = nB = 0;
    for (int v = 0; v < NV; v++) {
        if (side[v] == 0) listA[nA++] = v;
        else listB[nB++] = v;
    }
    if (nA == 0 || nB == 0) {
        printf("0 0\n");
        return 0;
    }

    have_sol = 0;
    int64_t cost = cost_full();
    int64_t bestc = cost;
    save_best();
    int PERIOD = 2500;
    int since = 0;
    double creh = (double)(cost > 1 ? cost : 1);

    while (elapsed() < TL) {
        if (cost == 0) {
            save_sol();
            if (NV + 2 > CAP) break;
            grow();
            cost = cost_full();
            bestc = cost;
            save_best();
            since = 0;
            creh = (double)(cost > 1 ? cost : 1);
            continue;
        }
        if (since >= PERIOD) {
            restore_best();
            cost = bestc;
            since = 0;
            creh = (double)(cost > 1 ? cost : 1);
        }
        double T = 0.03 * creh * (1.0 - (double)since / PERIOD);
        if (T < 0.2) T = 0.2;
        since++;
        int64_t nc;

        if (rnd01() < 0.75) {
            int a1 = listA[rndint(nA)], a2 = listA[rndint(nA)];
            if (a1 == a2 || deg[a1] == 0 || deg[a2] == 0) continue;
            int b1 = nb[(size_t)a1 * DEG + rndint(deg[a1])];
            int b2 = nb[(size_t)a2 * DEG + rndint(deg[a2])];
            if (b1 == b2 || is_adj(a1, b2) || is_adj(a2, b1)) continue;
            repl(a1, b1, b2);
            repl(b1, a1, a2);
            repl(a2, b2, a1);
            repl(b2, a2, b1);
            nc = cost_full();
            if (nc <= cost || rnd01() < exp(-(double)(nc - cost) / T)) {
                cost = nc;
            } else {
                repl(a1, b2, b1);
                repl(b1, a2, a1);
                repl(a2, b1, b2);
                repl(b2, a1, a2);
                continue;
            }
        } else {
            int a = listA[rndint(nA)], b = listB[rndint(nB)];
            if (deg[a] >= DEG || deg[b] >= DEG || is_adj(a, b)) continue;
            add_e(a, b);
            nc = cost_full();
            if (nc <= cost || rnd01() < exp(-(double)(nc - cost) / T)) {
                cost = nc;
            } else {
                del_e(a, b);
                continue;
            }
        }
        if (cost < bestc) {
            bestc = cost;
            save_best();
        }
    }
    if (cost == 0 && (!have_sol || snv != NV)) save_sol();

    if (!have_sol) {
        printf("0 0\n");
        return 0;
    }
    long long m = 0;
    for (int v = 0; v < snv; v++)
        if (side[v] == 0) m += sdeg[v];
    printf("%d %lld\n", snv, m);
    for (int v = 0; v < snv; v++) {
        if (side[v] != 0) continue;
        for (int k = 0; k < sdeg[v]; k++)
            printf("%d %d\n", v, snb[(size_t)v * DEG + k]);
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Safe algebraic families.
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
# Main build: exact constructions, then voltage search (engine 1), then the
# swap annealer (engine 2) started from the best graph so far, then slack.
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

    # Exact constructions.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D == 4 and time.monotonic() < start + budget:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Engine 1: voltage annealing over small groups (gives the large start).
    if d >= 3 and D >= 3:
        remaining = start + 0.5 * budget - time.monotonic()
        if remaining > 2.0:
            cap = lib.moore_bound(d, D)
            try:
                text = lib.run_c(VOLT_SOURCE,
                                 [d, D, best_n, cap, int(seed) & 0x7FFFFFFF, round(remaining, 2)],
                                 timeout=remaining + 20.0)
                consider(*lib.parse_graph_text(text))
            except Exception:
                pass

    # Engine 2: unstructured edge-swap annealing, grown from the current best.
    if d >= 3 and D >= 3 and best[0] >= 4:
        remaining = start + budget - time.monotonic()
        if remaining > 2.0:
            cap = lib.moore_bound(d, D)
            try:
                text = lib.run_c(SWAP_SOURCE,
                                 [d, D, cap, int(seed) & 0x7FFFFFFF, round(remaining, 2)],
                                 stdin_graph=best,
                                 timeout=remaining + 20.0)
                consider(*lib.parse_graph_text(text))
            except Exception:
                pass

    # Use any spare degree in the best graph to add vertices.
    if time.monotonic() < final_deadline:
        n2, e2 = _slack_extend(best[0], best[1], d, D, rng, final_deadline)
        consider(n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
