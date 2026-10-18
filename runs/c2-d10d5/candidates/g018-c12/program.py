import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Stage A: bi-Cayley voltage annealing over Z_m x| Z_k2 (unchanged parent engine).
# Vertices: A_{i,g} = i*G + g, B_{p,h} = (K+p)*G + h. Each layer is a permutation
# with voltages, so the graph is DEG-regular. Cost = unreached pairs + penalty*dups.
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
# Stage B (new, different construction): generic bipartite graph growth + repair.
#
# Start from any valid bipartite graph (the stage-A output). Each growth step adds
# one A-vertex x and one B-vertex y. Pick DEG edges (a_i, b_i) with all a_i distinct
# and all b_i distinct. Rewire each to (x, b_i) and add (a_i, y). Degrees of old
# vertices are unchanged and x, y get degree DEG. The graph then has defects, so
# a 2-switch annealer (degree and bipartition preserving) minimizes the number of
# vertex pairs at distance > DIAM. A repaired graph is kept, otherwise we roll back.
# Reach sets are bitsets over all vertices, with Jacobi-style rounds so distances
# are exact.
# ----------------------------------------------------------------------------

C_GROW = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define DMAX 64
#define REP_ITERS 1500

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
static int rndint(int k) {
    return (int)(rnd64() % (uint64_t)k);
}

static int DEG, DIAM, CAP, WC, EMAX;
static int n, m;
static int *ea, *eb;
static int *sn_ea, *sn_eb, sn_n, sn_m;
static uint64_t *adj, *Rc, *Rn;
static int *stA, *stB, stamp;
static double TL, tstart;

static double elapsed(void) {
    return (double)clock() / CLOCKS_PER_SEC - tstart;
}

static inline int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static inline int isadj(int u, int v) {
    return (int)((adj[(size_t)u * WC + (v >> 6)] >> (v & 63)) & 1ULL);
}

static inline void setadj(int u, int v, int val) {
    uint64_t *p = &adj[(size_t)u * WC + (v >> 6)];
    uint64_t bit = 1ULL << (v & 63);
    if (val) *p |= bit;
    else *p &= ~bit;
}

static inline void set_pair(int u, int v, int val) {
    setadj(u, v, val);
    setadj(v, u, val);
}

static void rebuild_adj(void) {
    memset(adj, 0, sizeof(uint64_t) * (size_t)CAP * WC);
    for (int e = 0; e < m; e++) set_pair(ea[e], eb[e], 1);
}

static void snapshot(void) {
    sn_n = n;
    sn_m = m;
    memcpy(sn_ea, ea, sizeof(int) * (size_t)m);
    memcpy(sn_eb, eb, sizeof(int) * (size_t)m);
}

static void restore(void) {
    n = sn_n;
    m = sn_m;
    memcpy(ea, sn_ea, sizeof(int) * (size_t)m);
    memcpy(eb, sn_eb, sizeof(int) * (size_t)m);
    rebuild_adj();
}

/* Number of unordered pairs at distance > DIAM (unreachable counts too). */
static long long eval_cost(void) {
    int W = (n + 63) >> 6;
    for (int v = 0; v < n; v++) {
        uint64_t *r = Rc + (size_t)v * WC;
        for (int w = 0; w < W; w++) r[w] = 0;
        r[v >> 6] |= 1ULL << (v & 63);
    }
    for (int t = 0; t < DIAM; t++) {
        for (int v = 0; v < n; v++)
            memcpy(Rn + (size_t)v * WC, Rc + (size_t)v * WC, sizeof(uint64_t) * (size_t)W);
        for (int e = 0; e < m; e++) {
            int a = ea[e], b = eb[e];
            uint64_t *ra = Rn + (size_t)a * WC, *rb = Rn + (size_t)b * WC;
            const uint64_t *ca = Rc + (size_t)a * WC, *cb = Rc + (size_t)b * WC;
            for (int w = 0; w < W; w++) {
                ra[w] |= cb[w];
                rb[w] |= ca[w];
            }
        }
        uint64_t *tmp = Rc;
        Rc = Rn;
        Rn = tmp;
    }
    long long s = 0;
    for (int v = 0; v < n; v++) {
        const uint64_t *r = Rc + (size_t)v * WC;
        int c = 0;
        for (int w = 0; w < W; w++) c += pc64(r[w]);
        s += n - c;
    }
    return s / 2;
}

/* Add two vertices x (side A) and y (side B) with DEG rewired edges. */
static int grow(void) {
    if (n + 2 > CAP || m + DEG > EMAX) return 0;
    int sel[DMAX];
    int cnt = 0;
    stamp++;
    for (int tr = 0; tr < 20000 && cnt < DEG; tr++) {
        int e = rndint(m);
        int a = ea[e], b = eb[e];
        if (stA[a] == stamp || stB[b] == stamp) continue;
        stA[a] = stamp;
        stB[b] = stamp;
        sel[cnt++] = e;
    }
    if (cnt < DEG) return 0;
    int x = n, y = n + 1;
    n += 2;
    for (int i = 0; i < DEG; i++) {
        int e = sel[i];
        int a = ea[e], b = eb[e];
        set_pair(a, b, 0);
        ea[e] = x;
        eb[e] = b;
        set_pair(x, b, 1);
        ea[m] = a;
        eb[m] = y;
        set_pair(a, y, 1);
        m++;
    }
    return 1;
}

/* 2-switch annealing: (a,b),(a2,b2) -> (a,b2),(a2,b). Returns 1 if cost reaches 0. */
static int repair(long long iters) {
    long long cost = eval_cost();
    if (cost == 0) return 1;
    double T0 = 1.0 + 0.02 * (double)cost;
    for (long long it = 0; it < iters; it++) {
        if ((it & 7) == 0 && elapsed() > TL) break;
        double T = T0 * (1.0 - (double)it / (double)iters) + 0.05;
        int e1 = rndint(m), e2 = rndint(m);
        if (e1 == e2) continue;
        int a = ea[e1], b = eb[e1], a2 = ea[e2], b2 = eb[e2];
        if (a == a2 || b == b2) continue;
        if (isadj(a, b2) || isadj(a2, b)) continue;
        set_pair(a, b, 0);
        set_pair(a2, b2, 0);
        set_pair(a, b2, 1);
        set_pair(a2, b, 1);
        eb[e1] = b2;
        eb[e2] = b;
        long long nc = eval_cost();
        long long dl = nc - cost;
        if (dl <= 0 || rnd01() < exp(-(double)dl / T)) {
            cost = nc;
            if (cost == 0) return 1;
        } else {
            set_pair(a, b2, 0);
            set_pair(a2, b, 0);
            set_pair(a, b, 1);
            set_pair(a2, b2, 1);
            eb[e1] = b;
            eb[e2] = b2;
        }
    }
    return cost == 0;
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: d D seed time cap < graph\n");
        return 1;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    TL = atof(argv[4]);
    CAP = atoi(argv[5]);
    tstart = (double)clock() / CLOCKS_PER_SEC;
    rs = (seed + 7) * 0x9E3779B97F4A7C15ULL ^ 0xA0761D6478BD642FULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 8; i++) rnd64();

    if (DEG < 2 || DEG > DMAX || DIAM < 1 || CAP < 4) {
        printf("0 0\n");
        return 0;
    }
    WC = (CAP + 63) >> 6;
    EMAX = CAP * DEG + 8;

    int n0, m0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 < 1 || n0 > CAP || m0 < 0) {
        printf("0 0\n");
        return 0;
    }
    if (m0 > EMAX) {
        printf("0 0\n");
        return 0;
    }
    int *ru = malloc(sizeof(int) * (size_t)(m0 + 1));
    int *rv = malloc(sizeof(int) * (size_t)(m0 + 1));
    for (int i = 0; i < m0; i++) {
        if (scanf("%d %d", &ru[i], &rv[i]) != 2 || ru[i] < 0 || ru[i] >= n0 || rv[i] < 0 || rv[i] >= n0) {
            printf("0 0\n");
            return 0;
        }
    }

    /* Bipartition by BFS (CSR adjacency). */
    int *dg = calloc((size_t)n0 + 1, sizeof(int));
    for (int i = 0; i < m0; i++) {
        dg[ru[i] + 1]++;
        dg[rv[i] + 1]++;
    }
    for (int i = 0; i < n0; i++) dg[i + 1] += dg[i];
    int *pos = malloc(sizeof(int) * (size_t)n0);
    for (int i = 0; i < n0; i++) pos[i] = dg[i];
    int *nb = malloc(sizeof(int) * (size_t)(2 * m0 + 2));
    for (int i = 0; i < m0; i++) {
        nb[pos[ru[i]]++] = rv[i];
        nb[pos[rv[i]]++] = ru[i];
    }
    int *col = malloc(sizeof(int) * (size_t)n0);
    int *q = malloc(sizeof(int) * (size_t)n0);
    for (int i = 0; i < n0; i++) col[i] = -1;
    int bad = 0;
    for (int s = 0; s < n0 && !bad; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int qh = 0, qt = 0;
        q[qt++] = s;
        while (qh < qt && !bad) {
            int u = q[qh++];
            for (int k = dg[u]; k < dg[u + 1]; k++) {
                int v = nb[k];
                if (col[v] < 0) {
                    col[v] = 1 - col[u];
                    q[qt++] = v;
                } else if (col[v] == col[u]) {
                    bad = 1;
                    break;
                }
            }
        }
    }
    if (bad) {
        printf("0 0\n");
        return 0;
    }

    ea = malloc(sizeof(int) * (size_t)EMAX);
    eb = malloc(sizeof(int) * (size_t)EMAX);
    sn_ea = malloc(sizeof(int) * (size_t)EMAX);
    sn_eb = malloc(sizeof(int) * (size_t)EMAX);
    adj = malloc(sizeof(uint64_t) * (size_t)CAP * WC);
    Rc = malloc(sizeof(uint64_t) * (size_t)CAP * WC);
    Rn = malloc(sizeof(uint64_t) * (size_t)CAP * WC);
    stA = calloc((size_t)CAP + 2, sizeof(int));
    stB = calloc((size_t)CAP + 2, sizeof(int));
    stamp = 0;
    if (!ea || !eb || !sn_ea || !sn_eb || !adj || !Rc || !Rn || !stA || !stB) {
        printf("0 0\n");
        return 0;
    }

    n = n0;
    m = 0;
    for (int i = 0; i < m0; i++) {
        if (col[ru[i]] == 0) {
            ea[m] = ru[i];
            eb[m] = rv[i];
        } else {
            ea[m] = rv[i];
            eb[m] = ru[i];
        }
        m++;
    }
    rebuild_adj();
    if (!(eval_cost() == 0 || repair(20000))) {
        printf("0 0\n");
        return 0;
    }
    snapshot();

    while (elapsed() < TL) {
        if (n + 2 > CAP) break;
        if (!grow()) continue;
        if (repair(REP_ITERS)) {
            snapshot();
        } else {
            restore();
        }
    }

    printf("%d %d\n", sn_n, sn_m);
    for (int e = 0; e < sn_m; e++)
        printf("%d %d\n", sn_ea[e], sn_eb[e]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact and safe constructions.
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
# Main build: exact constructions, then stage A (voltage search) for part of the
# budget, then stage B (growth + repair from the stage-A graph) for the rest.
# Every candidate is checked with lib.is_valid before it can replace the fallback.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    deadline = t0 + max(1.0, time_limit - 6.0)

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

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    if d < 3 or D < 3:
        return best

    # Stage A: voltage annealing over small groups (parent engine), 40% of the budget.
    rem = deadline - time.monotonic()
    if rem > 2.0:
        budA = max(1.0, 0.4 * rem)
        cap = lib.moore_bound(d, D)
        try:
            text = lib.run_c(C_SOURCE,
                             [d, D, best_n, cap, int(seed) & 0x7FFFFFFF, round(budA, 2)],
                             timeout=budA + 15.0)
            n2, e2 = lib.parse_graph_text(text)
            consider(n2, e2)
        except Exception:
            pass

    # Stage B: different construction. Grow the best valid graph by bipartite
    # vertex-pair insertion, then repair defects with 2-switch annealing.
    rem = deadline - time.monotonic()
    if rem > 3.0:
        capB = min(lib.moore_bound(d, D), 6000)
        if best_n + 2 <= capB:
            try:
                text = lib.run_c(C_GROW,
                                 [d, D, int(seed) & 0x7FFFFFFF, round(rem - 2.0, 2), capB],
                                 stdin_graph=best,
                                 timeout=rem + 5.0)
                n2, e2 = lib.parse_graph_text(text)
                consider(n2, e2)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
