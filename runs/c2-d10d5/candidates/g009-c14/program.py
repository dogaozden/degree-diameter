import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Two-stage search for the weakest targets (large d, D >= 4).
#
# Stage 1 (C_LIFT): bi-Cayley voltage annealing over Z_m x| Z_k2, as before.
# Stage 2 (C_GROW): a different construction. Take the valid stage-1 graph,
#   add two new vertices a (side A) and b (side B) and remove DEG edges
#   x_i y_i, replacing them with a y_i and b x_i. Degrees are preserved and
#   bipartiteness is kept. The result usually has diameter defects, so
#   2-switch annealing on bad-pair counts repairs it. On success the graph
#   grows again. Every output is re-checked, and the best valid graph is kept.
#
# Start graph: exact constructions (PG(2,q), W(q)) when they apply, else K_{d,d}.
# ----------------------------------------------------------------------------

C_LIFT = r"""
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

static int have_near;
static int nr_K, nr_M, nr_K2, nr_R, nr_G, nr_N;
static int64_t nr_cost;
static int *nr_lay, *nr_vol;

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

static inline int gmul(int x, int y) {
    int bx = BB[x];
    int64_t a2 = (AA[x] + PWR[bx] * (int64_t)AA[y]) % M;
    int b2 = (bx + BB[y]) % K2;
    return (int)(a2 * K2 + b2);
}

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

        int extra = 0;
        while (!ok && !timed_out && extra < 3 && LASTCOST <= (int64_t)N / 2 && elapsed() < TL) {
            ok = run_trial(6000, 2000, 0);
            extra++;
        }

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


C_GROW = r"""
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

static int DEG, DIAM, CAP, W;
static int N, E;
static int *eu, *ev;      /* edge e joins A-vertex eu[e] and B-vertex ev[e] */
static int *adj;          /* adj[v*DEG + s]: neighbours of v */
static int *dg;           /* current degree of v */
static int *mark, *chosen, *col, *qbuf;
static int stamp;
static int *ou, *ov;
static uint64_t *RA, *RB;
static int *bu, *bv, BN, BE;
static double TL, tstart;

static double elapsed(void) {
    return (double)clock() / CLOCKS_PER_SEC - tstart;
}

static int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void build_adj(void) {
    for (int v = 0; v < N; v++) dg[v] = 0;
    for (int e = 0; e < E; e++) {
        int a = eu[e], b = ev[e];
        adj[(size_t)a * DEG + dg[a]++] = b;
        adj[(size_t)b * DEG + dg[b]++] = a;
    }
}

static int has_edge(int a, int b) {
    const int *p = adj + (size_t)a * DEG;
    for (int s = 0; s < dg[a]; s++)
        if (p[s] == b) return 1;
    return 0;
}

static void adj_replace(int v, int old, int nw) {
    int *p = adj + (size_t)v * DEG;
    for (int s = 0; s < dg[v]; s++)
        if (p[s] == old) {
            p[s] = nw;
            return;
        }
}

static void adj_add(int v, int nw) {
    adj[(size_t)v * DEG + dg[v]++] = nw;
}

/* Edges e1=(a1,b1), e2=(a2,b2) become e1=(a1,b2), e2=(a2,b1). */
static void apply_switch(int e1, int e2, int a1, int b1, int a2, int b2) {
    ev[e1] = b2;
    ev[e2] = b1;
    adj_replace(a1, b1, b2);
    adj_replace(b1, a1, a2);
    adj_replace(a2, b2, b1);
    adj_replace(b2, a2, a1);
}

/* Bad ordered pairs: sum over v of unreached vertices within distance DIAM. */
static int64_t cost_now(void) {
    int Wn = (N + 63) >> 6;
    uint64_t *cu = RA, *nx = RB;
    for (int v = 0; v < N; v++) {
        for (int w = 0; w < Wn; w++) cu[(size_t)v * W + w] = 0;
        cu[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    }
    for (int t = 0; t < DIAM; t++) {
        for (int v = 0; v < N; v++) {
            uint64_t *o = nx + (size_t)v * W;
            const uint64_t *c = cu + (size_t)v * W;
            for (int w = 0; w < Wn; w++) o[w] = c[w];
            const int *p = adj + (size_t)v * DEG;
            for (int s = 0; s < dg[v]; s++) {
                const uint64_t *c2 = cu + (size_t)p[s] * W;
                for (int w = 0; w < Wn; w++) o[w] |= c2[w];
            }
        }
        uint64_t *tmp = cu;
        cu = nx;
        nx = tmp;
    }
    int64_t unr = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        const uint64_t *r = cu + (size_t)v * W;
        for (int w = 0; w < Wn; w++) c += popc64(r[w]);
        unr += N - c;
    }
    return unr;
}

/* Add two vertices a (side A) and b (side B). Each chosen edge (x,y), with
   distinct x and distinct y, becomes (a,y), and (x,b) is added. Degrees are kept. */
static int grow(void) {
    if (N + 2 > CAP || E + DEG > CAP * DEG) return 0;
    stamp++;
    int cnt = 0;
    for (long tr = 0; tr < 200000 && cnt < DEG; tr++) {
        int e = rndint(E);
        int x = eu[e], y = ev[e];
        if (mark[x] == stamp || mark[y] == stamp) continue;
        mark[x] = stamp;
        mark[y] = stamp;
        chosen[cnt++] = e;
    }
    if (cnt < DEG) return 0;
    int a = N, b = N + 1;
    N += 2;
    dg[a] = 0;
    dg[b] = 0;
    for (int i = 0; i < DEG; i++) {
        int e = chosen[i];
        int x = eu[e], y = ev[e];
        eu[e] = a;
        adj_replace(x, y, b);
        adj_replace(y, x, a);
        adj_add(a, y);
        eu[E] = x;
        ev[E] = b;
        E++;
        adj_add(b, x);
    }
    return 1;
}

static int64_t anneal(int64_t cur, int iters) {
    for (int t = 0; t < iters && cur > 0; t++) {
        if (elapsed() > TL) break;
        int e1 = rndint(E), e2 = rndint(E);
        if (e1 == e2) continue;
        int a1 = eu[e1], b1 = ev[e1], a2 = eu[e2], b2 = ev[e2];
        if (a1 == a2 || b1 == b2) continue;
        if (has_edge(a1, b2) || has_edge(a2, b1)) continue;
        apply_switch(e1, e2, a1, b1, a2, b2);
        int64_t c2 = cost_now();
        double temp = 4.0 * (1.0 - (double)t / iters) + 0.1;
        int64_t dl = c2 - cur;
        if (dl <= 0 || rnd01() < exp(-(double)dl / temp))
            cur = c2;
        else
            apply_switch(e1, e2, a1, b2, a2, b1);
    }
    return cur;
}

static void print_fail(void) {
    printf("0 0\n");
}

int main(int argc, char **argv) {
    if (argc < 6) return 1;
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    CAP = atoi(argv[3]);
    unsigned long long seed = strtoull(argv[4], NULL, 10);
    TL = atof(argv[5]);
    tstart = (double)clock() / CLOCKS_PER_SEC;

    rs = (seed + 1) * 0x9E3779B97F4A7C15ULL ^ 0xA24BAED4963EE407ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 8; i++) rnd64();

    if (DEG < 2 || DIAM < 2 || CAP < 8) {
        print_fail();
        return 0;
    }

    int n, m;
    if (scanf("%d %d", &n, &m) != 2 || n < 2 || m < 1 || n > CAP - 2 ||
        (long long)m > (long long)n * DEG) {
        print_fail();
        return 0;
    }

    W = (CAP + 63) >> 6;
    int EC = CAP * DEG + 2 * DEG + 4;
    eu = malloc(sizeof(int) * (size_t)EC);
    ev = malloc(sizeof(int) * (size_t)EC);
    bu = malloc(sizeof(int) * (size_t)EC);
    bv = malloc(sizeof(int) * (size_t)EC);
    ou = malloc(sizeof(int) * (size_t)EC);
    ov = malloc(sizeof(int) * (size_t)EC);
    adj = malloc(sizeof(int) * (size_t)CAP * DEG);
    dg = malloc(sizeof(int) * (size_t)CAP);
    mark = calloc((size_t)CAP, sizeof(int));
    chosen = malloc(sizeof(int) * (size_t)DEG);
    col = malloc(sizeof(int) * (size_t)CAP);
    qbuf = malloc(sizeof(int) * (size_t)CAP);
    RA = malloc(sizeof(uint64_t) * (size_t)CAP * W);
    RB = malloc(sizeof(uint64_t) * (size_t)CAP * W);
    if (!eu || !ev || !bu || !bv || !ou || !ov || !adj || !dg || !mark || !chosen ||
        !col || !qbuf || !RA || !RB) {
        print_fail();
        return 0;
    }

    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || u >= n || v < 0 || v >= n || u == v) {
            print_fail();
            return 0;
        }
        ou[i] = u;
        ov[i] = v;
    }

    /* Degree check, then bipartite colouring and duplicate-edge check. */
    for (int v = 0; v < n; v++) dg[v] = 0;
    for (int i = 0; i < m; i++) {
        dg[ou[i]]++;
        dg[ov[i]]++;
    }
    for (int v = 0; v < n; v++)
        if (dg[v] > DEG) {
            print_fail();
            return 0;
        }
    N = n;
    E = m;
    for (int i = 0; i < m; i++) {
        eu[i] = ou[i];
        ev[i] = ov[i];
    }
    build_adj();
    for (int v = 0; v < n; v++)
        for (int s = 0; s < dg[v]; s++)
            for (int t = s + 1; t < dg[v]; t++)
                if (adj[(size_t)v * DEG + s] == adj[(size_t)v * DEG + t]) {
                    print_fail();
                    return 0;
                }

    for (int v = 0; v < n; v++) col[v] = -1;
    int bad = 0;
    for (int s = 0; s < n && !bad; s++) {
        if (col[s] != -1) continue;
        col[s] = 0;
        int qh = 0, qt = 0;
        qbuf[qt++] = s;
        while (qh < qt && !bad) {
            int u = qbuf[qh++];
            for (int k = 0; k < dg[u]; k++) {
                int w = adj[(size_t)u * DEG + k];
                if (col[w] == -1) {
                    col[w] = 1 - col[u];
                    qbuf[qt++] = w;
                } else if (col[w] == col[u]) {
                    bad = 1;
                    break;
                }
            }
        }
    }
    if (bad) {
        print_fail();
        return 0;
    }
    for (int i = 0; i < m; i++) {
        if (col[ou[i]] == 0) {
            eu[i] = ou[i];
            ev[i] = ov[i];
        } else {
            eu[i] = ov[i];
            ev[i] = ou[i];
        }
    }
    build_adj();
    if (cost_now() != 0) {
        print_fail();
        return 0;
    }

    BN = N;
    BE = E;
    for (int e = 0; e < E; e++) {
        bu[e] = eu[e];
        bv[e] = ev[e];
    }

    /* Grow-and-repair loop. Every attempt starts from the best valid graph. */
    int fails = 0;
    while (elapsed() < TL) {
        N = BN;
        E = BE;
        for (int e = 0; e < E; e++) {
            eu[e] = bu[e];
            ev[e] = bv[e];
        }
        build_adj();
        if (!grow()) {
            if (++fails > 1000) break;
            continue;
        }
        int64_t c = cost_now();
        c = anneal(c, 1500);
        if (c == 0) {
            BN = N;
            BE = E;
            for (int e = 0; e < E; e++) {
                bu[e] = eu[e];
                bv[e] = ev[e];
            }
            fails = 0;
        }
    }

    printf("%d %d\n", BN, BE);
    for (int e = 0; e < BE; e++) printf("%d %d\n", bu[e], bv[e]);
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
# Main build: exact constructions, then voltage lifts, then grow-and-repair.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.9 * time_limit, time_limit - 5.0))
    deadline = start + budget

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

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    cap = lib.moore_bound(d, D)
    wide = d >= 4 and D >= 4

    # Stage 1: voltage-lift annealing (most of the time for wide cases).
    if d >= 3 and D >= 3:
        remaining = deadline - time.monotonic()
        if remaining > 2.0:
            lift_budget = remaining * 0.55 if wide else remaining
            try:
                text = lib.run_c(C_LIFT,
                                 [d, D, best_n, cap, int(seed) & 0x7FFFFFFF,
                                  round(lift_budget, 2)],
                                 timeout=lift_budget + 20.0)
                n2, e2 = lib.parse_graph_text(text)
                consider(n2, e2)
            except Exception:
                pass

    # Stage 2: grow the best valid graph by two vertices and repair by annealing.
    if wide:
        remaining = deadline - time.monotonic()
        if remaining > 2.0:
            try:
                text = lib.run_c(C_GROW,
                                 [d, D, cap, int(seed) & 0x7FFFFFFF, round(remaining, 2)],
                                 stdin_graph=best,
                                 timeout=remaining + 20.0)
                n3, e3 = lib.parse_graph_text(text)
                consider(n3, e3)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
