import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Engine 1 (unchanged from the parent): bi-Cayley voltage annealing over
# Z_m x| Z_k2, in C. Produces a valid lift that is larger than the start.
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
        double mv = rnd01();

        if (K >= 2 && mv < 0.25) {
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


# ----------------------------------------------------------------------------
# Engine 2 (new, bold): growth by edge splitting plus degree-preserving repair.
#
# State: a bipartite graph with max degree DEG. Its A side is the endpoint of
# colour 0, and every edge is stored as (ea = A end, eb = B end).
#
# Growth: pick DEG edges (a_i, b_i) with distinct a_i and distinct b_i. Add a
# new A vertex x and a new B vertex y, then replace each edge by a_i - y and
# x - b_i. Every degree stays <= DEG, x and y have degree DEG, and bipartiteness
# holds. This adds 2 vertices without needing spare degree.
#
# Repair: edge switches (a1,b1),(a2,b2) -> (a1,b2),(a2,b1) keep all degrees and
# bipartiteness. Cost = number of unordered vertex pairs at distance > DEG-
# diameter DIAM, computed with bitset ball expansion. Annealing runs until the
# cost is 0 or the trial budget ends. A success becomes the new best. Failure
# reverts to the best valid graph.
# ----------------------------------------------------------------------------

C_GROW = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXDEG 32
#define ITERS 1500

static int DEG, DIAM, CAP;
static int N, NE;
static int *dg, *adj, *ea, *eb;
static int *bdg, *badj, *bea, *beb;
static int bN, bNE, have_best;
static uint64_t *RA, *RB;
static double TL, tstart;
static int timed_out;
static uint64_t rs;

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + (double)ts.tv_nsec * 1e-9;
}

static double elapsed(void) {
    return now_s() - tstart;
}

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

static uint64_t popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (x * 0x0101010101010101ULL) >> 56;
}

static int has_edge(int a, int b) {
    const int *p = adj + (size_t)a * DEG;
    for (int k = 0; k < dg[a]; k++)
        if (p[k] == b) return 1;
    return 0;
}

static void replace_nb(int v, int old, int nw) {
    int *p = adj + (size_t)v * DEG;
    for (int k = 0; k < dg[v]; k++) {
        if (p[k] == old) {
            p[k] = nw;
            return;
        }
    }
}

/* Edge e1 = (a1,b1), e2 = (a2,b2) become (a1,b2), (a2,b1). Applying it twice undoes it. */
static void do_switch(int e1, int e2) {
    int a1 = ea[e1], a2 = ea[e2], b1 = eb[e1], b2 = eb[e2];
    replace_nb(a1, b1, b2);
    replace_nb(a2, b2, b1);
    replace_nb(b1, a1, a2);
    replace_nb(b2, a2, a1);
    eb[e1] = b2;
    eb[e2] = b1;
}

static int pick_pair(int *e1, int *e2) {
    if (NE < 2) return 0;
    for (int tries = 0; tries < 200; tries++) {
        int x = rndint(NE), y = rndint(NE);
        if (x == y || ea[x] == ea[y] || eb[x] == eb[y]) continue;
        if (has_edge(ea[x], eb[y]) || has_edge(ea[y], eb[x])) continue;
        *e1 = x;
        *e2 = y;
        return 1;
    }
    return 0;
}

/* Number of unordered pairs at distance > DIAM. */
static int64_t bad_pairs(void) {
    int n = N;
    int w = (N + 63) / 64;
    uint64_t *A = RA, *B = RB, *T;
    memset(A, 0, sizeof(uint64_t) * (size_t)n * (size_t)w);
    for (int v = 0; v < n; v++) A[(size_t)v * w + (v >> 6)] |= 1ULL << (v & 63);
    for (int t = 0; t < DIAM; t++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = B + (size_t)v * w;
            memcpy(dst, A + (size_t)v * w, sizeof(uint64_t) * (size_t)w);
            int dv = dg[v];
            for (int k = 0; k < dv; k++) {
                const uint64_t *src = A + (size_t)adj[(size_t)v * DEG + k] * w;
                for (int j = 0; j < w; j++) dst[j] |= src[j];
            }
        }
        T = A;
        A = B;
        B = T;
    }
    int64_t tot = 0;
    size_t words = (size_t)n * (size_t)w;
    for (size_t i = 0; i < words; i++) tot += (int64_t)popc64(A[i]);
    return ((int64_t)n * n - tot) / 2;
}

/* Split DEG edges with distinct endpoints into a new A vertex x and a new B vertex y. */
static int grow_one(void) {
    if (N + 2 > CAP || NE < DEG) return 0;
    int sel[MAXDEG];
    int cnt = 0;
    int tries = 0;
    while (cnt < DEG && tries < 5000) {
        tries++;
        int e = rndint(NE);
        int ok = 1;
        for (int j = 0; j < cnt; j++) {
            if (ea[sel[j]] == ea[e] || eb[sel[j]] == eb[e]) {
                ok = 0;
                break;
            }
        }
        if (ok) sel[cnt++] = e;
    }
    if (cnt < DEG) return 0;

    int x = N, y = N + 1;
    dg[x] = 0;
    dg[y] = 0;
    N += 2;
    for (int j = 0; j < DEG; j++) {
        int e = sel[j];
        int a = ea[e], b = eb[e];
        replace_nb(a, b, y);
        replace_nb(b, a, x);
        adj[(size_t)y * DEG + dg[y]++] = a;
        adj[(size_t)x * DEG + dg[x]++] = b;
        eb[e] = y;
        ea[NE] = x;
        eb[NE] = b;
        NE++;
    }
    return 1;
}

static int64_t anneal(long iters, double T0) {
    int64_t cost = bad_pairs();
    double scale = 0.5 + (double)cost / 200.0;
    for (long t = 0; t < iters && cost > 0; t++) {
        if (elapsed() > TL) {
            timed_out = 1;
            break;
        }
        int e1 = 0, e2 = 0;
        if (!pick_pair(&e1, &e2)) break;
        do_switch(e1, e2);
        int64_t c2 = bad_pairs();
        double T = scale * (T0 * (1.0 - (double)t / (double)iters) + 0.02);
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
            cost = c2;
        } else {
            do_switch(e1, e2);
        }
    }
    return cost;
}

static void save_best(void) {
    memcpy(bdg, dg, sizeof(int) * (size_t)N);
    memcpy(badj, adj, sizeof(int) * (size_t)N * (size_t)DEG);
    memcpy(bea, ea, sizeof(int) * (size_t)NE);
    memcpy(beb, eb, sizeof(int) * (size_t)NE);
    bN = N;
    bNE = NE;
    have_best = 1;
}

static void restore_best(void) {
    N = bN;
    NE = bNE;
    memcpy(dg, bdg, sizeof(int) * (size_t)N);
    memcpy(adj, badj, sizeof(int) * (size_t)N * (size_t)DEG);
    memcpy(ea, bea, sizeof(int) * (size_t)NE);
    memcpy(eb, beb, sizeof(int) * (size_t)NE);
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: d D cap seed time  (graph on stdin)\n");
        return 1;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    CAP = atoi(argv[3]);
    unsigned long long seed = strtoull(argv[4], NULL, 10);
    TL = atof(argv[5]);
    tstart = now_s();

    rs = (seed + 1) * 0x9E3779B97F4A7C15ULL ^ 0xD1B54A32D192ED03ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 8; i++) rnd64();

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 <= 0 || m0 <= 0 || DEG < 3 || DEG > MAXDEG ||
        DIAM < 3) {
        printf("0 0\n");
        return 0;
    }
    if (CAP < n0 + 2) CAP = n0 + 2;

    dg = calloc((size_t)CAP, sizeof(int));
    adj = malloc(sizeof(int) * (size_t)CAP * DEG);
    ea = malloc(sizeof(int) * (size_t)CAP * DEG);
    eb = malloc(sizeof(int) * (size_t)CAP * DEG);
    bdg = malloc(sizeof(int) * (size_t)CAP);
    badj = malloc(sizeof(int) * (size_t)CAP * DEG);
    bea = malloc(sizeof(int) * (size_t)CAP * DEG);
    beb = malloc(sizeof(int) * (size_t)CAP * DEG);
    int WMAX = (CAP + 63) / 64;
    RA = malloc(sizeof(uint64_t) * (size_t)CAP * WMAX);
    RB = malloc(sizeof(uint64_t) * (size_t)CAP * WMAX);
    int *eu = malloc(sizeof(int) * (size_t)m0);
    int *ev = malloc(sizeof(int) * (size_t)m0);
    int *col = malloc(sizeof(int) * (size_t)CAP);
    int *qu = malloc(sizeof(int) * (size_t)CAP);
    if (!dg || !adj || !ea || !eb || !bdg || !badj || !bea || !beb || !RA || !RB ||
        !eu || !ev || !col || !qu) {
        printf("0 0\n");
        return 0;
    }

    int bad = 0;
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) {
            bad = 1;
            break;
        }
        if (u < 0 || v < 0 || u >= n0 || v >= n0 || u == v) {
            bad = 1;
            break;
        }
        if (dg[u] >= DEG || dg[v] >= DEG) {
            bad = 1;
            break;
        }
        adj[(size_t)u * DEG + dg[u]++] = v;
        adj[(size_t)v * DEG + dg[v]++] = u;
        eu[i] = u;
        ev[i] = v;
    }
    if (bad) {
        printf("0 0\n");
        return 0;
    }

    /* Bipartition check by BFS. */
    for (int v = 0; v < n0; v++) col[v] = -1;
    int isbip = 1;
    for (int s = 0; s < n0 && isbip; s++) {
        if (col[s] != -1) continue;
        col[s] = 0;
        int head = 0, tail = 0;
        qu[tail++] = s;
        while (head < tail && isbip) {
            int u = qu[head++];
            for (int k = 0; k < dg[u]; k++) {
                int w = adj[(size_t)u * DEG + k];
                if (col[w] == -1) {
                    col[w] = 1 - col[u];
                    qu[tail++] = w;
                } else if (col[w] == col[u]) {
                    isbip = 0;
                    break;
                }
            }
        }
    }
    if (!isbip) {
        printf("0 0\n");
        return 0;
    }
    for (int i = 0; i < m0; i++) {
        if (col[eu[i]] == 0) {
            ea[i] = eu[i];
            eb[i] = ev[i];
        } else {
            ea[i] = ev[i];
            eb[i] = eu[i];
        }
    }
    N = n0;
    NE = m0;

    timed_out = 0;
    have_best = 0;
    int64_t c0 = bad_pairs();
    if (c0 == 0) {
        save_best();
    } else {
        int64_t c = anneal(20000, 2.0);
        if (c == 0) save_best();
    }

    int per = 1;
    while (have_best && !timed_out && elapsed() < TL) {
        restore_best();
        int grown = 0;
        for (int i = 0; i < per; i++) grown += grow_one();
        if (!grown) break;
        int64_t c = anneal(ITERS, 1.5);
        if (c == 0) {
            save_best();
            if (per < 16) per *= 2;
        } else {
            if (per > 1) per /= 2;
        }
    }

    if (!have_best) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", bN, bNE);
    for (int e = 0; e < bNE; e++) printf("%d %d\n", bea[e], beb[e]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact constructions used as start graphs.
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
# Main build: exact constructions, then the lift engine, then the growth
# engine on the best graph so far, then slack extension.
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

    # Exact constructions. Calibration-style cases return immediately.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    # The W(q) start only matters at D = 4: for D >= 5 it is far smaller than the
    # lift results and costly to build in Python, so skip it there.
    if D == 4 and time.monotonic() < start + budget:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    cap_moore = min(lib.moore_bound(d, D), _MAX_CAP)

    # Phase A: lift search in C, from the best exact start.
    if d >= 3 and D >= 3 and best_n < cap_moore:
        t_a = max(1.0, 0.5 * budget)
        if start + t_a - time.monotonic() > 1.0:
            try:
                text = lib.run_c(C_LIFT,
                                 [d, D, best_n, cap_moore, int(seed) & 0x7FFFFFFF, round(t_a, 2)],
                                 timeout=t_a + 20.0)
                n2, e2 = lib.parse_graph_text(text)
                consider(n2, e2)
            except Exception:
                pass

    # Phase B: growth by edge splitting plus repair, starting from the best graph.
    if d >= 3 and D >= 3:
        remaining = start + budget - time.monotonic()
        if remaining > 2.0:
            gcap = min(cap_moore, int(best_n * 1.25) + 64)
            if gcap > best_n:
                try:
                    text = lib.run_c(C_GROW,
                                     [d, D, gcap, int(seed) & 0x7FFFFFFF, round(remaining, 2)],
                                     stdin_graph=best,
                                     timeout=remaining + 20.0)
                    n2, e2 = lib.parse_graph_text(text)
                    consider(n2, e2)
                except Exception:
                    pass

    # Phase C: use spare degree in the best graph to add vertices.
    if time.monotonic() < final_deadline:
        try:
            n2, e2 = _slack_extend(best[0], best[1], d, D, rng, final_deadline)
            consider(n2, e2)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
