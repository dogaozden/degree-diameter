import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Two-stage program for the D >= 5, d >= 4 targets.
#
# Stage 1 (C_SOURCE): bi-Cayley voltage annealing over Z_m x| Z_k2, as before.
#   It returns a d-regular bipartite lift that is valid for diameter D.
#
# Stage 2 (REPAIR_SOURCE): a different search. It starts from the stage-1 lift
#   (or K_{d,d} if stage 1 fails) and works on the explicit graph, with no group
#   structure. Moves are degree-preserving edge switches, scored by the number of
#   vertex pairs at distance > D. A vertex-insertion move adds one vertex to each
#   side: it removes DEG disjoint edges (a_k, b_k) and joins a_k to a new B-vertex
#   and b_k to a new A-vertex. Degrees stay DEG. When the cost reaches 0 the graph
#   grows by two vertices and annealing resumes. A snapshot of the largest valid
#   graph is kept, and the search restarts from it after a long stall.
#
# Every output is checked with lib.is_valid. consider() keeps the largest valid
# graph seen, so a failed stage never lowers the score.
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
    int nb_ = (K2 - b) % K2;
    int64_t a2 = (M - (PWR[nb_] * (int64_t)AA[x]) % M) % M;
    return (int)(a2 * K2 + nb_);
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


REPAIR_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define PATIENCE 600
#define MAXDEG 60

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

static int DEG, DIAM, CAP, WC, N, NE, ECAP;
static int *nb, *dc, *ea, *eb, *snapA, *snapB;
static int snapN, snapNE, have_snap;
static uint64_t *adj, *RA, *RB;
static double TL, tstart;

static inline int getbit(int v, int u) {
    return (int)((adj[(size_t)v * WC + (u >> 6)] >> (u & 63)) & 1ULL);
}
static inline void setb(int v, int u) {
    adj[(size_t)v * WC + (u >> 6)] |= 1ULL << (u & 63);
}
static inline void clrb(int v, int u) {
    adj[(size_t)v * WC + (u >> 6)] &= ~(1ULL << (u & 63));
}

static inline int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Replace neighbour `old` by `nw` in the row of v. */
static void replace_nb(int v, int old, int nw) {
    int *row = nb + (size_t)v * DEG;
    for (int k = 0; k < DEG; k++) {
        if (row[k] == old) {
            row[k] = nw;
            return;
        }
    }
}

/* Remove (a,b),(c,d) and add (a,d),(c,b). Edge list is updated by the caller. */
static void do_switch(int a, int b, int c, int dd) {
    replace_nb(a, b, dd);
    replace_nb(dd, c, a);
    replace_nb(c, dd, b);
    replace_nb(b, a, c);
    clrb(a, b); clrb(b, a);
    clrb(c, dd); clrb(dd, c);
    setb(a, dd); setb(dd, a);
    setb(c, b); setb(b, c);
}

/* Number of unordered pairs at distance > DIAM. */
static int64_t compute_cost(void) {
    int W = (N + 63) / 64;
    uint64_t *cur = RA, *nxt = RB;
    for (int v = 0; v < N; v++) {
        uint64_t *r = cur + (size_t)v * WC;
        for (int w = 0; w < W; w++) r[w] = 0;
        r[v >> 6] |= 1ULL << (v & 63);
    }
    for (int t = 0; t < DIAM; t++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint64_t *out = nxt + (size_t)v * WC;
            const uint64_t *in = cur + (size_t)v * WC;
            for (int w = 0; w < W; w++) out[w] = in[w];
            const int *row = nb + (size_t)v * DEG;
            for (int k = 0; k < DEG; k++) {
                const uint64_t *src = cur + (size_t)row[k] * WC;
                for (int w = 0; w < W; w++) out[w] |= src[w];
            }
            for (int w = 0; w < W; w++)
                if (out[w] != in[w]) changed = 1;
        }
        uint64_t *tmp = cur;
        cur = nxt;
        nxt = tmp;
        if (!changed) break;
    }
    int64_t cnt = 0;
    for (int v = 0; v < N; v++) {
        const uint64_t *r = cur + (size_t)v * WC;
        for (int w = 0; w < W; w++) cnt += pc64(r[w]);
    }
    return ((int64_t)N * N - cnt) / 2;
}

/* Rebuild neighbour rows and bit rows from the edge list. Returns 0 on a defect. */
static int rebuild(void) {
    int W = (N + 63) / 64;
    for (int v = 0; v < N; v++) {
        dc[v] = 0;
        uint64_t *r = adj + (size_t)v * WC;
        for (int w = 0; w < W; w++) r[w] = 0;
    }
    for (int i = 0; i < NE; i++) {
        int a = ea[i], b = eb[i];
        if (dc[a] >= DEG || dc[b] >= DEG) return 0;
        if (getbit(a, b)) return 0;
        nb[(size_t)a * DEG + dc[a]++] = b;
        nb[(size_t)b * DEG + dc[b]++] = a;
        setb(a, b);
        setb(b, a);
    }
    return 1;
}

static void save_snap(void) {
    snapN = N;
    snapNE = NE;
    have_snap = 1;
    memcpy(snapA, ea, sizeof(int) * (size_t)NE);
    memcpy(snapB, eb, sizeof(int) * (size_t)NE);
}

static int restore_snap(void) {
    N = snapN;
    NE = snapNE;
    memcpy(ea, snapA, sizeof(int) * (size_t)NE);
    memcpy(eb, snapB, sizeof(int) * (size_t)NE);
    return rebuild();
}

/* Add two vertices A (side 0) and B (side 1): take DEG edges with pairwise
   distinct endpoints, (a_k,b_k), and replace them by (a_k,B) and (A,b_k). */
static int grow(void) {
    if (N + 2 > CAP) return 0;
    int idx[MAXDEG];
    int cnt = 0;
    for (int tries = 0; cnt < DEG && tries < 200000; tries++) {
        int i = rndint(NE);
        int ok = 1;
        for (int k = 0; k < cnt; k++) {
            if (ea[idx[k]] == ea[i] || eb[idx[k]] == eb[i]) {
                ok = 0;
                break;
            }
        }
        if (ok) idx[cnt++] = i;
    }
    if (cnt < DEG) return 0;

    int A = N, B = N + 1;
    int ka[MAXDEG], kb[MAXDEG];
    for (int k = 0; k < DEG; k++) {
        ka[k] = ea[idx[k]];
        kb[k] = eb[idx[k]];
    }
    for (int w = 0; w < WC; w++) {
        adj[(size_t)A * WC + w] = 0;
        adj[(size_t)B * WC + w] = 0;
    }
    dc[A] = 0;
    dc[B] = 0;
    for (int k = 0; k < DEG; k++) {
        int a = ka[k], b = kb[k], i = idx[k];
        replace_nb(a, b, B);
        replace_nb(b, a, A);
        clrb(a, b); clrb(b, a);
        setb(a, B); setb(B, a);
        setb(A, b); setb(b, A);
        ea[i] = a;
        eb[i] = B;
        ea[NE + k] = A;
        eb[NE + k] = b;
        nb[(size_t)B * DEG + k] = a;
        nb[(size_t)A * DEG + k] = b;
    }
    NE += DEG;
    N += 2;
    return 1;
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

    rs = (seed + 1) * 0x9E3779B97F4A7C15ULL ^ 0xA0761D6478BD642FULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 8; i++) rnd64();

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) {
        printf("0 0\n");
        return 0;
    }
    if (DEG < 2 || DEG > MAXDEG || DIAM < 2 || n0 < 2 || m0 < 1 || n0 > CAP ||
        (long long)m0 * 2 != (long long)n0 * DEG) {
        printf("0 0\n");
        return 0;
    }

    ECAP = CAP * DEG + 2 * DEG;
    nb = malloc(sizeof(int) * (size_t)CAP * DEG);
    dc = malloc(sizeof(int) * (size_t)CAP);
    ea = malloc(sizeof(int) * (size_t)ECAP);
    eb = malloc(sizeof(int) * (size_t)ECAP);
    snapA = malloc(sizeof(int) * (size_t)ECAP);
    snapB = malloc(sizeof(int) * (size_t)ECAP);
    WC = (CAP + 63) / 64;
    adj = malloc(sizeof(uint64_t) * (size_t)CAP * WC);
    RA = malloc(sizeof(uint64_t) * (size_t)CAP * WC);
    RB = malloc(sizeof(uint64_t) * (size_t)CAP * WC);
    int *eu = malloc(sizeof(int) * (size_t)m0);
    int *evv = malloc(sizeof(int) * (size_t)m0);
    int *col = malloc(sizeof(int) * (size_t)n0);
    int *qu = malloc(sizeof(int) * (size_t)n0);
    if (!nb || !dc || !ea || !eb || !snapA || !snapB || !adj || !RA || !RB ||
        !eu || !evv || !col || !qu) {
        printf("0 0\n");
        return 0;
    }

    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= n0 || v >= n0 || u == v) {
            printf("0 0\n");
            return 0;
        }
        eu[i] = u;
        evv[i] = v;
    }

    /* Degrees and bipartition of the start graph. */
    for (int v = 0; v < n0; v++) dc[v] = 0;
    for (int i = 0; i < m0; i++) {
        int u = eu[i], v = evv[i];
        if (dc[u] >= DEG || dc[v] >= DEG) {
            printf("0 0\n");
            return 0;
        }
        nb[(size_t)u * DEG + dc[u]++] = v;
        nb[(size_t)v * DEG + dc[v]++] = u;
    }
    for (int v = 0; v < n0; v++) col[v] = -1;
    for (int s = 0; s < n0; s++) {
        if (col[s] != -1) continue;
        col[s] = 0;
        int qh = 0, qt = 0;
        qu[qt++] = s;
        while (qh < qt) {
            int u = qu[qh++];
            for (int k = 0; k < DEG; k++) {
                int w = nb[(size_t)u * DEG + k];
                if (col[w] == -1) {
                    col[w] = 1 - col[u];
                    qu[qt++] = w;
                } else if (col[w] == col[u]) {
                    printf("0 0\n");
                    return 0;
                }
            }
        }
    }
    for (int i = 0; i < m0; i++) {
        int u = eu[i], v = evv[i];
        if (col[u] == 0) {
            ea[i] = u;
            eb[i] = v;
        } else {
            ea[i] = v;
            eb[i] = u;
        }
    }
    N = n0;
    NE = m0;
    if (!rebuild()) {
        printf("0 0\n");
        return 0;
    }

    int64_t cost = compute_cost();
    if (cost == 0) save_snap();
    int64_t best_since = cost;
    int stag = 0;
    long long it = 0;

    while (1) {
        if (cost == 0) {
            if (!grow()) break;
            cost = compute_cost();
            best_since = cost;
            stag = 0;
            if (cost == 0 && N > snapN) save_snap();
            continue;
        }
        if ((it & 7) == 0 && now_s() - tstart > TL) break;
        it++;

        int i = rndint(NE), j = rndint(NE);
        if (i == j) continue;
        int a = ea[i], b = eb[i], c = ea[j], dd = eb[j];
        if (a == c || b == dd) continue;
        if (getbit(a, dd) || getbit(c, b)) continue;

        do_switch(a, b, c, dd);
        ea[i] = a;
        eb[i] = dd;
        ea[j] = c;
        eb[j] = b;
        int64_t c2 = compute_cost();
        double T = 0.5 + 0.01 * (double)cost;
        int acc = (c2 <= cost) || (rnd01() < exp(-(double)(c2 - cost) / T));
        if (acc) {
            cost = c2;
            if (cost < best_since) {
                best_since = cost;
                stag = 0;
            } else {
                stag++;
            }
            if (cost == 0 && N > snapN) save_snap();
        } else {
            do_switch(a, dd, c, b);
            ea[i] = a;
            eb[i] = b;
            ea[j] = c;
            eb[j] = dd;
            stag++;
        }

        if (stag > PATIENCE && have_snap) {
            if (!restore_snap()) break;
            cost = compute_cost();
            best_since = cost;
            stag = 0;
        }
    }

    if (!have_snap) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", snapN, snapNE);
    for (int e = 0; e < snapNE; e++) printf("%d %d\n", snapA[e], snapB[e]);
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
# Main build: exact constructions, then the lift search (stage 1), then the
# explicit repair/growth search (stage 2) for D >= 5.
# ----------------------------------------------------------------------------

_MAX_CAP = 2_000_000  # keeps the C allocations and the int parsing safe


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

    # Exact constructions: return immediately on the calibration-style cases.
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

    # Stage 1: group-lift annealing in C (half of the budget when stage 2 applies).
    repair_on = (D >= 5 and d >= 4)
    if d >= 3 and D >= 3:
        remaining = deadline - time.monotonic()
        if remaining > 2.0:
            cap = min(lib.moore_bound(d, D), _MAX_CAP)
            if cap > best_n:
                t1 = remaining * (0.5 if repair_on else 1.0)
                try:
                    text = lib.run_c(C_SOURCE,
                                     [d, D, best_n, cap, int(seed) & 0x7FFFFFFF, round(t1, 2)],
                                     timeout=t1 + 20.0)
                    n1, e1 = lib.parse_graph_text(text)
                    consider(n1, e1)
                except Exception:
                    pass

    # Stage 2: explicit edge-switch annealing with vertex insertion, from the best graph.
    if repair_on:
        remaining = deadline - time.monotonic()
        if remaining > 3.0:
            cap2 = min(lib.moore_bound(d, D), _MAX_CAP, best_n + 3000)
            if cap2 > best_n:
                try:
                    text = lib.run_c(REPAIR_SOURCE,
                                     [d, D, cap2, (int(seed) * 7 + 3) & 0x7FFFFFFF,
                                      round(remaining - 1.0, 2)],
                                     stdin_graph=(best[0], list(best[1])),
                                     timeout=remaining + 20.0)
                    n2, e2 = lib.parse_graph_text(text)
                    consider(n2, e2)
                except Exception:
                    pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
