import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Bold variant for the weak target (D >= 5, d >= 6):
#
#   Stage 1: the proven bi-Cayley voltage annealer (C_SOURCE, unchanged) builds
#            a lift-based valid graph on about 60% of the search budget.
#   Stage 2: C_GROW takes that graph as an edge list and grows it by repeated
#            "add two vertices" moves. Each move removes a matching of d edges,
#            attaches x to one end of each and y to the other end, and then
#            repairs the diameter with double-edge swaps (bipartition preserved)
#            under simulated annealing. Failed attempts restore the last valid
#            snapshot.
#
# Every stage returns a valid graph or nothing. The result is checked with
# lib.is_valid, and the fallbacks are K_{d,d} and the exact constructions.
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


C_GROW = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define ANN_ITERS 1500

static int DEG, DIAM, CAPV, CAPE, WM;
static int NV, NE;
static int *adj, *dg, *side, *ea, *eb;
static uint64_t *RA, *RB;
static int *sadj, *sdg, *sside, *sea, *seb;
static int sNV, sNE;
static int *mk, stamp;
static int *chosen, *ca, *cb;
static uint64_t rs;
static double TL;
static clock_t t0;

static double elapsed(void) {
    return (double)(clock() - t0) / CLOCKS_PER_SEC;
}
static uint64_t rnd64(void) {
    uint64_t x = rs;
    x ^= x << 13;
    x ^= x >> 7;
    x ^= x << 17;
    rs = x;
    return x;
}
static double rnd01(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}
static int rndint(int n) {
    return (int)(rnd64() % (uint64_t)n);
}
static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void adj_remove(int v, int u) {
    int *a = adj + (size_t)v * DEG;
    for (int i = 0; i < dg[v]; i++) {
        if (a[i] == u) {
            a[i] = a[dg[v] - 1];
            dg[v]--;
            return;
        }
    }
}
static void adj_add(int v, int u) {
    adj[(size_t)v * DEG + dg[v]] = u;
    dg[v]++;
}
static int adj_has(int v, int u) {
    const int *a = adj + (size_t)v * DEG;
    for (int i = 0; i < dg[v]; i++)
        if (a[i] == u) return 1;
    return 0;
}

/* Replace edges e1, e2 (current endpoints) by (na1,nb1) and (na2,nb2). */
static void rewire2(int e1, int e2, int na1, int nb1, int na2, int nb2) {
    adj_remove(ea[e1], eb[e1]);
    adj_remove(eb[e1], ea[e1]);
    adj_remove(ea[e2], eb[e2]);
    adj_remove(eb[e2], ea[e2]);
    adj_add(na1, nb1);
    adj_add(nb1, na1);
    adj_add(na2, nb2);
    adj_add(nb2, na2);
    ea[e1] = na1;
    eb[e1] = nb1;
    ea[e2] = na2;
    eb[e2] = nb2;
}

/* Number of ordered pairs (v,w) with dist(v,w) > DIAM (bipartite, so 0 iff valid). */
static int64_t cost_full(void) {
    int w = (NV + 63) / 64;
    for (int v = 0; v < NV; v++) {
        uint64_t *r = RA + (size_t)v * WM;
        for (int k = 0; k < w; k++) r[k] = 0;
        r[v >> 6] |= 1ULL << (v & 63);
    }
    uint64_t *cu = RA, *nx = RB;
    for (int t = 0; t < DIAM; t++) {
        for (int v = 0; v < NV; v++) {
            uint64_t *o = nx + (size_t)v * WM;
            const uint64_t *c = cu + (size_t)v * WM;
            for (int k = 0; k < w; k++) o[k] = c[k];
            for (int i = 0; i < dg[v]; i++) {
                const uint64_t *c2 = cu + (size_t)adj[(size_t)v * DEG + i] * WM;
                for (int k = 0; k < w; k++) o[k] |= c2[k];
            }
        }
        uint64_t *tmp = cu;
        cu = nx;
        nx = tmp;
    }
    int64_t miss = 0;
    for (int v = 0; v < NV; v++) {
        const uint64_t *c = cu + (size_t)v * WM;
        int p = 0;
        for (int k = 0; k < w; k++) p += popc(c[k]);
        miss += NV - p;
    }
    return miss;
}

/* Simulated annealing with double-edge swaps; returns the final cost. */
static int64_t anneal(int64_t iters, double T0, double T1) {
    int64_t cost = cost_full();
    if (NE < 2) return cost;
    for (int64_t it = 0; it < iters && cost > 0; it++) {
        if ((it & 7) == 0 && elapsed() > TL) break;
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        int e1 = rndint(NE), e2 = rndint(NE);
        if (e1 == e2) continue;
        int a1 = ea[e1], b1 = eb[e1], a2 = ea[e2], b2 = eb[e2];
        if (a1 == a2 || b1 == b2) continue;
        if (adj_has(a1, b2) || adj_has(a2, b1)) continue;
        rewire2(e1, e2, a1, b2, a2, b1);
        int64_t c2 = cost_full();
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
            cost = c2;
        } else {
            rewire2(e1, e2, a1, b1, a2, b2);
        }
    }
    return cost;
}

/* Remove a matching of DEG edges and add two vertices x (side 0), y (side 1). */
static int add_pair(void) {
    if (NE < DEG || NV + 2 > CAPV) return 0;
    stamp++;
    int cnt = 0, tries = 0;
    while (cnt < DEG && tries < 60 * DEG) {
        tries++;
        int e = rndint(NE);
        int a = ea[e], b = eb[e];
        if (mk[a] == stamp || mk[b] == stamp) continue;
        mk[a] = stamp;
        mk[b] = stamp;
        chosen[cnt] = e;
        ca[cnt] = a;
        cb[cnt] = b;
        cnt++;
    }
    if (cnt < DEG) return 0;
    for (int i = 0; i < DEG; i++) {
        adj_remove(ca[i], cb[i]);
        adj_remove(cb[i], ca[i]);
    }
    int x = NV, y = NV + 1;
    NV += 2;
    side[x] = 0;
    side[y] = 1;
    dg[x] = 0;
    dg[y] = 0;
    for (int i = 0; i < DEG; i++) {
        int a = ca[i], b = cb[i], e = chosen[i];
        adj_add(a, y);
        adj_add(y, a);
        ea[e] = a;
        eb[e] = y;
        adj_add(x, b);
        adj_add(b, x);
        ea[NE] = x;
        eb[NE] = b;
        NE++;
    }
    return 1;
}

static void save_snap(void) {
    sNV = NV;
    sNE = NE;
    memcpy(sadj, adj, sizeof(int) * (size_t)CAPV * DEG);
    memcpy(sdg, dg, sizeof(int) * (size_t)CAPV);
    memcpy(sside, side, sizeof(int) * (size_t)CAPV);
    memcpy(sea, ea, sizeof(int) * (size_t)NE);
    memcpy(seb, eb, sizeof(int) * (size_t)NE);
}

static void restore_snap(void) {
    NV = sNV;
    NE = sNE;
    memcpy(adj, sadj, sizeof(int) * (size_t)CAPV * DEG);
    memcpy(dg, sdg, sizeof(int) * (size_t)CAPV);
    memcpy(side, sside, sizeof(int) * (size_t)CAPV);
    memcpy(ea, sea, sizeof(int) * (size_t)NE);
    memcpy(eb, seb, sizeof(int) * (size_t)NE);
}

static void fail_out(void) {
    printf("0 0\n");
    exit(0);
}

int main(int argc, char **argv) {
    if (argc < 6) return 1;
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    int cap = atoi(argv[3]);
    unsigned long long seed = strtoull(argv[4], NULL, 10);
    TL = atof(argv[5]);
    t0 = clock();
    rs = (seed + 1) * 0x9E3779B97F4A7C15ULL ^ 0x2545F4914F6CDD1DULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 8; i++) rnd64();

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || m < 0 || DEG < 2 || DEG > 64) fail_out();
    int *ru = malloc(sizeof(int) * (size_t)(m + 1));
    int *rv = malloc(sizeof(int) * (size_t)(m + 1));
    if (!ru || !rv) fail_out();
    for (int i = 0; i < m; i++)
        if (scanf("%d %d", &ru[i], &rv[i]) != 2) fail_out();

    CAPV = cap > n + 2 ? cap : n + 2;
    CAPE = CAPV * DEG;
    WM = (CAPV + 63) / 64;
    adj = malloc(sizeof(int) * (size_t)CAPV * DEG);
    dg = calloc((size_t)CAPV, sizeof(int));
    side = malloc(sizeof(int) * (size_t)CAPV);
    ea = malloc(sizeof(int) * (size_t)CAPE);
    eb = malloc(sizeof(int) * (size_t)CAPE);
    RA = malloc(sizeof(uint64_t) * (size_t)CAPV * WM);
    RB = malloc(sizeof(uint64_t) * (size_t)CAPV * WM);
    sadj = malloc(sizeof(int) * (size_t)CAPV * DEG);
    sdg = malloc(sizeof(int) * (size_t)CAPV);
    sside = malloc(sizeof(int) * (size_t)CAPV);
    sea = malloc(sizeof(int) * (size_t)CAPE);
    seb = malloc(sizeof(int) * (size_t)CAPE);
    mk = calloc((size_t)CAPV, sizeof(int));
    chosen = malloc(sizeof(int) * (size_t)DEG);
    ca = malloc(sizeof(int) * (size_t)DEG);
    cb = malloc(sizeof(int) * (size_t)DEG);
    if (!adj || !dg || !side || !ea || !eb || !RA || !RB || !sadj || !sdg || !sside ||
        !sea || !seb || !mk || !chosen || !ca || !cb)
        fail_out();

    NV = n;
    NE = 0;
    /* Build adjacency with degree and simplicity checks. */
    for (int i = 0; i < m; i++) {
        int u = ru[i], v = rv[i];
        if (u < 0 || u >= n || v < 0 || v >= n || u == v) fail_out();
        if (dg[u] >= DEG || dg[v] >= DEG) fail_out();
        if (adj_has(u, v)) fail_out();
        adj_add(u, v);
        adj_add(v, u);
    }
    /* Bipartition by BFS. */
    for (int v = 0; v < n; v++) side[v] = -1;
    int *q = malloc(sizeof(int) * (size_t)n);
    if (!q) fail_out();
    for (int s = 0; s < n; s++) {
        if (side[s] >= 0) continue;
        int head = 0, tail = 0;
        side[s] = 0;
        q[tail++] = s;
        while (head < tail) {
            int v = q[head++];
            for (int i = 0; i < dg[v]; i++) {
                int w = adj[(size_t)v * DEG + i];
                if (side[w] < 0) {
                    side[w] = 1 - side[v];
                    q[tail++] = w;
                } else if (side[w] == side[v]) {
                    fail_out();
                }
            }
        }
    }
    for (int i = 0; i < m; i++) {
        int u = ru[i], v = rv[i];
        if (side[u] == 0) {
            ea[NE] = u;
            eb[NE] = v;
        } else {
            ea[NE] = v;
            eb[NE] = u;
        }
        NE++;
    }

    int64_t cost = cost_full();
    if (cost != 0) cost = anneal(20000, 3.0, 0.2);
    if (cost != 0) fail_out();
    save_snap();

    while (elapsed() < TL) {
        if (!add_pair()) continue;
        int64_t c = anneal(ANN_ITERS, 3.0, 0.2);
        if (c == 0) save_snap();
        else restore_snap();
    }

    printf("%d %d\n", sNV, sNE);
    for (int i = 0; i < sNE; i++) printf("%d %d\n", sea[i], seb[i]);
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
# Main build.
# ----------------------------------------------------------------------------

_MAX_CAP = 2_000_000  # keeps the C allocations and the int parsing safe


def _run_grow(d, D, n, edges, seed, seconds):
    """Grow a valid start graph with C_GROW. Returns (n, edges) or None."""
    cap = min(lib.moore_bound(d, D), n + 800, _MAX_CAP)
    if cap < n + 2:
        return None
    text = lib.run_c(C_GROW, [d, D, cap, int(seed) & 0x7FFFFFFF, round(seconds, 2)],
                     stdin_graph=(n, edges), timeout=seconds + 20.0)
    return lib.parse_graph_text(text)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.88 * time_limit, time_limit - 7.0))
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

    # Stage 1: voltage-lift annealing in C.
    # The bold path (D >= 5, d >= 6) gives stage 1 about 60% of the budget and
    # reserves the rest for the growth stage.
    bold = d >= 6 and D >= 5
    if d >= 3 and D >= 3:
        remaining = deadline - time.monotonic()
        if remaining > 2.0:
            cap = min(lib.moore_bound(d, D), _MAX_CAP)
            if cap > best_n:
                s1 = round(remaining * (0.6 if bold else 1.0), 2)
                try:
                    text = lib.run_c(C_SOURCE,
                                     [d, D, best_n, cap, int(seed) & 0x7FFFFFFF, s1],
                                     timeout=s1 + 20.0)
                    n2, e2 = lib.parse_graph_text(text)
                    consider(n2, e2)
                except Exception:
                    pass

    # Stage 2 (bold): grow the best valid graph with double-edge-swap annealing.
    if bold:
        rem = deadline - time.monotonic()
        if rem > 4.0 and best_n >= 2:
            try:
                res = _run_grow(d, D, best_n, best[1], seed, rem - 2.0)
                if res is not None:
                    consider(res[0], res[1])
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
