import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Combined program: bi-Cayley voltage annealing over Z_m x| Z_k2, then
# split-growth on the best regular graph, all in C.
#
# Inherited from the parent:
#   - bandit over base sizes k (k <= 4), near-miss continuation, iterated local
#     search memory, voltage-exchange moves, wall-clock timing.
#   - exact start graphs (PG(2,q), W(q)) and K_{d,d} as a fallback.
#
# New in this version:
#   - Split-growth (C): a regular bipartite graph on n vertices is grown to n+2
#     by splitting a matching of d edges (a_i, b_i) into a_i - w and b_i - w2,
#     with w on side 1 and w2 on side 0. Every degree stays d and bipartiteness
#     is kept. The new graph is then repaired by degree-preserving double-edge
#     swaps (annealing on the count of pairs at distance > D, computed with
#     bitset BFS). Failed attempts are rolled back. This replaces the parent's
#     slack extension, which can never fire on a regular graph.
#   - The lift search gets LIFT_FRAC of the time, and split-growth gets the rest.
#
# Every candidate that is returned passes lib.is_valid.
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
#define MAXDEG 64
#define LIFT_FRAC 0.6
#define SPLIT_STEPS 400
#define SPLIT_CAP_MAX 20000

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
static double TL, TOTAL;
static int *bestnbr;
static int best_stride, best_K, best_G;
static int have_best;
static int64_t LASTCOST;

/* Iterated-local-search memory: best near-miss state seen so far. */
static int have_near;
static int nr_K, nr_M, nr_K2, nr_R, nr_G, nr_N;
static int64_t nr_cost;
static int *nr_lay, *nr_vol;

static long long g_found;
static double tr_arr[MAXK + 1], wn_arr[MAXK + 1];

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
            /* layer-swap move: exchange two permutation entries at one layer */
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
            /* voltage exchange: swap voltages of base vertex i between two layers */
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

/* Lift search: runs until elapsed() reaches TL. Updates g_found and the best lift. */
static void lift_search(void) {
    while (elapsed() < TL) {
        if (g_found >= CAP) break;
        int k = 1;
        int ok = 0;

        if (have_near && nr_N > g_found && rnd01() < 0.5) {
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
            k = pick_k(tr_arr, wn_arr);
            int64_t base = g_found / (2 * k);
            int64_t span = base / 8 + 1;
            if (span < 2) span = 2;
            int64_t target = base + 1 + rndint((int)span);
            if (target < 2) target = 2;
            if (!sample_group(target)) continue;
            long long Nn = 2LL * k * G;
            if (Nn <= g_found || Nn > CAP) continue;

            K = k;
            N = (int)Nn;
            FULL = (uint8_t)((1u << (2 * K)) - 1);
            setup_group();
            tr_arr[k] += 1.0;
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
            if (!have_near || LASTCOST < nr_cost || nr_N <= g_found) save_near();
        }

        if (ok) {
            wn_arr[k] += 1.0;
            g_found = N;
            memcpy(bestnbr, nbr, sizeof(int) * (size_t)DEG * N);
            best_stride = N;
            best_K = K;
            best_G = G;
            have_best = 1;
            have_near = 0;
        }
        if (timed_out) break;
    }
}

/* ------------------------------------------------------------------------ */
/* Split-growth on a DEG-regular bipartite graph.                            */
/* Side 0 vertices have colour 0, side 1 vertices colour 1.                  */
/* ------------------------------------------------------------------------ */

static int GN, SCAP;
static int *SA, *SAbak, *SAtmp;
static unsigned char *SC, *SCbak;
static uint64_t *RX, *RY;

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int find_slot(int v, int target) {
    const int *row = SA + (size_t)v * DEG;
    for (int l = 0; l < DEG; l++)
        if (row[l] == target) return l;
    return -1;
}

/* Number of ordered vertex pairs at distance > DIAM (0 means valid). Bitset BFS. */
static int64_t split_cost(void) {
    int n = GN;
    int W = (n + 63) >> 6;
    uint64_t *x = RX, *y = RY;
    memset(x, 0, sizeof(uint64_t) * (size_t)n * (size_t)W);
    for (int v = 0; v < n; v++) x[(size_t)v * W + (v >> 6)] = 1ULL << (v & 63);
    for (int t = 0; t < DIAM; t++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = y + (size_t)v * W;
            const uint64_t *src = x + (size_t)v * W;
            memcpy(dst, src, sizeof(uint64_t) * (size_t)W);
            const int *row = SA + (size_t)v * DEG;
            for (int l = 0; l < DEG; l++) {
                const uint64_t *s2 = x + (size_t)row[l] * W;
                for (int w = 0; w < W; w++) dst[w] |= s2[w];
            }
        }
        uint64_t *tmp = x;
        x = y;
        y = tmp;
    }
    int64_t cost = 0;
    for (int v = 0; v < n; v++) {
        const uint64_t *r = x + (size_t)v * W;
        int c = 0;
        for (int w = 0; w < W; w++) c += pc64(r[w]);
        cost += n - c;
    }
    return cost;
}

/* Degree- and bipartition-preserving double-edge swap:
   (a,b),(c,d) -> (a,d),(c,b) with a,c on side 0 and b,d on side 1. */
static int swap_move(void) {
    int n = GN;
    for (int tries = 0; tries < 2000; tries++) {
        int a = rndint(n), c = rndint(n);
        if (a == c || SC[a] != 0 || SC[c] != 0) continue;
        int la = rndint(DEG), lc = rndint(DEG);
        int b = SA[(size_t)a * DEG + la];
        int dd = SA[(size_t)c * DEG + lc];
        if (b == dd) continue;
        if (find_slot(a, dd) >= 0 || find_slot(c, b) >= 0) continue;
        int sb = find_slot(b, a);
        int sd = find_slot(dd, c);
        if (sb < 0 || sd < 0) continue;
        SA[(size_t)a * DEG + la] = dd;
        SA[(size_t)c * DEG + lc] = b;
        SA[(size_t)b * DEG + sb] = c;
        SA[(size_t)dd * DEG + sd] = a;
        return 1;
    }
    return 0;
}

/* Split a matching of DEG edges (a_i,b_i), a_i side 0, b_i side 1:
   a_i - b_i  becomes  a_i - w  and  b_i - w2,
   with new w on side 1 and new w2 on side 0. Adds 2 vertices, keeps every degree DEG. */
static int split_move(void) {
    int n = GN;
    int as[MAXDEG], ls[MAXDEG], bs[MAXDEG];
    int k = 0;
    for (int tries = 0; tries < 5000 && k < DEG; tries++) {
        int a = rndint(n);
        if (SC[a] != 0) continue;
        int l = rndint(DEG);
        int b = SA[(size_t)a * DEG + l];
        int dup = 0;
        for (int j = 0; j < k; j++) {
            if (as[j] == a || bs[j] == b) {
                dup = 1;
                break;
            }
        }
        if (dup) continue;
        as[k] = a;
        ls[k] = l;
        bs[k] = b;
        k++;
    }
    if (k < DEG) return 0;
    int w = n, w2 = n + 1;
    for (int i = 0; i < DEG; i++) {
        int a = as[i], b = bs[i];
        int sb = find_slot(b, a);
        SA[(size_t)a * DEG + ls[i]] = w;
        SA[(size_t)b * DEG + sb] = w2;
        SA[(size_t)w * DEG + i] = a;
        SA[(size_t)w2 * DEG + i] = b;
    }
    SC[w] = 1;
    SC[w2] = 0;
    GN = n + 2;
    return 1;
}

/* Grow the current valid graph (SA, SC, GN) by repeated split + repair. */
static void split_phase(void) {
    while (elapsed() < TOTAL) {
        int prevN = GN;
        if (GN + 2 > SCAP) break;
        memcpy(SAbak, SA, sizeof(int) * (size_t)DEG * (size_t)prevN);
        memcpy(SCbak, SC, (size_t)prevN);
        if (!split_move()) continue;

        int64_t cost = split_cost();
        double c0 = cost > 1 ? (double)cost : 1.0;
        for (int t = 0; t < SPLIT_STEPS && cost != 0; t++) {
            if (elapsed() > TOTAL) break;
            double temp = 0.02 * c0 * (1.0 - (double)t / SPLIT_STEPS);
            if (temp < 0.3) temp = 0.3;
            memcpy(SAtmp, SA, sizeof(int) * (size_t)DEG * (size_t)GN);
            if (!swap_move()) continue;
            int64_t c2 = split_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
            } else {
                memcpy(SA, SAtmp, sizeof(int) * (size_t)DEG * (size_t)GN);
            }
        }
        if (cost != 0) {
            GN = prevN;
            memcpy(SA, SAbak, sizeof(int) * (size_t)DEG * (size_t)prevN);
            memcpy(SC, SCbak, (size_t)prevN);
        }
    }
}

static void print_graph(int n) {
    long long m = 0;
    for (int u = 0; u < n; u++)
        if (SC[u] == 0) m += DEG;
    printf("%d %lld\n", n, m);
    for (int u = 0; u < n; u++) {
        if (SC[u] != 0) continue;
        for (int l = 0; l < DEG; l++)
            printf("%d %d\n", u, SA[(size_t)u * DEG + l]);
    }
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
    TOTAL = atof(argv[6]);
    TL = TOTAL * LIFT_FRAC;
    tstart = now_s();

    rs = (seed + 1) * 0x9E3779B97F4A7C15ULL ^ 0xD1B54A32D192ED03ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 8; i++) rnd64();
    for (int x = 0; x < 256; x++) {
        int c = 0;
        for (int y = x; y; y >>= 1) c += y & 1;
        POP[x] = (uint8_t)c;
    }

    if (DEG < 3 || DEG > MAXDEG || DIAM < 3 || CAP < 8) {
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

    g_found = best0;
    lift_search();
    if (!have_best) {
        TL = TOTAL;
        lift_search();
    }
    if (!have_best) {
        printf("0 0\n");
        return 0;
    }

    /* Split-growth from the best lift. */
    int N0 = best_stride;
    int lim = SPLIT_CAP_MAX;
    if (lim < N0) lim = N0;
    SCAP = lim < CAP ? lim : CAP;
    if (SCAP < N0) SCAP = N0;
    int words = (SCAP + 2 + 63) >> 6;
    SA = malloc(sizeof(int) * (size_t)DEG * (size_t)(SCAP + 2));
    SAbak = malloc(sizeof(int) * (size_t)DEG * (size_t)(SCAP + 2));
    SAtmp = malloc(sizeof(int) * (size_t)DEG * (size_t)(SCAP + 2));
    SC = malloc((size_t)(SCAP + 2));
    SCbak = malloc((size_t)(SCAP + 2));
    RX = malloc(sizeof(uint64_t) * (size_t)(SCAP + 2) * (size_t)words);
    RY = malloc(sizeof(uint64_t) * (size_t)(SCAP + 2) * (size_t)words);
    if (!SA || !SAbak || !SAtmp || !SC || !SCbak || !RX || !RY) {
        /* Could not allocate the growth buffers: print the lift graph directly. */
        GN = N0;
        for (int u = 0; u < N0; u++) {
            for (int l = 0; l < DEG; l++) {
                int v = bestnbr[(size_t)l * N0 + u];
                (void)v;
            }
        }
        printf("%d %lld\n", N0, (long long)N0 / 2 * DEG);
        int KG = best_K * best_G;
        for (int u = 0; u < KG; u++)
            for (int l = 0; l < DEG; l++)
                printf("%d %d\n", u, bestnbr[(size_t)l * N0 + u]);
        return 0;
    }

    for (int u = 0; u < N0; u++) {
        for (int l = 0; l < DEG; l++)
            SA[(size_t)u * DEG + l] = bestnbr[(size_t)l * N0 + u];
        SC[u] = (unsigned char)((u / best_G) >= best_K ? 1 : 0);
    }
    GN = N0;

    split_phase();
    print_graph(GN);
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
# Slack extension: add new vertices using spare degree. Useful only for
# non-regular starts (for example PG(2,q) with d > q + 1).
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
# Main build: exact constructions, then the C lift search and split-growth,
# then slack extension for non-regular starts.
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

    # Main search, entirely in C: lift search, then split-growth.
    if d >= 3 and D >= 3:
        remaining = start + budget - time.monotonic()
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

    # Use spare degree in the best graph to add vertices (non-regular starts only).
    if time.monotonic() < final_deadline:
        try:
            n2, e2 = _slack_extend(best[0], best[1], d, D, rng, final_deadline)
            consider(n2, e2)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
