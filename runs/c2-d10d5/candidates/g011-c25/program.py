import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Program: bi-Cayley voltage search (C_SOURCE) followed by an unstructured
# repair search (C_REPAIR).
#
# The bold change: after the structured search, the best lift is treated as a
# general bipartite graph. Two new vertices are inserted by freeing d disjoint
# edges and re-wiring them through the new vertices. Degree-preserving 2-switch
# annealing then drives the number of unreachable ordered pairs to zero. Each
# success adds two vertices and is saved. Every candidate passes lib.is_valid
# before it is kept, and K_{d,d} stays the fallback.
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


C_REPAIR = r"""
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
static int N, NE;
static int *EA, *EB;      /* edges; EA always on side 0, EB on side 1 */
static int *adj, *dg;     /* adj[v*DEG + k] */
static int *side, *mark, *perm;
static int stamp;
static uint64_t *RA, *RB;
static int *bestEA, *bestEB;
static int bestN, bestNE;
static double TL;
static clock_t t0;

static double elapsed(void) {
    return (double)(clock() - t0) / CLOCKS_PER_SEC;
}

static int has_edge(int u, int v) {
    const int *row = adj + (size_t)u * DEG;
    for (int k = 0; k < dg[u]; k++)
        if (row[k] == v) return 1;
    return 0;
}

static void adj_replace(int u, int old, int nw) {
    int *row = adj + (size_t)u * DEG;
    for (int k = 0; k < dg[u]; k++)
        if (row[k] == old) {
            row[k] = nw;
            return;
        }
}

static void adj_add(int u, int v) {
    adj[(size_t)u * DEG + dg[u]] = v;
    dg[u]++;
}

/* Rebuild adjacency from the edge list (degrees already checked <= DEG). */
static void rebuild_adj(void) {
    for (int v = 0; v < N; v++) dg[v] = 0;
    for (int e = 0; e < NE; e++) {
        adj_add(EA[e], EB[e]);
        adj_add(EB[e], EA[e]);
    }
}

/* Two-colour the graph; returns 1 if bipartite, filling side[]. Uses perm[] as a stack. */
static int bipartize(void) {
    for (int v = 0; v < N; v++) side[v] = -1;
    for (int s = 0; s < N; s++) {
        if (side[s] != -1) continue;
        side[s] = 0;
        int top = 0;
        perm[top++] = s;
        while (top > 0) {
            int u = perm[--top];
            for (int k = 0; k < dg[u]; k++) {
                int v = adj[(size_t)u * DEG + k];
                if (side[v] == -1) {
                    side[v] = 1 - side[u];
                    perm[top++] = v;
                } else if (side[v] == side[u]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

/* 2-switch of edges i=(a,b) and j=(c,e) into (a,e) and (c,b). Applying it twice undoes it. */
static void sw(int i, int j) {
    int a = EA[i], b = EB[i], c = EA[j], e = EB[j];
    adj_replace(a, b, e);
    adj_replace(e, c, a);
    adj_replace(c, e, b);
    adj_replace(b, a, c);
    EB[i] = e;
    EB[j] = b;
}

/* Number of ordered unreachable pairs within distance DIAM. */
static int64_t cost_of(void) {
    uint64_t *R = RA, *Nx = RB;
    memset(R, 0, sizeof(uint64_t) * (size_t)N * W);
    for (int v = 0; v < N; v++) R[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int t = 0; t < DIAM; t++) {
        for (int v = 0; v < N; v++) {
            uint64_t *out = Nx + (size_t)v * W;
            const uint64_t *in = R + (size_t)v * W;
            memcpy(out, in, sizeof(uint64_t) * W);
            for (int k = 0; k < dg[v]; k++) {
                const uint64_t *s = R + (size_t)adj[(size_t)v * DEG + k] * W;
                for (int w = 0; w < W; w++) out[w] |= s[w];
            }
        }
        uint64_t *tmp = R;
        R = Nx;
        Nx = tmp;
    }
    int64_t cnt = 0;
    for (int v = 0; v < N; v++) {
        const uint64_t *row = R + (size_t)v * W;
        int64_t c = 0;
        for (int w = 0; w < W; w++) c += __builtin_popcountll(row[w]);
        cnt += N - c;
    }
    return cnt;
}

/* Free d vertex-disjoint edges, attach new vertex x (side 0) and y (side 1) through them.
   Every degree is preserved. Returns 0 (state untouched) if no d disjoint edges exist. */
static int insert_pair(void) {
    stamp++;
    for (int e = 0; e < NE; e++) perm[e] = e;
    for (int e = NE - 1; e > 0; e--) {
        int j = rndint(e + 1);
        int t = perm[e];
        perm[e] = perm[j];
        perm[j] = t;
    }
    int chosen[64];
    int nc = 0;
    for (int q = 0; q < NE && nc < DEG; q++) {
        int e = perm[q];
        int a = EA[e], b = EB[e];
        if (mark[a] == stamp || mark[b] == stamp) continue;
        mark[a] = stamp;
        mark[b] = stamp;
        chosen[nc++] = e;
    }
    if (nc < DEG) return 0;

    int x = N, y = N + 1;
    side[x] = 0;
    side[y] = 1;
    dg[x] = 0;
    dg[y] = 0;
    for (int k = 0; k < DEG; k++) {
        int e = chosen[k];
        int a = EA[e], b = EB[e];
        adj_replace(a, b, y);
        adj_replace(b, a, x);
        EA[e] = x;          /* edge becomes (x, b) */
        adj_add(x, b);
        adj_add(y, a);
        EA[NE] = a;         /* new edge (a, y) */
        EB[NE] = y;
        NE++;
    }
    N += 2;
    return 1;
}

/* Degree-preserving annealing on 2-switches. Returns 1 on success (cost 0),
   0 if the move budget ran out, -1 on timeout. */
static int anneal(int iters) {
    int64_t cur = cost_of();
    if (cur == 0) return 1;
    double T0 = 2.0 + 0.02 * (double)cur;
    for (int t = 0; t < iters; t++) {
        if ((t & 15) == 0 && elapsed() > TL) return -1;
        int i = rndint(NE), j = rndint(NE);
        if (i == j) continue;
        int a = EA[i], b = EB[i], c = EA[j], e = EB[j];
        if (a == c || b == e) continue;
        if (has_edge(a, e) || has_edge(c, b)) continue;
        sw(i, j);
        int64_t nc = cost_of();
        if (nc == 0) return 1;
        double T = T0 * (1.0 - (double)t / iters) + 0.05;
        if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
            cur = nc;
        } else {
            sw(i, j);
        }
    }
    return 0;
}

static void save_best(void) {
    bestN = N;
    bestNE = NE;
    memcpy(bestEA, EA, sizeof(int) * (size_t)NE);
    memcpy(bestEB, EB, sizeof(int) * (size_t)NE);
}

static void restore_best(void) {
    N = bestN;
    NE = bestNE;
    memcpy(EA, bestEA, sizeof(int) * (size_t)NE);
    memcpy(EB, bestEB, sizeof(int) * (size_t)NE);
    rebuild_adj();
}

int main(int argc, char **argv) {
    if (argc < 6) {
        printf("0 0\n");
        return 0;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    CAP = atoi(argv[3]);
    unsigned long long seed = strtoull(argv[4], NULL, 10);
    TL = atof(argv[5]);
    t0 = clock();

    rs = (seed + 7) * 0x9E3779B97F4A7C15ULL ^ 0x94D049BB133111EBULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 8; i++) rnd64();

    if (DEG < 3 || DEG > 64 || DIAM < 2 || CAP < 4) {
        printf("0 0\n");
        return 0;
    }

    int n, m;
    if (scanf("%d %d", &n, &m) != 2 || n < 2 || n > CAP || m < 0) {
        printf("0 0\n");
        return 0;
    }
    W = (CAP + 63) / 64;
    size_t ecap = (size_t)CAP * DEG;
    if ((size_t)m > ecap / 2) {
        printf("0 0\n");
        return 0;
    }
    EA = malloc(sizeof(int) * ecap);
    EB = malloc(sizeof(int) * ecap);
    bestEA = malloc(sizeof(int) * ecap);
    bestEB = malloc(sizeof(int) * ecap);
    perm = malloc(sizeof(int) * ecap);
    adj = malloc(sizeof(int) * ecap);
    dg = malloc(sizeof(int) * (size_t)CAP);
    side = malloc(sizeof(int) * (size_t)CAP);
    mark = malloc(sizeof(int) * (size_t)CAP);
    RA = malloc(sizeof(uint64_t) * (size_t)CAP * W);
    RB = malloc(sizeof(uint64_t) * (size_t)CAP * W);
    if (!EA || !EB || !bestEA || !bestEB || !perm || !adj || !dg || !side || !mark || !RA || !RB) {
        printf("0 0\n");
        return 0;
    }
    memset(mark, 0, sizeof(int) * (size_t)CAP);
    stamp = 0;

    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= n || v >= n || u == v) {
            printf("0 0\n");
            return 0;
        }
        EA[e] = u;
        EB[e] = v;
    }
    N = n;
    NE = m;

    for (int v = 0; v < N; v++) dg[v] = 0;
    for (int e = 0; e < NE; e++) {
        dg[EA[e]]++;
        dg[EB[e]]++;
    }
    for (int v = 0; v < N; v++) {
        if (dg[v] > DEG) {
            printf("0 0\n");
            return 0;
        }
    }
    rebuild_adj();
    if (!bipartize()) {
        printf("0 0\n");
        return 0;
    }
    for (int e = 0; e < NE; e++) {
        if (side[EA[e]] == 1) {
            int t = EA[e];
            EA[e] = EB[e];
            EB[e] = t;
        }
    }
    rebuild_adj();
    if (cost_of() != 0) {
        printf("0 0\n");
        return 0;
    }

    save_best();
    while (elapsed() < TL && N + 2 <= CAP) {
        if (!insert_pair()) break;
        int r = anneal(1500);
        if (r == 1) {
            save_best();
        } else if (r == -1) {
            restore_best();
            break;
        } else {
            restore_best();
        }
    }

    printf("%d %d\n", bestN, bestNE);
    for (int e = 0; e < bestNE; e++)
        printf("%d %d\n", bestEA[e], bestEB[e]);
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
# Main build: exact constructions, then bi-Cayley search, then unstructured
# repair from the best lift, then slack extension.
# ----------------------------------------------------------------------------

_MAX_CAP = 2_000_000  # keeps the C allocations and the int parsing safe


def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = max(1.0, time_limit - 6.0)
    hard = start + total
    rng = random.Random(seed)
    seed_c = int(seed) & 0x7FFFFFFF

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

    if D >= 4 and time.monotonic() < start + 0.2 * total:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    if d >= 3 and D >= 3:
        # Stage 1: bi-Cayley voltage search.
        remaining = start + 0.6 * total - time.monotonic()
        if remaining > 2.0:
            cap = min(lib.moore_bound(d, D), _MAX_CAP)
            if cap > best_n:
                try:
                    text = lib.run_c(C_SOURCE,
                                     [d, D, best_n, cap, seed_c, round(remaining, 2)],
                                     timeout=remaining + 20.0)
                    consider(*lib.parse_graph_text(text))
                except Exception:
                    pass

        # Stage 2 (new): unstructured repair. Insert two vertices at a time
        # into the best lift and anneal 2-switches until no pair is far apart.
        remaining = hard - time.monotonic() - 2.0
        if remaining > 2.0:
            cap = min(lib.moore_bound(d, D), best_n + 600, _MAX_CAP)
            if cap >= best_n + 2:
                try:
                    text = lib.run_c(C_REPAIR,
                                     [d, D, cap, seed_c, round(remaining, 2)],
                                     stdin_graph=best,
                                     timeout=remaining + 20.0)
                    consider(*lib.parse_graph_text(text))
                except Exception:
                    pass

    # Stage 3: use any spare degree to add vertices.
    if time.monotonic() < hard - 0.5:
        try:
            n2, e2 = _slack_extend(best[0], best[1], d, D, rng, hard)
            consider(n2, e2)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
