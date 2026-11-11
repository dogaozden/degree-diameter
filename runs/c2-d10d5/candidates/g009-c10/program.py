import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Combined program.
#
# Two C engines, both run only after the exact constructions:
#   * C_NEW: a non-algebraic search. It grows a d-regular bipartite graph by
#     vertex-pair insertion and repairs each new size with degree-preserving
#     edge switches under simulated annealing (cost = unordered pairs at
#     distance > D). It is a different construction from the group-lift search.
#   * C_OLD: the previous bi-Cayley voltage annealing engine, kept as a safe
#     second route. Its best0 is the best order found so far.
# Every candidate is checked with lib.is_valid, and the best valid graph wins.
# Fallback: K_{d,d} (valid for D >= 2).
# ----------------------------------------------------------------------------

NEW_CAP = 8000

C_NEW = r"""
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

static int d_, D_, CAP, WS, N, nA;
static int *adj, *side, *Alist;
static int *snap_adj, *snap_side, *snap_A;
static int snapN, snapnA;
static uint64_t *bsA, *bsB;
static double TL, tstart;
static int sa, sa2, sj, sj2, sb, sb2, sslA, sslB;

static double now(void) {
    return (double)clock() / CLOCKS_PER_SEC - tstart;
}

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int find_slot(int v, int target) {
    const int *ar = adj + (size_t)v * d_;
    for (int j = 0; j < d_; j++)
        if (ar[j] == target) return j;
    return -1;
}

/* Number of unordered pairs at distance > D_. */
static int64_t cost_of(void) {
    int W = (N + 63) / 64;
    uint64_t *cur = bsA, *nxt = bsB, *t;
    for (int v = 0; v < N; v++) {
        uint64_t *r = cur + (size_t)v * WS;
        for (int w = 0; w < W; w++) r[w] = 0;
        r[v >> 6] |= 1ULL << (v & 63);
    }
    for (int s = 0; s < D_; s++) {
        for (int v = 0; v < N; v++) {
            uint64_t *o = nxt + (size_t)v * WS;
            const uint64_t *c = cur + (size_t)v * WS;
            for (int w = 0; w < W; w++) o[w] = c[w];
            const int *ar = adj + (size_t)v * d_;
            for (int j = 0; j < d_; j++) {
                const uint64_t *u = cur + (size_t)ar[j] * WS;
                for (int w = 0; w < W; w++) o[w] |= u[w];
            }
        }
        t = cur;
        cur = nxt;
        nxt = t;
    }
    int64_t ones = 0;
    for (int v = 0; v < N; v++) {
        const uint64_t *r = cur + (size_t)v * WS;
        for (int w = 0; w < W; w++) ones += popc(r[w]);
    }
    return ((int64_t)N * N - ones) / 2;
}

/* Degree-preserving switch between two A vertices. Records undo info. */
static int try_switch(void) {
    int a = Alist[rndint(nA)];
    int a2 = Alist[rndint(nA)];
    if (a == a2) return 0;
    int j = rndint(d_), j2 = rndint(d_);
    int b = adj[a * d_ + j], b2 = adj[a2 * d_ + j2];
    if (b == b2) return 0;
    if (find_slot(a, b2) >= 0 || find_slot(a2, b) >= 0) return 0;
    int sA = find_slot(b, a), sB = find_slot(b2, a2);
    adj[a * d_ + j] = b2;
    adj[a2 * d_ + j2] = b;
    adj[b * d_ + sA] = a2;
    adj[b2 * d_ + sB] = a;
    sa = a; sa2 = a2; sj = j; sj2 = j2;
    sb = b; sb2 = b2; sslA = sA; sslB = sB;
    return 1;
}

static void undo_switch(void) {
    adj[sa * d_ + sj] = sb;
    adj[sa2 * d_ + sj2] = sb2;
    adj[sb * d_ + sslA] = sa;
    adj[sb2 * d_ + sslB] = sa2;
}

/* Add two new vertices ap (side 0) and bp (side 1), each of degree d_:
   d_ times remove an old edge (x,y) and add (x,bp), (ap,y). */
static void insert_pair(void) {
    int oldN = N, oldnA = nA;
    int ap = N, bp = N + 1;
    side[ap] = 0;
    side[bp] = 1;
    int cA = 0, cB = 0;
    long guard = 0;
    while (cA < d_ && guard < 2000000) {
        guard++;
        int x = Alist[rndint(oldnA)];
        int j = rndint(d_);
        int y = adj[x * d_ + j];
        if (y >= oldN) continue;
        int dup = 0;
        for (int q = 0; q < cA; q++)
            if (adj[ap * d_ + q] == y) dup = 1;
        for (int q = 0; q < cB; q++)
            if (adj[bp * d_ + q] == x) dup = 1;
        if (dup) continue;
        int sy = find_slot(y, x);
        if (sy < 0) continue;
        adj[x * d_ + j] = bp;
        adj[y * d_ + sy] = ap;
        adj[bp * d_ + cB++] = x;
        adj[ap * d_ + cA++] = y;
    }
    Alist[nA++] = ap;
    N += 2;
}

static void save_snap(void) {
    snapN = N;
    snapnA = nA;
    memcpy(snap_adj, adj, sizeof(int) * (size_t)N * d_);
    memcpy(snap_side, side, sizeof(int) * (size_t)N);
    memcpy(snap_A, Alist, sizeof(int) * (size_t)nA);
}

static void load_snap(void) {
    N = snapN;
    nA = snapnA;
    memcpy(adj, snap_adj, sizeof(int) * (size_t)N * d_);
    memcpy(side, snap_side, sizeof(int) * (size_t)N);
    memcpy(Alist, snap_A, sizeof(int) * (size_t)nA);
}

/* Simulated annealing on the current size, for at most `budget` seconds. */
static int anneal(double budget) {
    double t0 = now();
    int64_t cost = cost_of();
    const double T0 = 1.5, T1 = 0.05;
    while (cost > 0) {
        double el = now() - t0;
        if (el > budget) break;
        double T = T0 * pow(T1 / T0, el / budget);
        if (!try_switch()) continue;
        int64_t c2 = cost_of();
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
            cost = c2;
        } else {
            undo_switch();
        }
    }
    return cost == 0;
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: d D seed time cap\n");
        return 1;
    }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    TL = atof(argv[4]);
    CAP = atoi(argv[5]);
    tstart = (double)clock() / CLOCKS_PER_SEC;

    rs = (seed + 7) * 0x9E3779B97F4A7C15ULL ^ 0xA24BAED4963EE407ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 8; i++) rnd64();

    if (d_ < 2 || D_ < 2) {
        printf("0 0\n");
        return 0;
    }
    CAP &= ~1;
    if (CAP < 2 * d_ + 2) {
        printf("0 0\n");
        return 0;
    }
    WS = (CAP + 63) / 64;

    adj = malloc(sizeof(int) * (size_t)CAP * d_);
    side = malloc(sizeof(int) * (size_t)CAP);
    Alist = malloc(sizeof(int) * (size_t)CAP);
    snap_adj = malloc(sizeof(int) * (size_t)CAP * d_);
    snap_side = malloc(sizeof(int) * (size_t)CAP);
    snap_A = malloc(sizeof(int) * (size_t)CAP);
    bsA = malloc(sizeof(uint64_t) * (size_t)CAP * WS);
    bsB = malloc(sizeof(uint64_t) * (size_t)CAP * WS);
    if (!adj || !side || !Alist || !snap_adj || !snap_side || !snap_A || !bsA || !bsB) {
        printf("0 0\n");
        return 0;
    }

    /* Start: K_{d,d}, diameter 2. */
    N = 2 * d_;
    nA = d_;
    for (int i = 0; i < d_; i++) {
        Alist[i] = i;
        side[i] = 0;
        side[d_ + i] = 1;
    }
    for (int i = 0; i < d_; i++)
        for (int s = 0; s < d_; s++)
            adj[i * d_ + s] = d_ + (i + s) % d_;
    for (int k = 0; k < d_; k++)
        for (int s = 0; s < d_; s++)
            adj[(d_ + k) * d_ + s] = (k - s + d_) % d_;
    save_snap();

    while (now() < TL) {
        if (N + 2 > CAP) break;
        double rem = TL - now();
        double step = 0.25 * rem;
        if (step < 0.5) step = 0.5;
        if (step > rem) step = rem;
        insert_pair();
        if (anneal(step)) {
            save_snap();
        } else {
            load_snap();
        }
    }

    long long m = (long long)snapnA * d_;
    printf("%d %lld\n", snapN, m);
    for (int v = 0; v < snapN; v++) {
        if (snap_side[v] != 0) continue;
        for (int j = 0; j < d_; j++)
            printf("%d %d\n", v, snap_adj[v * d_ + j]);
    }
    return 0;
}
"""

C_OLD = r"""
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
# Main build: exact constructions, then the two C engines, keeping the best valid graph.
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

    if d >= 3 and D >= 3:
        # Route 1: direct bipartite switch-and-insert annealing (different construction).
        remaining = deadline - time.monotonic()
        if remaining > 4.0:
            new_budget = round(0.55 * remaining, 2)
            cap = min(lib.moore_bound(d, D), NEW_CAP)
            try:
                text = lib.run_c(C_NEW,
                                 [d, D, int(seed) & 0x7FFFFFFF, new_budget, cap],
                                 timeout=new_budget + 15.0)
                n1, e1 = lib.parse_graph_text(text)
                consider(n1, e1)
            except Exception:
                pass

        # Route 2: the previous bi-Cayley voltage engine, seeded with the best order so far.
        remaining = deadline - time.monotonic()
        if remaining > 2.0:
            cap = lib.moore_bound(d, D)
            try:
                text = lib.run_c(C_OLD,
                                 [d, D, best_n, cap, int(seed) & 0x7FFFFFFF, round(remaining, 2)],
                                 timeout=remaining + 8.0)
                n2, e2 = lib.parse_graph_text(text)
                consider(n2, e2)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
