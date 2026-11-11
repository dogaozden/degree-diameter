import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Combined program.
#
# Engine (C), two phases:
#
# Phase 1, bi-Cayley voltage annealing over Z_m x| Z_k2 (as in the parent):
#   - a bandit over base sizes k (k <= 4),
#   - near-miss continuation and an iterated-local-search memory.
#
# Phase 2, NEW: pair insertion with switch repair.
#   Take the best valid regular bipartite graph G on 2h vertices. Add one A-vertex
#   a and one B-vertex b. Pick DEG disjoint edges (x_k, y_k) of G, reroute x_k to b
#   and y_k to a. The result is (DEG)-regular bipartite on 2h+2 vertices, and every
#   vertex again has degree DEG. Its defects (pairs at distance > D) are then removed
#   by degree-preserving double-edge switches under simulated annealing, with the
#   bad-pair count as the cost. A success becomes the new base, and growth repeats.
#   Reach sets are bitsets, so the cost is exact.
#
# Start graph: exact constructions (PG(2,q), W(q)) when they apply, else K_{d,d}.
# Calibration cases (d=3, D=3) return the exact graph immediately.
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
static double TOTAL;
static int *bestnbr;
static int best_stride, best_K, best_G;
static int have_best;
static int64_t LASTCOST;

/* Iterated-local-search memory: best near-miss state seen so far. */
static int have_near;
static int nr_K, nr_M, nr_K2, nr_R, nr_G, nr_N;
static int64_t nr_cost;
static int *nr_lay, *nr_vol;

/* Phase 2 state. */
static int vn = 0, vh = 0;
static int *vnb = NULL, *wnb = NULL, *usedv = NULL;
static uint64_t *RA = NULL, *RB = NULL;
static int R_MAX = 0;

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

/* ---------------- Phase 2: pair insertion with switch repair ---------------- */

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Number of unordered pairs at distance > DIAM in a graph with n vertices, deg-regular.
   Reach sets are bitsets; RA and RB must hold at least n rows of (n+63)/64 words. */
static int64_t bad_pairs(const int *nb, int n, int deg, int diam) {
    int W = (n + 63) >> 6;
    uint64_t *X = RA, *Y = RB;
    memset(X, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++) X[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int t = 0; t < diam; t++) {
        int changed = 0;
        for (int v = 0; v < n; v++) {
            uint64_t *dst = Y + (size_t)v * W;
            const uint64_t *src = X + (size_t)v * W;
            memcpy(dst, src, sizeof(uint64_t) * (size_t)W);
            for (int l = 0; l < deg; l++) {
                const uint64_t *s2 = X + (size_t)nb[v * deg + l] * W;
                for (int w = 0; w < W; w++) dst[w] |= s2[w];
            }
            if (memcmp(dst, src, sizeof(uint64_t) * (size_t)W) != 0) changed = 1;
        }
        uint64_t *tmp = X;
        X = Y;
        Y = tmp;
        if (!changed) break;
    }
    int64_t tot = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        const uint64_t *r = X + (size_t)v * W;
        for (int w = 0; w < W; w++) c += pc64(r[w]);
        tot += n - c;
    }
    return tot / 2;
}

static int adjacent(const int *nb, int a, int b, int deg) {
    for (int l = 0; l < deg; l++)
        if (nb[a * deg + l] == b) return 1;
    return 0;
}

static int find_slot(const int *nb, int v, int target, int deg) {
    for (int l = 0; l < deg; l++)
        if (nb[v * deg + l] == target) return l;
    return -1;
}

/* Build wnb from the valid base (vn = 2*vh vertices): A = 0..vh-1, B = vh..2vh-1.
   New A vertex a = vh (old), new B vertex b = 2*vh+1. Choose DEG disjoint base edges
   (x_k, y_k); reroute x_k -> b and y_k -> a. Result is still DEG-regular. */
static int grow_from_base(void) {
    int deg = DEG, h0 = vh, h = vh + 1, n = 2 * h;
    int a = h0, b = n - 1;
    for (int v = 0; v < 2 * h0; v++) {
        int nv = v < h0 ? v : v + 1;
        for (int l = 0; l < deg; l++) {
            int y = vnb[v * deg + l];
            wnb[nv * deg + l] = y < h0 ? y : y + 1;
        }
    }
    memset(usedv, 0, sizeof(int) * (size_t)n);
    int cnt = 0;
    for (int tries = 0; cnt < deg && tries < 200000; tries++) {
        int x = rndint(h0);
        int l = rndint(deg);
        int y = wnb[x * deg + l];
        if (usedv[x] || usedv[y]) continue;
        int s = find_slot(wnb, y, x, deg);
        if (s < 0) return 0;
        usedv[x] = usedv[y] = 1;
        wnb[x * deg + l] = b;
        wnb[y * deg + s] = a;
        wnb[a * deg + cnt] = y;
        wnb[b * deg + cnt] = x;
        cnt++;
    }
    return cnt == deg;
}

/* One growth attempt: grow by a pair, then anneal double-edge switches on bad pairs.
   On success the grown graph becomes the new valid base. */
static int try_grow(int iters) {
    int deg = DEG;
    if (!grow_from_base()) return 0;
    int h = vh + 1, n = 2 * h;
    int64_t cost = bad_pairs(wnb, n, deg, DIAM);
    for (int it = 0; it < iters && cost > 0; it++) {
        if (elapsed() > TOTAL) break;
        double T = 1.5 * (1.0 - (double)it / iters) + 0.05;
        int a1 = rndint(h), a2 = rndint(h);
        if (a1 == a2) continue;
        int l1 = rndint(deg), l2 = rndint(deg);
        int b1 = wnb[a1 * deg + l1], b2 = wnb[a2 * deg + l2];
        if (b1 == b2) continue;
        if (adjacent(wnb, a1, b2, deg) || adjacent(wnb, a2, b1, deg)) continue;
        int s1 = find_slot(wnb, b1, a1, deg), s2 = find_slot(wnb, b2, a2, deg);
        if (s1 < 0 || s2 < 0) return 0;
        wnb[a1 * deg + l1] = b2;
        wnb[a2 * deg + l2] = b1;
        wnb[b1 * deg + s1] = a2;
        wnb[b2 * deg + s2] = a1;
        int64_t nc = bad_pairs(wnb, n, deg, DIAM);
        int64_t dl = nc - cost;
        if (dl <= 0 || rnd01() < exp(-(double)dl / T)) {
            cost = nc;
        } else {
            wnb[a1 * deg + l1] = b1;
            wnb[a2 * deg + l2] = b2;
            wnb[b1 * deg + s1] = a1;
            wnb[b2 * deg + s2] = a2;
        }
    }
    if (cost != 0) return 0;
    vn = n;
    vh = h;
    memcpy(vnb, wnb, sizeof(int) * (size_t)n * deg);
    return 1;
}

/* Start phase 2 from the best voltage graph and grow it as far as time allows. */
static void phase2(void) {
    int deg = DEG;
    if (best_stride + 2 > CAP) return;
    int rows = (CAP < best_stride + 200 ? CAP : best_stride + 200) + 2;
    int words = (rows + 63) >> 6;
    double mem = (double)rows * (double)words * 8.0 * 2.0;
    if (mem > 3e8) return;
    vnb = malloc(sizeof(int) * (size_t)rows * deg);
    wnb = malloc(sizeof(int) * (size_t)rows * deg);
    usedv = malloc(sizeof(int) * (size_t)rows);
    RA = malloc(sizeof(uint64_t) * (size_t)rows * words);
    RB = malloc(sizeof(uint64_t) * (size_t)rows * words);
    if (!vnb || !wnb || !usedv || !RA || !RB) return;
    R_MAX = rows;

    vn = best_stride;
    vh = vn / 2;
    for (int v = 0; v < vn; v++)
        for (int l = 0; l < deg; l++)
            vnb[v * deg + l] = bestnbr[(size_t)l * vn + v];

    while (elapsed() < TOTAL && vn + 2 <= CAP && vn + 2 <= R_MAX) {
        try_grow(800);
    }
}

static void print_result(void) {
    if (vnb && vn > 0) {
        printf("%d %d\n", vn, vh * DEG);
        for (int u = 0; u < vh; u++)
            for (int l = 0; l < DEG; l++)
                printf("%d %d\n", u, vnb[u * DEG + l]);
        return;
    }
    if (have_best) {
        int KG = best_K * best_G;
        long long m = (long long)KG * DEG;
        printf("%d %lld\n", best_stride, m);
        for (int u = 0; u < KG; u++)
            for (int l = 0; l < DEG; l++)
                printf("%d %d\n", u, bestnbr[(size_t)l * best_stride + u]);
        return;
    }
    printf("0 0\n");
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
    TL = TOTAL * 0.6;
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

    /* Phase 1: voltage annealing. */
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

    /* Phase 2: pair insertion with switch repair, from the best voltage graph. */
    TL = TOTAL;
    if (have_best) phase2();

    print_result();
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
# Main build: exact constructions first, then the C search.
# ----------------------------------------------------------------------------

_MAX_CAP = 2_000_000  # keeps the C allocations and the int parsing safe


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
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

    # Main search, entirely in C (voltage annealing, then pair insertion with switch repair).
    if d >= 3 and D >= 3:
        remaining = deadline - time.monotonic()
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

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
