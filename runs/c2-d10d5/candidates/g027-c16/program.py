import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Two-engine program.
#
# Stage A (C_SOURCE): bi-Cayley voltage annealing over Z_m x| Z_k2, as before.
# Stage B (C_GROW, new): take the best d-regular bipartite graph and grow it by
#   vertex insertion. A new A-vertex and a new B-vertex take over a matching of
#   d edges (each removed edge a-b becomes a-newB and newA-b), so every degree
#   stays exactly d. Double-edge swaps then anneal the bad-pair count back to 0.
#   Non-algebraic, local search only.
# The K_{d,d} fallback and every candidate pass lib.is_valid before being kept.
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
    int nb2 = (K2 - b) % K2;
    int64_t a2 = (M - (PWR[nb2] * (int64_t)AA[x]) % M) % M;
    return (int)(a2 * K2 + nb2);
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


C_GROW = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define ITER_PER_STAGE 600

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
static int rndint(int m) {
    return (int)(rnd64() % (uint64_t)m);
}

/* Active ids: A vertices 0..n-1, B vertices MAXH..MAXH+n-1. Graph is DEG-regular. */
static int DEG, DIAM, MAXH, n, WS;
static int *nb, *bestnb, *unr, *unr2;
static int bestn = -1;
static uint64_t *R, *T;
static double tstart, TL;

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + (double)ts.tv_nsec * 1e-9;
}

static double elapsed(void) {
    return now_s() - tstart;
}

static int pop64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int nwords(void) {
    return (MAXH + n + 63) / 64;
}

/* Fills out[v] with unreached-vertex counts for active v; returns their sum. */
static int64_t evaluate(int *out) {
    int W = nwords();
    int N = 2 * n;
    for (int s = 0; s < 2; s++)
        for (int i = 0; i < n; i++) {
            int v = s ? MAXH + i : i;
            uint64_t *row = R + (size_t)v * WS;
            memset(row, 0, sizeof(uint64_t) * (size_t)W);
            row[v >> 6] |= 1ULL << (v & 63);
        }
    for (int t = 0; t < DIAM; t++) {
        for (int s = 0; s < 2; s++)
            for (int i = 0; i < n; i++) {
                int v = s ? MAXH + i : i;
                uint64_t *dst = T + (size_t)v * WS;
                const uint64_t *src = R + (size_t)v * WS;
                memcpy(dst, src, sizeof(uint64_t) * (size_t)W);
                for (int k = 0; k < DEG; k++) {
                    const uint64_t *ru = R + (size_t)nb[(size_t)v * DEG + k] * WS;
                    for (int w = 0; w < W; w++) dst[w] |= ru[w];
                }
            }
        uint64_t *tmp = R;
        R = T;
        T = tmp;
    }
    int64_t total = 0;
    for (int s = 0; s < 2; s++)
        for (int i = 0; i < n; i++) {
            int v = s ? MAXH + i : i;
            const uint64_t *row = R + (size_t)v * WS;
            int c = 0;
            for (int w = 0; w < W; w++) c += pop64(row[w]);
            out[v] = N - c;
            total += N - c;
        }
    return total;
}

static int has_nb(int v, int u) {
    for (int k = 0; k < DEG; k++)
        if (nb[(size_t)v * DEG + k] == u) return 1;
    return 0;
}

/* In v's neighbour list replace old by nw. */
static void repl(int v, int old, int nw) {
    int *p = nb + (size_t)v * DEG;
    for (int k = 0; k < DEG; k++)
        if (p[k] == old) {
            p[k] = nw;
            return;
        }
}

/* Remove a1-b1 and a2-b2, add a1-b2 and a2-b1. */
static void do_swap(int a1, int b1, int a2, int b2) {
    repl(a1, b1, b2);
    repl(b1, a1, a2);
    repl(a2, b2, b1);
    repl(b2, a2, a1);
}

static int pick_a(void) {
    for (int tries = 0; tries < 40; tries++) {
        int i = rndint(2 * n);
        int v = i < n ? i : MAXH + (i - n);
        if (unr[v] > 0) return v < MAXH ? v : nb[(size_t)v * DEG + rndint(DEG)];
    }
    return rndint(n);
}

/* Returns 1 if cost reached 0, 0 if the budget ran out, -1 on timeout. */
static int anneal(int iters, int64_t *costp) {
    int64_t cost = *costp;
    for (int it = 0; it < iters && cost > 0; it++) {
        if ((it & 7) == 0 && elapsed() > TL) {
            *costp = cost;
            return -1;
        }
        int a1 = (rnd01() < 0.6) ? pick_a() : rndint(n);
        int a2 = rndint(n);
        if (a1 == a2) continue;
        int b1 = nb[(size_t)a1 * DEG + rndint(DEG)];
        int b2 = nb[(size_t)a2 * DEG + rndint(DEG)];
        if (b1 == b2) continue;
        if (has_nb(a1, b2) || has_nb(a2, b1)) continue;
        do_swap(a1, b1, a2, b2);
        int64_t c2 = evaluate(unr2);
        double temp = 0.2 + 0.003 * (double)cost;
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
            int *tmp = unr;
            unr = unr2;
            unr2 = tmp;
            cost = c2;
        } else {
            do_swap(a1, b2, a2, b1);
        }
    }
    *costp = cost;
    return cost == 0;
}

/* Insert one new A vertex (id n) and one new B vertex (id MAXH+n) using a matching of DEG edges. */
static int grow(void) {
    if (n >= MAXH) return 0;
    int as[64], bs[64], cnt = 0;
    for (int tries = 0; cnt < DEG && tries < 20000; tries++) {
        int a = rndint(n);
        int b = nb[(size_t)a * DEG + rndint(DEG)];
        int ok = 1;
        for (int j = 0; j < cnt; j++)
            if (as[j] == a || bs[j] == b) {
                ok = 0;
                break;
            }
        if (ok) {
            as[cnt] = a;
            bs[cnt] = b;
            cnt++;
        }
    }
    if (cnt < DEG) return 0;
    int na = n, nbv = MAXH + n;
    for (int j = 0; j < DEG; j++) {
        int a = as[j], b = bs[j];
        repl(a, b, nbv);
        repl(b, a, na);
        nb[(size_t)na * DEG + j] = b;
        nb[(size_t)nbv * DEG + j] = a;
    }
    n++;
    return 1;
}

static void save_best(void) {
    memcpy(bestnb, nb, sizeof(int) * (size_t)2 * MAXH * DEG);
    bestn = n;
}

static void restore_best(void) {
    memcpy(nb, bestnb, sizeof(int) * (size_t)2 * MAXH * DEG);
    n = bestn;
}

int main(int argc, char **argv) {
    if (argc < 6) {
        printf("0 0\n");
        return 1;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    MAXH = atoi(argv[3]);
    unsigned long long seed = strtoull(argv[4], NULL, 10);
    TL = atof(argv[5]);
    tstart = now_s();

    rs = (seed + 1) * 0xA24BAED4963EE407ULL ^ 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 8; i++) rnd64();

    if (DEG < 3 || DEG > 64 || DIAM < 3 || MAXH < 4 || MAXH > 4000) {
        printf("0 0\n");
        return 0;
    }

    WS = (2 * MAXH + 63) / 64;
    nb = malloc(sizeof(int) * (size_t)2 * MAXH * DEG);
    bestnb = malloc(sizeof(int) * (size_t)2 * MAXH * DEG);
    unr = calloc((size_t)2 * MAXH, sizeof(int));
    unr2 = calloc((size_t)2 * MAXH, sizeof(int));
    R = calloc((size_t)2 * MAXH * WS, sizeof(uint64_t));
    T = calloc((size_t)2 * MAXH * WS, sizeof(uint64_t));
    if (!nb || !bestnb || !unr || !unr2 || !R || !T) {
        printf("0 0\n");
        return 0;
    }

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 <= 0 || m0 <= 0 || n0 > 2 * MAXH) {
        printf("0 0\n");
        return 0;
    }
    int *eu = malloc(sizeof(int) * (size_t)m0);
    int *ev = malloc(sizeof(int) * (size_t)m0);
    int *deg = calloc((size_t)n0, sizeof(int));
    int ok = eu && ev && deg;
    for (int e = 0; ok && e < m0; e++) {
        if (scanf("%d %d", &eu[e], &ev[e]) != 2) {
            ok = 0;
            break;
        }
        if (eu[e] < 0 || eu[e] >= n0 || ev[e] < 0 || ev[e] >= n0 || eu[e] == ev[e]) {
            ok = 0;
            break;
        }
        deg[eu[e]]++;
        deg[ev[e]]++;
    }
    for (int v = 0; ok && v < n0; v++)
        if (deg[v] != DEG) ok = 0;
    if (!ok) {
        printf("0 0\n");
        return 0;
    }

    int *off = malloc(sizeof(int) * (size_t)(n0 + 1));
    int *adj = malloc(sizeof(int) * (size_t)(2 * m0));
    int *fl = calloc((size_t)n0, sizeof(int));
    int *col = malloc(sizeof(int) * (size_t)n0);
    int *qu = malloc(sizeof(int) * (size_t)n0);
    if (!off || !adj || !fl || !col || !qu) {
        printf("0 0\n");
        return 0;
    }
    off[0] = 0;
    for (int v = 0; v < n0; v++) off[v + 1] = off[v] + deg[v];
    for (int e = 0; e < m0; e++) {
        int u = eu[e], v = ev[e];
        adj[off[u] + fl[u]++] = v;
        adj[off[v] + fl[v]++] = u;
    }
    for (int v = 0; v < n0; v++) col[v] = -1;
    for (int s = 0; s < n0 && ok; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int qh = 0, qt = 0;
        qu[qt++] = s;
        while (qh < qt && ok) {
            int u = qu[qh++];
            for (int j = off[u]; j < off[u + 1]; j++) {
                int w = adj[j];
                if (col[w] < 0) {
                    col[w] = 1 - col[u];
                    qu[qt++] = w;
                } else if (col[w] == col[u]) {
                    ok = 0;
                    break;
                }
            }
        }
    }
    int cA = 0, cB = 0;
    for (int v = 0; v < n0; v++) {
        if (col[v] == 0) cA++;
        else cB++;
    }
    if (!ok || cA != cB || cA < 1 || cA > MAXH) {
        printf("0 0\n");
        return 0;
    }
    n = cA;

    int *newid = malloc(sizeof(int) * (size_t)n0);
    int ia = 0, ib = 0;
    for (int v = 0; v < n0; v++) newid[v] = (col[v] == 0) ? ia++ : MAXH + ib++;
    int *nfl = calloc((size_t)2 * MAXH, sizeof(int));
    for (int e = 0; e < m0; e++) {
        int u = eu[e], v = ev[e];
        int a = (col[u] == 0) ? u : v;
        int b = (col[u] == 0) ? v : u;
        int ida = newid[a], idb = newid[b];
        nb[(size_t)ida * DEG + nfl[ida]++] = idb;
        nb[(size_t)idb * DEG + nfl[idb]++] = ida;
    }

    int64_t cost = evaluate(unr);
    if (cost != 0) {
        int r = anneal(1000000000, &cost);
        if (r == 1) save_best();
    } else {
        save_best();
    }
    if (bestn < 0) {
        printf("0 0\n");
        return 0;
    }

    while (n < MAXH && elapsed() < TL) {
        restore_best();
        if (!grow()) break;
        cost = evaluate(unr);
        int r = anneal(ITER_PER_STAGE, &cost);
        if (r == 1) save_best();
        else if (r < 0) break;
    }

    int bn = bestn;
    printf("%d %d\n", 2 * bn, bn * DEG);
    for (int i = 0; i < bn; i++)
        for (int k = 0; k < DEG; k++)
            printf("%d %d\n", i, bn + (bestnb[(size_t)i * DEG + k] - MAXH));
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
# Main build: exact start, voltage search (stage A), vertex growth (stage B).
# ----------------------------------------------------------------------------

_MAX_CAP = 2_000_000   # keeps the stage A allocations and int parsing safe
_GROW_CAP = 2600       # per-side cap for stage B arrays and eval cost


def build(d, D, seed, time_limit):
    start = time.monotonic()
    usable = max(1.0, min(0.85 * time_limit, time_limit - 8.0))
    deadline = start + usable

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

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
        # Stage A: bi-Cayley voltage annealing in C.
        remaining = deadline - time.monotonic()
        if remaining > 4.0:
            t_a = round(remaining * 0.5, 2)
            cap = min(lib.moore_bound(d, D), _MAX_CAP)
            if cap > best[0]:
                try:
                    text = lib.run_c(C_SOURCE,
                                     [d, D, best[0], cap, int(seed) & 0x7FFFFFFF, t_a],
                                     timeout=t_a + 20.0)
                    consider(*lib.parse_graph_text(text))
                except Exception:
                    pass

        # Stage B: grow the best d-regular graph by vertex insertion plus annealing.
        remaining = deadline - time.monotonic()
        if remaining > 3.0 and best[0] % 2 == 0:
            side_cap = min(lib.moore_bound(d, D) // 2 + 1, _GROW_CAP)
            if best[0] // 2 < side_cap:
                try:
                    t_b = round(remaining - 1.0, 2)
                    text = lib.run_c(C_GROW,
                                     [d, D, side_cap, int(seed) & 0x7FFFFFFF, t_b],
                                     stdin_graph=best,
                                     timeout=t_b + 20.0)
                    consider(*lib.parse_graph_text(text))
                except Exception:
                    pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
