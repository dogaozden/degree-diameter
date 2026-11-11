import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Stage 1 engine (unchanged from parent): bi-Cayley voltage annealing over
# Z_m x| Z_k2. Produces a d-regular bipartite lift that is valid for diameter D.
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
        /* Near miss: keep annealing the same group from its final state. */
        int extra = 0;
        while (!ok && !timed_out && extra < 3 && LASTCOST <= (int64_t)N / 2 && elapsed() < TL) {
            ok = run_trial(6000, 2000, 0);
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
# Stage 2 engine (new): vertex growth on a d-regular bipartite graph plus
# degree-preserving 2-switch annealing against the diameter constraint.
#
# Growth: choose d-1 edges (a_i, b_i) forming a matching. Add x (side A) and
# y (side B). Replace a_i-b_i by a_i-y and b_i-x, and add x-y. Every
# existing vertex keeps its degree, and x, y each get degree d.
#
# Repair: 2-switches (a1-b1, a2-b2 -> a1-b2, a2-b1) keep the graph d-regular
# and bipartite. Cost = ordered pairs at distance > DIAM, computed with
# bitset reach masks. A growth is kept only if the cost reaches 0 within
# the iteration budget; otherwise the last valid state is restored.
#
# The input graph is used as the starting point if it is d-regular, bipartite
# and valid for DIAM. Otherwise the engine starts from K_{d,d}.
# ----------------------------------------------------------------------------

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

static int D, DIAM, CAPN, WCAP;
static int *side, *base, *cur, *tmp;
static uint64_t *R0, *R1;
static int nbase, ncur;
static int64_t curcost;
static double tstart, TL;

static double elapsed(void) {
    return (double)clock() / CLOCKS_PER_SEC - tstart;
}

static int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Ordered pairs at distance > DIAM (0 iff the graph has diameter <= DIAM). */
static int64_t eval_cost(const int *nb, int n) {
    int Wn = (n + 63) >> 6;
    size_t sz = (size_t)n * (size_t)Wn;
    memset(R0, 0, sz * sizeof(uint64_t));
    for (int v = 0; v < n; v++)
        R0[(size_t)v * Wn + (size_t)(v >> 6)] |= 1ULL << (v & 63);
    for (int t = 0; t < DIAM; t++) {
        int changed = 0;
        for (int v = 0; v < n; v++) {
            const int *row = nb + (size_t)v * D;
            const uint64_t *self = R0 + (size_t)v * Wn;
            uint64_t *out = R1 + (size_t)v * Wn;
            for (int w = 0; w < Wn; w++) out[w] = self[w];
            for (int k = 0; k < D; k++) {
                const uint64_t *src = R0 + (size_t)row[k] * Wn;
                for (int w = 0; w < Wn; w++) out[w] |= src[w];
            }
            for (int w = 0; w < Wn; w++)
                if (out[w] != self[w]) changed = 1;
        }
        uint64_t *sw = R0;
        R0 = R1;
        R1 = sw;
        if (!changed) break;
    }
    int64_t reach = 0;
    for (size_t i = 0; i < sz; i++) reach += popc64(R0[i]);
    return (int64_t)n * n - reach;
}

/* Growth: dst = src plus two new vertices (ids n0 = side A, n0+1 = side B). */
static int grow_from(const int *src, int n0, int *dst) {
    int need = D - 1;
    if (need > 64 || need < 1) return 0;
    memcpy(dst, src, sizeof(int) * (size_t)n0 * D);
    int ea[64], ka[64], eb[64];
    int cnt = 0;
    for (int tries = 0; cnt < need && tries < 20000; tries++) {
        int a = rndint(n0);
        if (side[a] != 0) continue;
        int k = rndint(D);
        int b = src[a * D + k];
        int bad = 0;
        for (int i = 0; i < cnt; i++)
            if (ea[i] == a || eb[i] == b) {
                bad = 1;
                break;
            }
        if (bad) continue;
        ea[cnt] = a;
        ka[cnt] = k;
        eb[cnt] = b;
        cnt++;
    }
    if (cnt < need) return 0;
    int x = n0, y = n0 + 1;
    side[x] = 0;
    side[y] = 1;
    for (int i = 0; i < cnt; i++) {
        int a = ea[i], b = eb[i];
        dst[a * D + ka[i]] = y;
        int kb = -1;
        for (int k = 0; k < D; k++)
            if (dst[b * D + k] == a) {
                kb = k;
                break;
            }
        if (kb < 0) return 0;
        dst[b * D + kb] = x;
        dst[x * D + i] = b;
        dst[y * D + i] = a;
    }
    dst[x * D + D - 1] = y;
    dst[y * D + D - 1] = x;
    return 1;
}

/* Degree-preserving 2-switch on g with n vertices. Returns 0 if no change was made. */
static int swap_move(int *g, int n) {
    int a1, a2;
    do {
        a1 = rndint(n);
    } while (side[a1] != 0);
    do {
        a2 = rndint(n);
    } while (side[a2] != 0 || a2 == a1);
    int k1 = rndint(D), k2 = rndint(D);
    int b1 = g[a1 * D + k1], b2 = g[a2 * D + k2];
    if (b1 == b2) return 0;
    for (int k = 0; k < D; k++) {
        if (g[a1 * D + k] == b2) return 0;
        if (g[a2 * D + k] == b1) return 0;
    }
    g[a1 * D + k1] = b2;
    g[a2 * D + k2] = b1;
    for (int k = 0; k < D; k++)
        if (g[b1 * D + k] == a1) {
            g[b1 * D + k] = a2;
            break;
        }
    for (int k = 0; k < D; k++)
        if (g[b2 * D + k] == a2) {
            g[b2 * D + k] = a1;
            break;
        }
    return 1;
}

/* Anneal the state in cur (ncur vertices, curcost > 0) toward cost 0. */
static int anneal(int iters) {
    for (int t = 0; t < iters; t++) {
        if (curcost == 0) return 1;
        if ((t & 7) == 0 && elapsed() > TL) return 0;
        double T = 2.0 * (1.0 - (double)t / iters) + 0.05;
        memcpy(tmp, cur, sizeof(int) * (size_t)ncur * D);
        if (!swap_move(tmp, ncur)) continue;
        int64_t c = eval_cost(tmp, ncur);
        double dc = (double)(c - curcost) * 0.5;
        if (c <= curcost || rnd01() < exp(-dc / T)) {
            int *s = cur;
            cur = tmp;
            tmp = s;
            curcost = c;
        }
    }
    return curcost == 0;
}

static void set_kdd(void) {
    nbase = 2 * D;
    for (int i = 0; i < D; i++) {
        side[i] = 0;
        side[D + i] = 1;
    }
    for (int i = 0; i < D; i++)
        for (int k = 0; k < D; k++) {
            base[i * D + k] = D + k;
            base[(D + i) * D + k] = k;
        }
}

int main(int argc, char **argv) {
    if (argc < 6) {
        printf("0 0\n");
        return 1;
    }
    D = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    CAPN = atoi(argv[3]);
    unsigned long long seed = strtoull(argv[4], NULL, 10);
    TL = atof(argv[5]);
    tstart = (double)clock() / CLOCKS_PER_SEC;

    rs = (seed + 1) * 0x9E3779B97F4A7C15ULL ^ 0x5851F42D4C957F2DULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 8; i++) rnd64();

    if (D < 3 || D > 64 || DIAM < 2 || CAPN < 2 * D + 4) {
        printf("0 0\n");
        return 0;
    }
    CAPN &= ~1;
    WCAP = (CAPN + 63) >> 6;

    side = malloc(sizeof(int) * (size_t)CAPN);
    base = malloc(sizeof(int) * (size_t)CAPN * D);
    cur = malloc(sizeof(int) * (size_t)CAPN * D);
    tmp = malloc(sizeof(int) * (size_t)CAPN * D);
    R0 = malloc(sizeof(uint64_t) * (size_t)CAPN * WCAP);
    R1 = malloc(sizeof(uint64_t) * (size_t)CAPN * WCAP);
    if (!side || !base || !cur || !tmp || !R0 || !R1) {
        printf("0 0\n");
        return 0;
    }

    /* Optional start graph from stdin. */
    int n_in = 0, m_in = 0;
    int ok = 0;
    if (scanf("%d %d", &n_in, &m_in) == 2 && n_in > 0 && n_in <= CAPN &&
        n_in % 2 == 0 && m_in >= 0) {
        int *deg = calloc((size_t)n_in, sizeof(int));
        ok = (deg != NULL);
        for (int e = 0; e < m_in && ok; e++) {
            int u, v;
            if (scanf("%d %d", &u, &v) != 2) {
                ok = 0;
                break;
            }
            if (u < 0 || v < 0 || u >= n_in || v >= n_in || u == v) {
                ok = 0;
                break;
            }
            if (deg[u] >= D || deg[v] >= D) {
                ok = 0;
                break;
            }
            base[u * D + deg[u]++] = v;
            base[v * D + deg[v]++] = u;
        }
        if (ok)
            for (int v = 0; v < n_in && ok; v++)
                if (deg[v] != D) ok = 0;
        if (ok)
            for (int v = 0; v < n_in && ok; v++)
                for (int k = 0; k < D && ok; k++)
                    for (int j = k + 1; j < D; j++)
                        if (base[v * D + k] == base[v * D + j]) {
                            ok = 0;
                            break;
                        }
        if (ok) {
            int *q = malloc(sizeof(int) * (size_t)n_in);
            if (!q) {
                ok = 0;
            } else {
                for (int v = 0; v < n_in; v++) side[v] = -1;
                for (int s = 0; s < n_in; s++) {
                    if (side[s] != -1) continue;
                    side[s] = 0;
                    int qh = 0, qt = 0;
                    q[qt++] = s;
                    while (qh < qt) {
                        int u = q[qh++];
                        for (int k = 0; k < D; k++) {
                            int w = base[u * D + k];
                            if (side[w] == -1) {
                                side[w] = 1 - side[u];
                                q[qt++] = w;
                            }
                        }
                    }
                }
                for (int v = 0; v < n_in && ok; v++)
                    for (int k = 0; k < D; k++)
                        if (side[base[v * D + k]] == side[v]) {
                            ok = 0;
                            break;
                        }
                free(q);
            }
        }
        free(deg);
        if (ok) nbase = n_in;
    }

    if (ok) {
        curcost = eval_cost(base, nbase);
        if (curcost != 0) ok = 0;
    }
    if (!ok) {
        set_kdd();
        curcost = eval_cost(base, nbase);
    }

    const int ITER = 150;
    while (elapsed() < TL && nbase + 2 <= CAPN) {
        int n1 = nbase + 2;
        if (!grow_from(base, nbase, tmp)) continue;
        int *s = cur;
        cur = tmp;
        tmp = s;
        ncur = n1;
        curcost = eval_cost(cur, ncur);
        if (anneal(ITER)) {
            s = base;
            base = cur;
            cur = s;
            nbase = n1;
        }
    }

    /* base is always a valid d-regular bipartite graph with diameter <= DIAM. */
    int n = nbase;
    long long m = 0;
    for (int v = 0; v < n; v++)
        if (side[v] == 0) m += D;
    printf("%d %lld\n", n, m);
    for (int v = 0; v < n; v++)
        if (side[v] == 0)
            for (int k = 0; k < D; k++) printf("%d %d\n", v, base[v * D + k]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Safe baseline families (unchanged from parent).
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


def _is_regular(n, edges, d):
    """True if every vertex of the graph has degree exactly d."""
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
    return all(x == d for x in deg)


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
# Main build: exact constructions, then the lift search (stage 1), then the
# vertex-growth search from the best graph so far (stage 2), then slack.
# Every accepted graph passes lib.is_valid. The fallback is always valid.
# ----------------------------------------------------------------------------

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

    # Exact constructions.
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

    if d >= 3 and D >= 3:
        # Stage 1: group-lift annealing (parent engine).
        remaining = start + budget - time.monotonic()
        if remaining > 4.0:
            t1 = 0.6 * remaining
            try:
                text = lib.run_c(C_LIFT,
                                 [d, D, best_n, lib.moore_bound(d, D),
                                  int(seed) & 0x7FFFFFFF, round(t1, 2)],
                                 timeout=t1 + 15.0)
                n1, e1 = lib.parse_graph_text(text)
                consider(n1, e1)
            except Exception:
                pass

        # Stage 2: vertex growth with 2-switch annealing, starting from best.
        remaining = start + budget - time.monotonic()
        if remaining > 2.0:
            seed_graph = best if _is_regular(best[0], best[1], d) else None
            cap = min(lib.moore_bound(d, D), max(8192, best_n + 64))
            t2 = remaining - 1.0
            try:
                text = lib.run_c(C_GROW,
                                 [d, D, cap, int(seed) & 0x7FFFFFFF, round(t2, 2)],
                                 stdin_graph=seed_graph,
                                 timeout=t2 + 15.0)
                n2, e2 = lib.parse_graph_text(text)
                consider(n2, e2)
            except Exception:
                pass

    # Use any spare degree in the best graph to add vertices.
    if time.monotonic() < final_deadline:
        n3, e3 = _slack_extend(best[0], best[1], d, D, rng, final_deadline)
        consider(n3, e3)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
