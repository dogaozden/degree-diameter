import random
import time

import lib


# ----------------------------------------------------------------------------
# Two-phase engine, all in C.
#
# Phase A: bi-Cayley lift search over Z_m x| Z_k (semidirect groups, voltage
# annealing with exact-by-symmetry cost). It grows the best known graph.
#
# Phase B (new): exact, non-lifted annealing. Starting from the best graph, it
# inserts a new vertex pair (w in A, x in B) by removing DEG-1 matching edges
# and rewiring them through w and x. Then it anneals with degree-preserving
# 2-switches. The cost is the exact number of vertex pairs at distance > D,
# computed by bitset BFS. A graph is output only when that cost is zero.
#
# Python side: exact projective-plane incidence when it applies, otherwise
# K_{d,d} as the safe fallback. The C engine gets the current best as its start
# graph. Slack extension and lib.is_valid guard every kept graph.
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
#define MAXSTEP 500
#define BIGCOST ((int64_t)1 << 60)

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

static int DEG, DIAM, CAP, CAPN;
static double TL, TSTART, TLA;
static int timed_out;
static uint8_t POP8[256];

static double elapsed(void) {
    return (double)clock() / CLOCKS_PER_SEC - TSTART;
}

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
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

/* ---------------- phase A: bi-Cayley lift search ---------------- */

static const int K2_CHOICES[NCHOICE] = {1,1,2,2,3,4,5,6,7,8,9,10,12,14,16,18,20,24,30,36};
static int K, K2, M, R, G, N;
static int64_t PWR[64];
static int *AA, *BB, *nbr, *lay, *vol;
static uint8_t *cur, *scr, *tmpb, FULL;
static int64_t LASTCOST;

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
    for (int v = 0; v < N; v++) s += POP8[r[v]];
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
        for (int i = 0; i < K; i++) set_dart(l, i, lay[l * K + i], vol[l * K + i]);

    compute_reach(cur);
    int64_t cost = total_cost(cur);
    double c0 = cost > 1 ? (double)cost : 1.0;
    int64_t best_cost = cost;
    int last = 0;

    for (int t = 0; t < iters && cost != 0; t++) {
        if (t - last > patience) break;
        if ((t & 31) == 0 && elapsed() > TLA) {
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

/* ---------------- phase B: exact annealing with pair insertion ---------------- */

static int *Wadj, *Wdeg, *Badj, *Bdeg;
static uint8_t *Wside, *Bside;
static int Wn, Bn;
static uint64_t *RX = NULL, *RY = NULL;
static size_t rcap = 0;
static int undo_row[4 * MAXDEG];

static int colour(int n, const int *adj, const int *deg, uint8_t *side) {
    int *st = malloc(sizeof(int) * (size_t)(n > 0 ? n : 1));
    if (!st) return 0;
    for (int v = 0; v < n; v++) side[v] = 2;
    int ok = 1;
    for (int s = 0; s < n && ok; s++) {
        if (side[s] != 2) continue;
        side[s] = 0;
        int sp = 0;
        st[sp++] = s;
        while (sp > 0 && ok) {
            int u = st[--sp];
            for (int j = 0; j < deg[u]; j++) {
                int v = adj[(size_t)u * DEG + j];
                if (side[v] == 2) {
                    side[v] = (uint8_t)(1 - side[u]);
                    st[sp++] = v;
                } else if (side[v] == side[u]) {
                    ok = 0;
                    break;
                }
            }
        }
    }
    free(st);
    return ok;
}

static int find_slot(int v, int u) {
    for (int j = 0; j < Wdeg[v]; j++)
        if (Wadj[(size_t)v * DEG + j] == u) return j;
    return -1;
}

static int rand_side(uint8_t s) {
    for (int t = 0; t < 100000; t++) {
        int v = rndint(Wn);
        if (Wside[v] == s && Wdeg[v] > 0) return v;
    }
    return -1;
}

/* Exact number of unordered vertex pairs at distance > DIAM in the working graph. */
static int64_t exact_cost(void) {
    int n = Wn;
    size_t W = (size_t)((n + 63) >> 6);
    size_t need = (size_t)n * W;
    if (need > rcap) {
        free(RX);
        free(RY);
        RX = malloc(need * sizeof(uint64_t));
        RY = malloc(need * sizeof(uint64_t));
        if (!RX || !RY) {
            RX = NULL;
            RY = NULL;
            rcap = 0;
            return BIGCOST;
        }
        rcap = need;
    }
    uint64_t *X = RX, *Y = RY;
    memset(X, 0, need * sizeof(uint64_t));
    for (int v = 0; v < n; v++) X[(size_t)v * W + ((size_t)v >> 6)] |= 1ULL << (v & 63);
    for (int t = 0; t < DIAM; t++) {
        int changed = 0;
        for (int v = 0; v < n; v++) {
            uint64_t *dst = Y + (size_t)v * W;
            const uint64_t *src = X + (size_t)v * W;
            for (size_t w = 0; w < W; w++) dst[w] = src[w];
            for (int j = 0; j < Wdeg[v]; j++) {
                const uint64_t *s = X + (size_t)Wadj[(size_t)v * DEG + j] * W;
                for (size_t w = 0; w < W; w++) dst[w] |= s[w];
            }
            for (size_t w = 0; w < W; w++) {
                if (dst[w] != src[w]) {
                    changed = 1;
                    break;
                }
            }
        }
        uint64_t *tp = X;
        X = Y;
        Y = tp;
        if (!changed) break;
    }
    int64_t tot = 0;
    for (size_t w = 0; w < need; w++) tot += pc64(X[w]);
    return ((int64_t)n * n - tot) / 2;
}

/* One degree-preserving 2-switch proposal, Metropolis accepted. Returns the new cost. */
static int64_t anneal_step(int64_t cost, double T) {
    int a = rand_side(0), a2 = rand_side(0);
    if (a < 0 || a2 < 0 || a == a2) return cost;
    int ja = rndint(Wdeg[a]), ja2 = rndint(Wdeg[a2]);
    int b = Wadj[(size_t)a * DEG + ja];
    int b2 = Wadj[(size_t)a2 * DEG + ja2];
    if (b == b2) return cost;
    if (find_slot(a, b2) >= 0 || find_slot(a2, b) >= 0) return cost;
    int jb = find_slot(b, a);
    int jb2 = find_slot(b2, a2);
    if (jb < 0 || jb2 < 0) return cost;
    int vs[4] = {a, a2, b, b2};
    for (int q = 0; q < 4; q++)
        memcpy(undo_row + q * DEG, Wadj + (size_t)vs[q] * DEG, sizeof(int) * (size_t)DEG);

    Wadj[(size_t)a * DEG + ja] = b2;
    Wadj[(size_t)b * DEG + jb] = a2;
    Wadj[(size_t)a2 * DEG + ja2] = b;
    Wadj[(size_t)b2 * DEG + jb2] = a;

    int64_t c2 = exact_cost();
    if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) return c2;
    for (int q = 0; q < 4; q++)
        memcpy(Wadj + (size_t)vs[q] * DEG, undo_row + q * DEG, sizeof(int) * (size_t)DEG);
    return cost;
}

/* Insert a new pair w (side 0) and x (side 1) by rewiring DEG-1 disjoint matching edges. */
static int insert_pair(void) {
    int n = Wn;
    if (n + 2 > CAP) return 0;
    int need = DEG - 1;
    int ua[MAXDEG], ub[MAXDEG];
    int cnt = 0;
    for (int tries = 0; cnt < need && tries < 20000; tries++) {
        int a = rand_side(0);
        if (a < 0) return 0;
        int b = Wadj[(size_t)a * DEG + rndint(Wdeg[a])];
        int dup = 0;
        for (int k = 0; k < cnt; k++) {
            if (ua[k] == a || ub[k] == b) {
                dup = 1;
                break;
            }
        }
        if (!dup) {
            ua[cnt] = a;
            ub[cnt] = b;
            cnt++;
        }
    }
    if (cnt < need) return 0;
    int w = n, x = n + 1;
    for (int k = 0; k < need; k++) {
        int a = ua[k], b = ub[k];
        int ja = find_slot(a, b);
        int jb = find_slot(b, a);
        Wadj[(size_t)a * DEG + ja] = x;
        Wadj[(size_t)b * DEG + jb] = w;
        Wadj[(size_t)w * DEG + k] = b;
        Wadj[(size_t)x * DEG + k] = a;
    }
    Wadj[(size_t)w * DEG + need] = x;
    Wadj[(size_t)x * DEG + need] = w;
    Wdeg[w] = DEG;
    Wdeg[x] = DEG;
    Wside[w] = 0;
    Wside[x] = 1;
    Wn = n + 2;
    return 1;
}

static void copy_B_to_W(void) {
    Wn = Bn;
    memcpy(Wadj, Badj, sizeof(int) * (size_t)DEG * Bn);
    memcpy(Wdeg, Bdeg, sizeof(int) * (size_t)Bn);
    memcpy(Wside, Bside, (size_t)Bn);
}

static void copy_W_to_B(void) {
    Bn = Wn;
    memcpy(Badj, Wadj, sizeof(int) * (size_t)DEG * Wn);
    memcpy(Bdeg, Wdeg, sizeof(int) * (size_t)Wn);
    memcpy(Bside, Wside, (size_t)Wn);
}

static void print_best(void) {
    long long m = 0;
    for (int v = 0; v < Bn; v++) m += Bdeg[v];
    m /= 2;
    printf("%d %lld\n", Bn, m);
    for (int v = 0; v < Bn; v++)
        for (int j = 0; j < Bdeg[v]; j++) {
            int u = Badj[(size_t)v * DEG + j];
            if (u > v) printf("%d %d\n", v, u);
        }
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: d D seed time < graph\n");
        return 1;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    TL = atof(argv[4]);
    TSTART = (double)clock() / CLOCKS_PER_SEC;

    rs = (seed + 1) * 0x9E3779B97F4A7C15ULL ^ 0xD1B54A32D192ED03ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 8; i++) rnd64();
    for (int x = 0; x < 256; x++) {
        int c = 0;
        for (int y = x; y; y >>= 1) c += y & 1;
        POP8[x] = (uint8_t)c;
    }
    if (DEG < 3 || DEG > MAXDEG || DIAM < 3) {
        printf("0 0\n");
        return 0;
    }

    double mb = 0.0, pw = 1.0;
    for (int i = 0; i < DIAM && mb < 1e6; i++) {
        mb += pw;
        pw *= (DEG - 1);
    }
    double bound = 2.0 * mb;
    CAP = bound > 200000.0 ? 200000 : (int)bound;
    CAPN = CAP + 4;

    AA = malloc(sizeof(int) * (size_t)CAPN);
    BB = malloc(sizeof(int) * (size_t)CAPN);
    nbr = malloc(sizeof(int) * (size_t)DEG * CAPN);
    lay = malloc(sizeof(int) * (size_t)DEG * MAXK);
    vol = malloc(sizeof(int) * (size_t)DEG * MAXK);
    cur = malloc((size_t)CAPN);
    scr = malloc((size_t)CAPN);
    tmpb = malloc((size_t)CAPN);
    Wadj = malloc(sizeof(int) * (size_t)DEG * CAPN);
    Badj = malloc(sizeof(int) * (size_t)DEG * CAPN);
    Wdeg = malloc(sizeof(int) * (size_t)CAPN);
    Bdeg = malloc(sizeof(int) * (size_t)CAPN);
    Wside = malloc((size_t)CAPN);
    Bside = malloc((size_t)CAPN);
    if (!AA || !BB || !nbr || !lay || !vol || !cur || !scr || !tmpb || !Wadj || !Badj ||
        !Wdeg || !Bdeg || !Wside || !Bside) {
        printf("0 0\n");
        return 0;
    }

    /* Read the start graph from stdin (the current best). Invalid input gives Bn = 0. */
    Bn = 0;
    int sn = 0, sm = 0;
    if (scanf("%d %d", &sn, &sm) != 2) {
        sn = 0;
        sm = 0;
    }
    if (sn >= 2 && sn <= CAP && sm >= 0) {
        int ok = 1;
        for (int v = 0; v < sn; v++) Bdeg[v] = 0;
        for (int i = 0; i < sm && ok; i++) {
            int u, v;
            if (scanf("%d %d", &u, &v) != 2) {
                ok = 0;
                break;
            }
            if (u < 0 || v < 0 || u >= sn || v >= sn || u == v) {
                ok = 0;
                break;
            }
            if (Bdeg[u] >= DEG || Bdeg[v] >= DEG) {
                ok = 0;
                break;
            }
            for (int j = 0; j < Bdeg[u]; j++)
                if (Badj[(size_t)u * DEG + j] == v) ok = 0;
            if (!ok) break;
            Badj[(size_t)u * DEG + Bdeg[u]++] = v;
            Badj[(size_t)v * DEG + Bdeg[v]++] = u;
        }
        if (ok && colour(sn, Badj, Bdeg, Bside)) Bn = sn;
    }

    /* Phase A: lift search for graphs larger than the start. */
    double TA = 0.55 * TL;
    TLA = TA;
    long long found = Bn;
    while (elapsed() < TA) {
        int k = 1 + rndint(MAXK);
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
        int ok = run_trial(4000, 1200, 1);
        int extra = 0;
        while (!ok && !timed_out && extra < 3 && LASTCOST <= (int64_t)N / 2 && elapsed() < TA) {
            ok = run_trial(6000, 2000, 0);
            extra++;
        }
        if (ok) {
            found = N;
            for (int v = 0; v < N; v++) {
                for (int l = 0; l < DEG; l++)
                    Badj[(size_t)v * DEG + l] = nbr[(size_t)l * N + v];
                Bdeg[v] = DEG;
            }
            Bn = N;
        }
    }

    /* Phase B: exact annealing with pair insertion, starting from the best graph. */
    int can_b = (Bn >= 2) && colour(Bn, Badj, Bdeg, Bside);
    while (can_b && elapsed() < TL - 0.5) {
        copy_B_to_W();
        if (!insert_pair()) break;
        int64_t cost = exact_cost();
        if (cost >= BIGCOST) break;
        double T0 = 1.0 + 0.05 * (double)cost;
        int steps = 0;
        while (cost > 0 && steps < MAXSTEP) {
            if ((steps & 7) == 0 && elapsed() > TL - 0.3) break;
            double T = T0 * (1.0 - (double)steps / MAXSTEP) + 0.15;
            cost = anneal_step(cost, T);
            steps++;
        }
        if (cost == 0) copy_W_to_B();
        if (elapsed() > TL - 0.3) break;
    }

    print_best();
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact construction used as a start graph.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Slack extension: add new vertices using spare degree, keeping only valid graphs.
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
# Main build.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.80 * time_limit, time_limit - 8.0))
    deadline = start + max(1.0, time_limit - 4.0)
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

    # Exact start: the projective-plane incidence graph is valid for D = 3.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    # Main search in C: lift search, then exact annealing with pair insertion.
    if d >= 3 and D >= 3:
        remaining = start + budget - time.monotonic()
        if remaining > 3.0:
            try:
                text = lib.run_c(C_SOURCE,
                                 [d, D, int(seed) & 0x7FFFFFFF, round(remaining - 1.0, 2)],
                                 stdin_graph=best,
                                 timeout=remaining + 20.0)
                n2, e2 = lib.parse_graph_text(text)
                consider(n2, e2)
            except Exception:
                pass

    # Use any spare degree in the best graph to add vertices.
    if time.monotonic() < deadline:
        try:
            n2, e2 = _slack_extend(best[0], best[1], d, D, rng, deadline)
            consider(n2, e2)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
