import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Two-phase C engine, one process.
#
# Phase 1: bi-Cayley voltage annealing over Z_m x| Z_k2 (the parent's search),
#          run until frac * TL. It keeps the largest valid lift found.
# Phase 2 (new): graph surgery on the best valid graph. Repeatedly:
#          - insert a vertex pair (x on side A, y on side B) by removing a
#            matching of d edges and rewiring them through x and y, which keeps
#            every degree and the bipartition,
#          - repair the diameter with degree- and bipartition-preserving edge
#            switches, minimising the number of ordered pairs at distance > D
#            (simulated annealing, bitset BFS),
#          - keep the result only if the cost reaches 0, otherwise restart from
#            the best valid graph.
#
# Python keeps the exact constructions (PG(2,q), W(q)) and K_{d,d} as the
# safe fallback. Every C output is re-checked with lib.is_valid.
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
#define PHASE2_STEPS 1200

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

static int DEG, DIAM, CAP, EMAX;
static double tstart, TL, TL_TOTAL;
static uint8_t POP[256];

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + (double)ts.tv_nsec * 1e-9;
}
static double elapsed(void) {
    return now_s() - tstart;
}

static inline int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* ============================ phase 1 state ============================ */
static int K, K2, M, R, G, N;
static int64_t PWR[64];
static int *AA, *BB;
static int *nbr, *lay, *vol;
static uint8_t *cur, *scr, *tmpb;
static uint8_t FULL;
static int timed_out;
static int *bestnbr;
static int best_stride, best_K, best_G;
static int have_best;
static int64_t LASTCOST;
static int have_near;
static int nr_K, nr_M, nr_K2, nr_R, nr_G, nr_N;
static int64_t nr_cost;
static int *nr_lay, *nr_vol;

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

/* Phase 1: voltage search for lifts larger than `found`. */
static void phase1(long long found) {
    double tr[MAXK + 1] = {0}, wn[MAXK + 1] = {0};
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
}

/* ============================ phase 2 state ============================ */
static int gN, gm;
static int *gEA, *gEB, *gnb, *gdg, *gside, *queue_;
static int bN, bm;
static int *bEA, *bEB;
static uint64_t *RA, *RB;

static int rebuild(void) {
    for (int v = 0; v < gN; v++) gdg[v] = 0;
    for (int i = 0; i < gm; i++) {
        int a = gEA[i], b = gEB[i];
        if (a < 0 || b < 0 || a >= gN || b >= gN || a == b) return 0;
        if (gdg[a] >= DEG || gdg[b] >= DEG) return 0;
        gnb[(size_t)a * DEG + gdg[a]++] = b;
        gnb[(size_t)b * DEG + gdg[b]++] = a;
    }
    return 1;
}

/* Uses gN, gm, gEA, gEB (unoriented edges). Orients edges so gEA is side 0. */
static int load_edges(void) {
    if (gN <= 0 || gN > CAP || gm < 0 || gm > EMAX) return 0;
    if (!rebuild()) return 0;
    for (int v = 0; v < gN; v++) gside[v] = -1;
    int qh = 0, qt = 0;
    for (int s = 0; s < gN; s++) {
        if (gside[s] != -1) continue;
        gside[s] = 0;
        queue_[qt++] = s;
        while (qh < qt) {
            int u = queue_[qh++];
            for (int k = 0; k < gdg[u]; k++) {
                int w = gnb[(size_t)u * DEG + k];
                if (gside[w] == -1) {
                    gside[w] = 1 - gside[u];
                    queue_[qt++] = w;
                } else if (gside[w] == gside[u]) {
                    return 0;
                }
            }
        }
    }
    for (int i = 0; i < gm; i++) {
        if (gside[gEA[i]] == 1) {
            int t = gEA[i];
            gEA[i] = gEB[i];
            gEB[i] = t;
        }
    }
    return 1;
}

static int has_edge(int a, int b) {
    const int *row = gnb + (size_t)a * DEG;
    for (int k = 0; k < gdg[a]; k++)
        if (row[k] == b) return 1;
    return 0;
}

static void rep(int v, int old, int nw) {
    int *row = gnb + (size_t)v * DEG;
    for (int k = 0; k < gdg[v]; k++) {
        if (row[k] == old) {
            row[k] = nw;
            return;
        }
    }
}

/* Self-inverse switch: edges i=(A1,B1), j=(A2,B2) become i=(A1,B2), j=(A2,B1). */
static void sw(int i, int j) {
    int A1 = gEA[i], B1 = gEB[i], A2 = gEA[j], B2 = gEB[j];
    gEB[i] = B2;
    gEB[j] = B1;
    rep(A1, B1, B2);
    rep(B2, A2, A1);
    rep(A2, B2, B1);
    rep(B1, A1, A2);
}

/* Number of ordered pairs at distance > DIAM (0 iff valid diameter, connected). */
static int64_t full_cost(void) {
    int W = (gN + 63) / 64;
    uint64_t *X = RA, *Y = RB;
    memset(X, 0, sizeof(uint64_t) * (size_t)gN * W);
    for (int v = 0; v < gN; v++) X[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int t = 0; t < DIAM; t++) {
        for (int v = 0; v < gN; v++) {
            uint64_t *dst = Y + (size_t)v * W;
            const uint64_t *src = X + (size_t)v * W;
            memcpy(dst, src, sizeof(uint64_t) * (size_t)W);
            for (int k = 0; k < gdg[v]; k++) {
                const uint64_t *s2 = X + (size_t)gnb[(size_t)v * DEG + k] * W;
                for (int w = 0; w < W; w++) dst[w] |= s2[w];
            }
        }
        uint64_t *tp = X;
        X = Y;
        Y = tp;
    }
    int64_t tot = 0;
    for (size_t idx = 0; idx < (size_t)gN * W; idx++) tot += pc64(X[idx]);
    return (int64_t)gN * gN - tot;
}

/* Vertex-pair insertion with degree and bipartition preserved.
   Returns 1 on success, 0 if no suitable matching was found, -1 if capacity is full. */
static int insert_pair(void) {
    int d = DEG;
    if (gN + 2 > CAP || gm + d > EMAX) return -1;
    if (gm < d) return 0;
    int idx[MAXDEG];
    int c = 0, tries = 0;
    while (c < d && tries < 4000) {
        tries++;
        int i = rndint(gm);
        int ok = 1;
        for (int k = 0; k < c; k++) {
            if (gEA[idx[k]] == gEA[i] || gEB[idx[k]] == gEB[i]) {
                ok = 0;
                break;
            }
        }
        if (ok) idx[c++] = i;
    }
    if (c < d) return 0;
    int x = gN, y = gN + 1;
    int sa[MAXDEG], sb[MAXDEG];
    for (int k = 0; k < d; k++) {
        sa[k] = gEA[idx[k]];
        sb[k] = gEB[idx[k]];
    }
    for (int k = 0; k < d; k++) {
        int i = idx[k];
        int a = sa[k], b = sb[k];
        gEB[i] = y;          /* edge (a,y) */
        rep(a, b, y);
        rep(b, a, x);
        gEA[gm + k] = x;     /* edge (x,b) */
        gEB[gm + k] = b;
    }
    gN += 2;
    gm += d;
    gdg[x] = d;
    gdg[y] = d;
    for (int k = 0; k < d; k++) {
        gnb[(size_t)x * DEG + k] = sb[k];
        gnb[(size_t)y * DEG + k] = sa[k];
    }
    return 1;
}

static int64_t anneal(int steps, double T0) {
    int64_t cost = full_cost();
    for (int t = 0; t < steps && cost > 0; t++) {
        if ((t & 7) == 0 && elapsed() > TL_TOTAL) break;
        int i = rndint(gm), j = rndint(gm);
        if (i == j) continue;
        int a = gEA[i], b = gEB[i], c = gEA[j], e = gEB[j];
        if (a == c || b == e) continue;
        if (has_edge(a, e) || has_edge(c, b)) continue;
        sw(i, j);
        int64_t c2 = full_cost();
        double T = T0 * (1.0 - (double)t / steps) + 0.05;
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
            cost = c2;
        } else {
            sw(i, j);
        }
    }
    return cost;
}

static void save_best(void) {
    bN = gN;
    bm = gm;
    memcpy(bEA, gEA, sizeof(int) * (size_t)gm);
    memcpy(bEB, gEB, sizeof(int) * (size_t)gm);
}

static void phase2(void) {
    save_best();
    while (elapsed() < TL_TOTAL) {
        gN = bN;
        gm = bm;
        memcpy(gEA, bEA, sizeof(int) * (size_t)bm);
        memcpy(gEB, bEB, sizeof(int) * (size_t)bm);
        if (!rebuild()) break;
        int r = insert_pair();
        if (r < 0) break;
        if (r == 0) continue;
        int64_t c = anneal(PHASE2_STEPS, 3.0);
        if (c == 0) save_best();
    }
}

int main(int argc, char **argv) {
    if (argc < 7) {
        fprintf(stderr, "usage: d D cap seed time frac\n");
        return 1;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    CAP = atoi(argv[3]);
    unsigned long long seed = strtoull(argv[4], NULL, 10);
    TL_TOTAL = atof(argv[5]);
    double frac = atof(argv[6]);
    tstart = now_s();

    rs = (seed + 1) * 0x9E3779B97F4A7C15ULL ^ 0xD1B54A32D192ED03ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 8; i++) rnd64();
    for (int x = 0; x < 256; x++) {
        int c = 0;
        for (int y = x; y; y >>= 1) c += y & 1;
        POP[x] = (uint8_t)c;
    }

    if (DEG < 3 || DIAM < 3 || CAP < 8 || DEG > MAXDEG || CAP > 2000000) {
        printf("0 0\n");
        return 0;
    }
    EMAX = CAP * DEG / 2 + 8 * DEG + 64;
    int WCAP = (CAP + 63) / 64;

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
    gEA = malloc(sizeof(int) * (size_t)EMAX);
    gEB = malloc(sizeof(int) * (size_t)EMAX);
    bEA = malloc(sizeof(int) * (size_t)EMAX);
    bEB = malloc(sizeof(int) * (size_t)EMAX);
    gnb = malloc(sizeof(int) * (size_t)DEG * CAP);
    gdg = malloc(sizeof(int) * (size_t)CAP);
    gside = malloc(sizeof(int) * (size_t)CAP);
    queue_ = malloc(sizeof(int) * (size_t)CAP);
    RA = malloc(sizeof(uint64_t) * (size_t)CAP * WCAP);
    RB = malloc(sizeof(uint64_t) * (size_t)CAP * WCAP);
    if (!AA || !BB || !nbr || !lay || !vol || !nr_lay || !nr_vol || !cur || !scr ||
        !tmpb || !bestnbr || !gEA || !gEB || !bEA || !bEB || !gnb || !gdg || !gside ||
        !queue_ || !RA || !RB) {
        printf("0 0\n");
        return 0;
    }

    /* Optional start graph on stdin. */
    int s_n = 0, s_m = 0;
    if (scanf("%d %d", &s_n, &s_m) != 2) {
        s_n = 0;
        s_m = 0;
    }
    if (s_n < 0 || s_m < 0 || s_n > CAP || s_m > EMAX) {
        s_n = 0;
        s_m = 0;
    }
    for (int i = 0; i < s_m; i++) {
        if (scanf("%d %d", &gEA[i], &gEB[i]) != 2) {
            s_n = 0;
            s_m = 0;
            break;
        }
    }
    gN = s_n;
    gm = s_m;

    /* Phase 1: voltage lifts, larger than the start graph. */
    TL = frac * TL_TOTAL;
    phase1((long long)s_n);

    if (have_best && best_stride > 0) {
        int KG = best_K * best_G;
        gN = best_stride;
        gm = 0;
        for (int u = 0; u < KG; u++) {
            for (int l = 0; l < DEG; l++) {
                gEA[gm] = u;
                gEB[gm] = bestnbr[(size_t)l * best_stride + u];
                gm++;
            }
        }
    }

    if (!load_edges()) {
        printf("0 0\n");
        return 0;
    }

    /* Phase 2: vertex-pair insertion with diameter repair, until the deadline. */
    phase2();

    if (bN <= 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", bN, bm);
    for (int i = 0; i < bm; i++) printf("%d %d\n", bEA[i], bEB[i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact constructions used as start graphs and fallbacks.
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
# Main build: exact start, then one C run (voltage lifts, then vertex-pair
# insertion with diameter repair), with every result validated.
# ----------------------------------------------------------------------------

_MAX_CAP = 2_000_000
_PHASE1_FRACTION = 0.6  # share of the C time spent on voltage lifts


def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = max(1.0, min(0.9 * time_limit, time_limit - 6.0))
    deadline = start + total

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
        remaining = deadline - time.monotonic() - 1.0
        if remaining > 3.0:
            cap = min(lib.moore_bound(d, D), _MAX_CAP)
            if cap > best_n:
                try:
                    text = lib.run_c(
                        C_SOURCE,
                        [d, D, cap, int(seed) & 0x7FFFFFFF, round(remaining, 2), _PHASE1_FRACTION],
                        stdin_graph=best,
                        timeout=remaining + 15.0,
                    )
                    n2, e2 = lib.parse_graph_text(text)
                    consider(n2, e2)
                except Exception:
                    pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
