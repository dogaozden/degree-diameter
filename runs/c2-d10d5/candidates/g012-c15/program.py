import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Three-stage program.
#
# Stage 0: exact constructions (PG(2,q) incidence, W(q) for D = 4) and K_{d,d}
#          as a safe fallback. Every candidate passes lib.is_valid before it
#          is kept.
# Stage 1: the bi-Cayley voltage annealer from the parent (C_PARENT).
# Stage 2 (new, bold): take the best d-regular graph and GROW it by adding
#          vertex pairs. Each pair is wired in by removing d edges and
#          re-attaching their ends to the two new vertices, which keeps every
#          degree exact. Then edge-switch simulated annealing removes the bad
#          pairs (distance > D), using bitset BFS. Only states with zero bad
#          pairs are saved. If repair fails, the last saved state is restored
#          and the growth chunk is halved.
# ----------------------------------------------------------------------------

C_GROW = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXDEG 64

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

static int DEG, DIAM, CAP, N, M, W, WCAP, NLIM;
static int *nb, *dg, *ea, *eb;
static int *bEA, *bEB, bN, bM, haveBest;
static uint64_t *RA, *RB;
static int *BADA, *BADB, *BADC, *BADN;
static double TL, tstart;

static double elapsed(void) {
    return (double)clock() / CLOCKS_PER_SEC - tstart;
}

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* In the adjacency list of v, replace neighbour old by nw. */
static void repl(int v, int old, int nw) {
    int *row = nb + (size_t)v * DEG;
    for (int j = 0; j < dg[v]; j++) {
        if (row[j] == old) {
            row[j] = nw;
            return;
        }
    }
}

static int has_edge(int a, int b) {
    const int *row = nb + (size_t)a * DEG;
    for (int j = 0; j < dg[a]; j++)
        if (row[j] == b) return 1;
    return 0;
}

static int find_edge(int a, int b) {
    for (int k = 0; k < M; k++) {
        if ((ea[k] == a && eb[k] == b) || (ea[k] == b && eb[k] == a)) return k;
    }
    return -1;
}

/* Edge k1 = (a1,b1), k2 = (a2,b2) become (a1,b2), (a2,b1). Degrees are kept.
   Applying it again to the same pair of edge indices undoes it. */
static void do_switch(int k1, int k2) {
    int a1 = ea[k1], b1 = eb[k1], a2 = ea[k2], b2 = eb[k2];
    eb[k1] = b2;
    eb[k2] = b1;
    repl(a1, b1, b2);
    repl(b2, a2, a1);
    repl(a2, b2, b1);
    repl(b1, a1, a2);
}

/* Number of ordered-pair reach failures / 2. bad[v] = vertices at distance > DIAM from v. */
static int64_t eval_bad(int *bad) {
    int n = N, w = W;
    uint64_t *cur = RA, *nxt = RB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * (size_t)w);
    for (int v = 0; v < n; v++) cur[(size_t)v * w + (v >> 6)] |= 1ULL << (v & 63);
    for (int t = 0; t < DIAM; t++) {
        int changed = 0;
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + (size_t)v * w;
            const uint64_t *src = cur + (size_t)v * w;
            memcpy(dst, src, sizeof(uint64_t) * (size_t)w);
            const int *row = nb + (size_t)v * DEG;
            for (int j = 0; j < dg[v]; j++) {
                const uint64_t *s2 = cur + (size_t)row[j] * w;
                for (int k = 0; k < w; k++) dst[k] |= s2[k];
            }
            if (!changed && memcmp(dst, src, sizeof(uint64_t) * (size_t)w) != 0) changed = 1;
        }
        uint64_t *tmp = cur;
        cur = nxt;
        nxt = tmp;
        if (!changed) break;
    }
    int64_t s = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        const uint64_t *row = cur + (size_t)v * w;
        for (int k = 0; k < w; k++) c += pc64(row[k]);
        bad[v] = n - c;
        s += n - c;
    }
    return s / 2;
}

/* Edge-switch annealing on the current graph. Returns 1 if no bad pairs remain. */
static int repair(int maxmoves) {
    int64_t cost = eval_bad(BADC);
    double temp0 = 0.5 + 0.02 * (double)cost;
    for (int t = 0; t < maxmoves && cost > 0; t++) {
        if ((t & 7) == 0 && elapsed() > TL) return 0;
        int k1, k2;
        if (rnd01() < 0.6) {
            /* Pick a random bad vertex, then one of its edges. */
            int nbad = 0, v = -1;
            for (int x = 0; x < N; x++) {
                if (BADC[x] > 0) {
                    nbad++;
                    if (rndint(nbad) == 0) v = x;
                }
            }
            if (v < 0) break;
            int u = nb[(size_t)v * DEG + rndint(dg[v])];
            k1 = find_edge(v, u);
            if (k1 < 0) continue;
        } else {
            k1 = rndint(M);
        }
        k2 = rndint(M);
        if (k1 == k2) continue;
        int a1 = ea[k1], b1 = eb[k1], a2 = ea[k2], b2 = eb[k2];
        if (a1 == a2 || b1 == b2) continue;
        if (has_edge(a1, b2) || has_edge(a2, b1)) continue;
        do_switch(k1, k2);
        int64_t c2 = eval_bad(BADN);
        double temp = temp0 * (1.0 - (double)t / maxmoves) + 0.05;
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
            int *tb = BADC;
            BADC = BADN;
            BADN = tb;
        } else {
            do_switch(k1, k2);
        }
    }
    return cost == 0;
}

/* Add two vertices x (side 1) and y (side 0). Take DEG edges with pairwise
   distinct ends, both among the old vertices (< NLIM). Each chosen edge (a,b)
   becomes (a,x) and (b,y), so a and b keep their degree. */
static int grow_once(void) {
    if (N + 2 > CAP) return 0;
    int ua[MAXDEG], ub[MAXDEG], ch[MAXDEG];
    int cnt = 0, tries = 0;
    while (cnt < DEG && tries < 50000) {
        tries++;
        int k = rndint(M);
        int a = ea[k], b = eb[k];
        if (a >= NLIM || b >= NLIM) continue;
        int ok = 1;
        for (int i = 0; i < cnt; i++) {
            if (ua[i] == a || ub[i] == b) {
                ok = 0;
                break;
            }
        }
        if (!ok) continue;
        ua[cnt] = a;
        ub[cnt] = b;
        ch[cnt] = k;
        cnt++;
    }
    if (cnt < DEG) return 0;
    int x = N, y = N + 1;
    dg[x] = 0;
    dg[y] = 0;
    for (int i = 0; i < DEG; i++) {
        int a = ua[i], b = ub[i], k = ch[i];
        repl(a, b, x);
        repl(b, a, y);
        nb[(size_t)x * DEG + i] = a;
        nb[(size_t)y * DEG + i] = b;
        ea[k] = a;
        eb[k] = x;
        ea[M] = y;
        eb[M] = b;
        M++;
    }
    dg[x] = DEG;
    dg[y] = DEG;
    N += 2;
    W = (N + 63) / 64;
    return 1;
}

static void save_best(void) {
    haveBest = 1;
    bN = N;
    bM = M;
    memcpy(bEA, ea, sizeof(int) * (size_t)M);
    memcpy(bEB, eb, sizeof(int) * (size_t)M);
}

static void restore_best(void) {
    N = bN;
    M = bM;
    W = (N + 63) / 64;
    memcpy(ea, bEA, sizeof(int) * (size_t)M);
    memcpy(eb, bEB, sizeof(int) * (size_t)M);
    for (int v = 0; v < N; v++) dg[v] = 0;
    for (int k = 0; k < M; k++) {
        int a = ea[k], b = eb[k];
        nb[(size_t)a * DEG + dg[a]++] = b;
        nb[(size_t)b * DEG + dg[b]++] = a;
    }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    TL = atof(argv[4]);
    tstart = (double)clock() / CLOCKS_PER_SEC;

    rs = (seed + 7) * 0x9E3779B97F4A7C15ULL ^ 0xA24BAED4963EE407ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 8; i++) rnd64();

    if (DEG < 3 || DEG > MAXDEG || DIAM < 2) {
        printf("0 0\n");
        return 0;
    }
    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 <= 0 || m0 <= 0 || n0 > 1000000) {
        printf("0 0\n");
        return 0;
    }
    CAP = n0 + 4096;
    WCAP = (CAP + 63) / 64;
    int ecap = CAP * DEG + 2 * DEG + 8;

    int *U = malloc(sizeof(int) * (size_t)m0);
    int *V = malloc(sizeof(int) * (size_t)m0);
    nb = malloc(sizeof(int) * (size_t)CAP * DEG);
    dg = calloc((size_t)CAP, sizeof(int));
    ea = malloc(sizeof(int) * (size_t)ecap);
    eb = malloc(sizeof(int) * (size_t)ecap);
    bEA = malloc(sizeof(int) * (size_t)ecap);
    bEB = malloc(sizeof(int) * (size_t)ecap);
    BADA = malloc(sizeof(int) * (size_t)CAP);
    BADB = malloc(sizeof(int) * (size_t)CAP);
    RA = malloc(sizeof(uint64_t) * (size_t)CAP * WCAP);
    RB = malloc(sizeof(uint64_t) * (size_t)CAP * WCAP);
    int *col = malloc(sizeof(int) * (size_t)CAP);
    int *stk = malloc(sizeof(int) * (size_t)CAP);
    if (!U || !V || !nb || !dg || !ea || !eb || !bEA || !bEB || !BADA || !BADB ||
        !RA || !RB || !col || !stk) {
        printf("0 0\n");
        return 0;
    }

    int bad = 0;
    for (int k = 0; k < m0; k++) {
        if (scanf("%d %d", &U[k], &V[k]) != 2) {
            bad = 1;
            break;
        }
        if (U[k] < 0 || U[k] >= n0 || V[k] < 0 || V[k] >= n0 || U[k] == V[k]) {
            bad = 1;
            break;
        }
        int u = U[k], v = V[k];
        if (dg[u] >= DEG || dg[v] >= DEG) {
            bad = 1;
            break;
        }
        nb[(size_t)u * DEG + dg[u]++] = v;
        nb[(size_t)v * DEG + dg[v]++] = u;
    }
    if (bad) {
        printf("0 0\n");
        return 0;
    }
    for (int v = 0; v < n0; v++)
        if (dg[v] != DEG) bad = 1;
    if (bad) {
        printf("0 0\n");
        return 0;
    }

    /* Bipartition by BFS. */
    for (int v = 0; v < n0; v++) col[v] = -1;
    for (int s = 0; s < n0 && !bad; s++) {
        if (col[s] != -1) continue;
        col[s] = 0;
        int sp = 0;
        stk[sp++] = s;
        while (sp > 0) {
            int u = stk[--sp];
            for (int j = 0; j < dg[u]; j++) {
                int w = nb[(size_t)u * DEG + j];
                if (col[w] == -1) {
                    col[w] = 1 - col[u];
                    stk[sp++] = w;
                } else if (col[w] == col[u]) {
                    bad = 1;
                }
            }
        }
    }
    if (bad) {
        printf("0 0\n");
        return 0;
    }
    for (int k = 0; k < m0; k++) {
        if (col[U[k]] == 0) {
            ea[k] = U[k];
            eb[k] = V[k];
        } else {
            ea[k] = V[k];
            eb[k] = U[k];
        }
    }

    N = n0;
    M = m0;
    W = (N + 63) / 64;
    BADC = BADA;
    BADN = BADB;
    int64_t c0 = eval_bad(BADC);
    if (c0 > 0 && !repair(3000)) {
        printf("0 0\n");
        return 0;
    }
    save_best();

    int chunk = 1, fails = 0;
    while (fails < 8 && elapsed() < TL) {
        NLIM = N;
        int added = 0;
        for (int c = 0; c < chunk; c++) {
            if (!grow_once()) break;
            added++;
        }
        if (added == 0) break;
        int ok = repair(300 + 40 * added);
        if (ok) {
            save_best();
            fails = 0;
            if (chunk < 64) chunk *= 2;
        } else {
            restore_best();
            fails++;
            if (chunk > 1) chunk /= 2;
        }
    }

    if (!haveBest) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", bN, bM);
    for (int k = 0; k < bM; k++) printf("%d %d\n", bEA[k], bEB[k]);
    return 0;
}
"""


C_PARENT = r"""
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
# Exact constructions.
# ----------------------------------------------------------------------------

_MAX_CAP = 2_000_000


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
    """True if every vertex 0..n-1 has degree exactly d."""
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
    return all(x == d for x in deg)


# ----------------------------------------------------------------------------
# Main build.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    usable = max(1.0, float(time_limit) - 8.0)
    deadline = start + usable

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]  # even cycle, diameter D

    # Safe fallback: K_{d,d} has diameter 2.
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

    if D == 4 and time.monotonic() < start + 0.2 * usable:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    if d >= 3 and D >= 3:
        # Stage 1: parent bi-Cayley voltage annealer.
        cap = min(lib.moore_bound(d, D), _MAX_CAP)
        p1 = min(0.35 * usable, deadline - time.monotonic() - 10.0)
        if p1 > 2.0 and cap > best_n:
            try:
                text = lib.run_c(C_PARENT,
                                 [d, D, best_n, cap, int(seed) & 0x7FFFFFFF, round(p1, 2)],
                                 timeout=p1 + 20.0)
                n2, e2 = lib.parse_graph_text(text)
                consider(n2, e2)
            except Exception:
                pass

        # Stage 2: grow the best regular graph by vertex pairs, repairing with edge switches.
        remaining = deadline - time.monotonic() - 2.0
        if remaining > 3.0 and _is_regular(best_n, best[1], d):
            try:
                text = lib.run_c(C_GROW,
                                 [d, D, int(seed) & 0x7FFFFFFF, round(remaining, 2)],
                                 stdin_graph=best,
                                 timeout=remaining + 20.0)
                n2, e2 = lib.parse_graph_text(text)
                consider(n2, e2)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
