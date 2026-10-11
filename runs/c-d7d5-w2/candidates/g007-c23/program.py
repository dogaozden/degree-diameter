import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Engine A: bi-Cayley lifts over one group, K = 1 (parent's search).
#
# Usage: prog DEG DIAM m k2 r seed slice_seconds
# ----------------------------------------------------------------------------

BICAY_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define BIGC (1 << 30)

static int DEG, DIAM, MM, K2, G;
static int *mt, *iv, *POWR, *S, *IS, *bestS, *stampv, *qu;
static int stamp = 0;
static uint64_t rs = 88172645463325252ULL;

static inline uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static inline int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static inline double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double elapsed(clock_t t0) {
    return (double)(clock() - t0) / (double)CLOCKS_PER_SEC;
}

static int gmul(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, d2 = y % K2;
    long long t = ((long long)a + (long long)POWR[b] * c) % MM;
    return (int)(t * K2 + (b + d2) % K2);
}

static int in_set(int x) {
    for (int t = 0; t < DEG; t++) if (S[t] == x) return 1;
    return 0;
}

static int in_prefix(int x, int upto) {
    for (int t = 0; t < upto; t++) if (S[t] == x) return 1;
    return 0;
}

static void set_inv(void) {
    for (int t = 0; t < DEG; t++) IS[t] = iv[S[t]];
}

static int reach_count(int src) {
    if (stamp >= 0x7ffffff0) {
        memset(stampv, 0, sizeof(int) * (size_t)(2 * G));
        stamp = 0;
    }
    stamp++;
    int head = 0, tail = 0;
    stampv[src] = stamp;
    qu[tail++] = src;
    for (int lv = 0; lv < DIAM && head < tail; lv++) {
        int end = tail;
        while (head < end) {
            int u = qu[head++];
            if (u < G) {
                const int *row = mt + (size_t)u * G;
                for (int t = 0; t < DEG; t++) {
                    int v = G + row[S[t]];
                    if (stampv[v] != stamp) { stampv[v] = stamp; qu[tail++] = v; }
                }
            } else {
                const int *row = mt + (size_t)(u - G) * G;
                for (int t = 0; t < DEG; t++) {
                    int v = row[IS[t]];
                    if (stampv[v] != stamp) { stampv[v] = stamp; qu[tail++] = v; }
                }
            }
        }
    }
    return tail;
}

static int cost_fn(void) {
    int nv = 2 * G;
    return (nv - reach_count(0)) + (nv - reach_count(G));
}

int main(int argc, char **argv) {
    if (argc < 8) { printf("0 0\n"); return 0; }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    MM = atoi(argv[3]);
    K2 = atoi(argv[4]);
    int r = atoi(argv[5]);
    uint64_t seed = strtoull(argv[6], NULL, 10);
    double slice = atof(argv[7]);

    if (DEG < 1 || DIAM < 1 || MM < 1 || K2 < 1) { printf("0 0\n"); return 0; }
    G = MM * K2;
    if (G <= DEG || G > 2400) { printf("0 0\n"); return 0; }

    POWR = malloc(sizeof(int) * (size_t)K2);
    if (!POWR) { printf("0 0\n"); return 0; }
    POWR[0] = 1 % MM;
    for (int b = 1; b < K2; b++) POWR[b] = (int)((long long)POWR[b - 1] * r % MM);
    if (((long long)POWR[K2 - 1] * r) % MM != 1 % MM) { printf("0 0\n"); return 0; }
    {
        int a1 = r, b1 = MM;
        while (b1) { int t = a1 % b1; a1 = b1; b1 = t; }
        if (a1 != 1) { printf("0 0\n"); return 0; }
    }

    mt = malloc(sizeof(int) * (size_t)G * (size_t)G);
    iv = malloc(sizeof(int) * (size_t)G);
    S = malloc(sizeof(int) * (size_t)DEG);
    IS = malloc(sizeof(int) * (size_t)DEG);
    bestS = malloc(sizeof(int) * (size_t)DEG);
    stampv = calloc((size_t)(2 * G), sizeof(int));
    qu = malloc(sizeof(int) * (size_t)(2 * G));
    if (!mt || !iv || !S || !IS || !bestS || !stampv || !qu) { printf("0 0\n"); return 0; }

    for (int x = 0; x < G; x++)
        for (int y = 0; y < G; y++)
            mt[(size_t)x * G + y] = gmul(x, y);
    for (int x = 0; x < G; x++) {
        iv[x] = 0;
        for (int y = 0; y < G; y++)
            if (mt[(size_t)x * G + y] == 0) { iv[x] = y; break; }
    }

    rs = seed * 0x9E3779B97F4A7C15ULL ^ 0xABCDEFULL;
    if (rs == 0) rs = 1;

    clock_t t0 = clock();
    int bestCost = BIGC, found = 0;
    const int RL = 30000;

    while (!found && elapsed(t0) < slice) {
        double T0;
        if (bestCost >= BIGC || rnd01() < 0.3) {
            for (int t = 0; t < DEG; t++) {
                int x;
                do { x = rndint(G); } while (in_prefix(x, t));
                S[t] = x;
            }
            T0 = 3.0;
        } else {
            memcpy(S, bestS, sizeof(int) * (size_t)DEG);
            int kick = 1 + DEG / 3;
            for (int q = 0; q < kick; q++) {
                int t = rndint(DEG);
                int x = rndint(G);
                if (!in_set(x)) S[t] = x;
            }
            T0 = 1.0;
        }
        set_inv();
        int cur = cost_fn();
        if (cur < bestCost) { bestCost = cur; memcpy(bestS, S, sizeof(int) * (size_t)DEG); }
        if (cur == 0) { found = 1; break; }

        for (int it = 0; it < RL; it++) {
            if ((it & 127) == 0 && elapsed(t0) >= slice) break;
            double T = T0 * (1.0 - (double)it / RL) + 0.02;
            int t = rndint(DEG);
            int x = rndint(G);
            if (in_set(x)) continue;
            int old = S[t], oldI = IS[t];
            S[t] = x;
            IS[t] = iv[x];
            int nc = cost_fn();
            if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
                cur = nc;
                if (cur < bestCost) { bestCost = cur; memcpy(bestS, S, sizeof(int) * (size_t)DEG); }
                if (cur == 0) { found = 1; break; }
            } else {
                S[t] = old;
                IS[t] = oldI;
            }
        }
    }

    if (found) {
        printf("%d %d\n", 2 * G, G * DEG);
        for (int g = 0; g < G; g++)
            for (int t = 0; t < DEG; t++)
                printf("%d %d\n", g, G + mt[(size_t)g * G + S[t]]);
    } else {
        printf("0 0\n");
    }
    fflush(stdout);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Engine B: voltage annealing of general bi-Cayley lifts (parent baseline).
#
# Usage: prog d D K m k2 r seed slice_seconds
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define PEN 1000
#define BIGCOST (1 << 30)
#define STAG 8000

static int DEG, DIAM, K, MM, K2, G, N, NE;
static int *POWR;
static int *dI, *dJ, *dS, *perm, *adj, *cnt, *fr, *nx;
static int *bestS, *bestJ;
static uint32_t *vis;
static uint32_t stamp = 0;
static uint64_t rs = 88172645463325252ULL;

static inline uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static inline int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static inline double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double elapsed(clock_t t0) {
    return (double)(clock() - t0) / (double)CLOCKS_PER_SEC;
}

static int gcd_int(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static int gmul(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, dd = y % K2;
    long long t = (a + (long long)POWR[b] * c) % MM;
    return (int)(t * K2 + (b + dd) % K2);
}

static void set_perm(int e) {
    int s = dS[e];
    int *pm = perm + (size_t)e * G;
    for (int g = 0; g < G; g++) pm[g] = gmul(g, s);
}

static int cost_fn(void) {
    int dup = 0;
    for (int e1 = 0; e1 < NE; e1++)
        for (int e2 = e1 + 1; e2 < NE; e2++)
            if (dI[e1] == dI[e2] && dJ[e1] == dJ[e2] && dS[e1] == dS[e2]) dup++;

    memset(cnt, 0, sizeof(int) * (size_t)N);
    for (int e = 0; e < NE; e++) {
        int ba = dI[e] * G, bb = (K + dJ[e]) * G;
        const int *pm = perm + (size_t)e * G;
        for (int g = 0; g < G; g++) {
            int a = ba + g, b = bb + pm[g];
            adj[(size_t)a * DEG + cnt[a]++] = b;
            adj[(size_t)b * DEG + cnt[b]++] = a;
        }
    }

    int total = 0;
    for (int ri = 0; ri < 2 * K; ri++) {
        int src = ri * G;
        if (stamp == 0xFFFFFFFFu) {
            memset(vis, 0, sizeof(uint32_t) * (size_t)N);
            stamp = 0;
        }
        stamp++;
        vis[src] = stamp;
        int *cur = fr, *nxt = nx;
        int fn = 1, reached = 1;
        cur[0] = src;
        for (int lv = 0; lv < DIAM && fn > 0; lv++) {
            int nn = 0;
            for (int q = 0; q < fn; q++) {
                int u = cur[q];
                const int *au = adj + (size_t)u * DEG;
                for (int t = 0; t < DEG; t++) {
                    int v = au[t];
                    if (vis[v] != stamp) {
                        vis[v] = stamp;
                        nxt[nn++] = v;
                    }
                }
            }
            reached += nn;
            int *tmp = cur; cur = nxt; nxt = tmp;
            fn = nn;
        }
        total += N - reached;
    }
    return total + PEN * dup;
}

static void save_best(void) {
    memcpy(bestS, dS, sizeof(int) * (size_t)NE);
    memcpy(bestJ, dJ, sizeof(int) * (size_t)NE);
}

int main(int argc, char **argv) {
    if (argc < 9) {
        fprintf(stderr, "usage: prog d D K m k2 r seed slice\n");
        return 1;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    K = atoi(argv[3]);
    MM = atoi(argv[4]);
    K2 = atoi(argv[5]);
    int r = atoi(argv[6]);
    uint64_t seed = strtoull(argv[7], NULL, 10);
    double slice = atof(argv[8]);

    if (DEG < 1 || DIAM < 1 || K < 1 || MM < 1 || K2 < 1 || K2 > 4096) {
        printf("0 0\n");
        return 0;
    }
    if (gcd_int(r, MM) != 1) { printf("0 0\n"); return 0; }
    POWR = malloc(sizeof(int) * (size_t)K2);
    if (!POWR) { printf("0 0\n"); return 0; }
    POWR[0] = 1 % MM;
    for (int b = 1; b < K2; b++) POWR[b] = (int)((long long)POWR[b - 1] * r % MM);
    if (((long long)POWR[K2 - 1] * r) % MM != 1 % MM) { printf("0 0\n"); return 0; }

    G = MM * K2;
    N = 2 * K * G;
    NE = DEG * K;

    rs = seed * 0x9E3779B97F4A7C15ULL ^ 0x1234567ULL;
    if (rs == 0) rs = 1;

    dI = malloc(sizeof(int) * NE);
    dJ = malloc(sizeof(int) * NE);
    dS = malloc(sizeof(int) * NE);
    bestS = malloc(sizeof(int) * NE);
    bestJ = malloc(sizeof(int) * NE);
    perm = malloc(sizeof(int) * (size_t)NE * G);
    adj = malloc(sizeof(int) * (size_t)N * DEG);
    cnt = malloc(sizeof(int) * N);
    fr = malloc(sizeof(int) * N);
    nx = malloc(sizeof(int) * N);
    vis = calloc(N, sizeof(uint32_t));
    int *p = malloc(sizeof(int) * K);
    if (!dI || !dJ || !dS || !bestS || !bestJ || !perm || !adj || !cnt || !fr || !nx || !vis || !p) {
        printf("0 0\n");
        return 0;
    }

    clock_t t0 = clock();
    int found = 0;
    int bestCost = BIGCOST;
    const int RL = 60000;

    while (!found && elapsed(t0) < slice) {
        double T0;
        if (bestCost >= BIGCOST || rnd01() < 0.25) {
            for (int l = 0; l < DEG; l++) {
                for (int i = 0; i < K; i++) p[i] = i;
                for (int i = K - 1; i > 0; i--) {
                    int j = rndint(i + 1);
                    int t = p[i]; p[i] = p[j]; p[j] = t;
                }
                for (int i = 0; i < K; i++) {
                    dI[l * K + i] = i;
                    dJ[l * K + i] = p[i];
                }
            }
            for (int e = 0; e < NE; e++) {
                dS[e] = rndint(G);
                set_perm(e);
            }
            T0 = 2.0;
        } else {
            memcpy(dJ, bestJ, sizeof(int) * (size_t)NE);
            memcpy(dS, bestS, sizeof(int) * (size_t)NE);
            int kick = NE / 8 + 1;
            for (int q = 0; q < kick; q++) dS[rndint(NE)] = rndint(G);
            for (int e = 0; e < NE; e++) set_perm(e);
            T0 = 0.8;
        }
        int cur = cost_fn();
        if (cur < bestCost) { bestCost = cur; save_best(); }
        if (cur == 0) { found = 1; break; }

        int runBest = cur;
        int since = 0;
        for (int it = 0; it < RL; it++) {
            if ((it & 255) == 0 && elapsed(t0) >= slice) break;
            double T = T0 * (1.0 - (double)it / RL) + 0.05;
            if (K > 1 && rnd01() < 0.3) {
                int l = rndint(DEG);
                int i1 = rndint(K);
                int i2 = rndint(K - 1);
                if (i2 >= i1) i2++;
                int e1 = l * K + i1, e2 = l * K + i2;
                int t = dJ[e1]; dJ[e1] = dJ[e2]; dJ[e2] = t;
                int nc = cost_fn();
                if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
                    cur = nc;
                } else {
                    t = dJ[e1]; dJ[e1] = dJ[e2]; dJ[e2] = t;
                }
            } else {
                int e = rndint(NE);
                int old = dS[e];
                int ns = rndint(G);
                if (ns == old) continue;
                dS[e] = ns;
                set_perm(e);
                int nc = cost_fn();
                if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
                    cur = nc;
                } else {
                    dS[e] = old;
                    set_perm(e);
                }
            }
            if (cur < bestCost) { bestCost = cur; save_best(); }
            if (cur < runBest) { runBest = cur; since = 0; }
            else if (++since > STAG) break;
            if (cur == 0) { found = 1; break; }
        }
    }

    if (found) {
        printf("%d %d\n", N, NE * G);
        for (int e = 0; e < NE; e++) {
            for (int g = 0; g < G; g++) {
                printf("%d %d\n", dI[e] * G + g, (K + dJ[e]) * G + perm[(size_t)e * G + g]);
            }
        }
    } else {
        printf("0 0\n");
    }
    fflush(stdout);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Engine C (new, bold): non-symmetric repair search on the whole graph.
#
# The start graph (or an empty start) is a bipartite graph with sides A
# (colour 0) and B (colour 1). EXTRA new vertices are added to each side.
# New vertices are spliced in by subdividing random old edges, then the
# spare degree is filled greedily. Simulated annealing then performs
# degree-preserving edge switches (a1,b1),(a2,b2) -> (a1,b2),(a2,b1) and
# greedy edge additions between deficient vertices. Cost = number of
# unordered vertex pairs at distance > DIAM, computed with bitsets.
#
# Usage: prog DEG DIAM EXTRA seed slice_seconds   (graph on stdin, or "0 0")
# Prints a valid graph ("n m" + edges) or "0 0".
# ----------------------------------------------------------------------------

REPAIR_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 3000

static int DEG, DIAM, EXTRA, N0, N, NE, W;
static int *side, *nbr, *ndeg, *ea, *eb, *ql, *dA, *dB;
static char *am;
static uint64_t *CUR, *NXT;
static uint64_t rs = 88172645463325252ULL;

static inline uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static inline int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static inline double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double elapsed(clock_t t0) {
    return (double)(clock() - t0) / (double)CLOCKS_PER_SEC;
}

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void add_nb(int v, int u) {
    nbr[(size_t)v * DEG + ndeg[v]++] = u;
}

static void rem_nb(int v, int u) {
    int *row = nbr + (size_t)v * DEG;
    for (int k = 0; k < ndeg[v]; k++) {
        if (row[k] == u) { row[k] = row[ndeg[v] - 1]; ndeg[v]--; return; }
    }
}

static void put_edge(int e, int a, int b) {
    ea[e] = a; eb[e] = b;
    am[(size_t)a * N + b] = 1; am[(size_t)b * N + a] = 1;
    add_nb(a, b); add_nb(b, a);
}

static void del_edge(int e) {
    int a = ea[e], b = eb[e];
    am[(size_t)a * N + b] = 0; am[(size_t)b * N + a] = 0;
    rem_nb(a, b); rem_nb(b, a);
}

/* Number of unordered pairs at distance > DIAM. */
static long long cost_fn(void) {
    memset(CUR, 0, sizeof(uint64_t) * (size_t)N * W);
    for (int v = 0; v < N; v++) CUR[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int s = 0; s < DIAM; s++) {
        for (int v = 0; v < N; v++) {
            uint64_t *dst = NXT + (size_t)v * W;
            const uint64_t *src = CUR + (size_t)v * W;
            memcpy(dst, src, sizeof(uint64_t) * (size_t)W);
            for (int k = 0; k < ndeg[v]; k++) {
                int u = nbr[(size_t)v * DEG + k];
                const uint64_t *su = CUR + (size_t)u * W;
                for (int w = 0; w < W; w++) dst[w] |= su[w];
            }
        }
        uint64_t *tmp = CUR; CUR = NXT; NXT = tmp;
    }
    long long bad = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += pc64(CUR[(size_t)v * W + w]);
        bad += N - c;
    }
    return bad / 2;
}

/* Greedily add edges between deficient vertices of opposite sides. */
static void initial_fill(void) {
    int changed = 1;
    while (changed) {
        changed = 0;
        int off = rndint(N);
        for (int ia = 0; ia < N; ia++) {
            int a = (ia + off) % N;
            if (side[a] != 0 || ndeg[a] >= DEG) continue;
            int off2 = rndint(N);
            for (int ib = 0; ib < N && ndeg[a] < DEG; ib++) {
                int b = (ib + off2) % N;
                if (side[b] != 1 || ndeg[b] >= DEG || am[(size_t)a * N + b]) continue;
                put_edge(NE, a, b);
                NE++;
                changed = 1;
            }
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 6) { printf("0 0\n"); return 0; }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    EXTRA = atoi(argv[3]);
    uint64_t seed = strtoull(argv[4], NULL, 10);
    double slice = atof(argv[5]);

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { n0 = 0; m0 = 0; }
    if (DEG < 2 || DIAM < 1 || EXTRA < 0 || n0 < 0 || m0 < 0) { printf("0 0\n"); return 0; }

    if (n0 == 0) { N0 = 0; N = 2 * EXTRA; }
    else { N0 = n0; N = n0 + 2 * EXTRA; }
    if (N < 2 * DEG || N > MAXN) { printf("0 0\n"); return 0; }
    W = (N + 63) / 64;

    side = calloc(N, sizeof(int));
    nbr = malloc(sizeof(int) * (size_t)N * DEG);
    ndeg = calloc(N, sizeof(int));
    ea = malloc(sizeof(int) * (size_t)N * DEG + 16);
    eb = malloc(sizeof(int) * (size_t)N * DEG + 16);
    ql = malloc(sizeof(int) * N);
    dA = malloc(sizeof(int) * N);
    dB = malloc(sizeof(int) * N);
    am = calloc((size_t)N * N, 1);
    CUR = malloc(sizeof(uint64_t) * (size_t)N * W);
    NXT = malloc(sizeof(uint64_t) * (size_t)N * W);
    int *eu = malloc(sizeof(int) * (size_t)(m0 + 1));
    int *ev = malloc(sizeof(int) * (size_t)(m0 + 1));
    int *tdeg = calloc(N, sizeof(int));
    int *col = malloc(sizeof(int) * N);
    if (!side || !nbr || !ndeg || !ea || !eb || !ql || !dA || !dB || !am || !CUR || !NXT ||
        !eu || !ev || !tdeg || !col) {
        printf("0 0\n");
        return 0;
    }

    rs = seed * 0x9E3779B97F4A7C15ULL ^ 0x5151ULL;
    if (rs == 0) rs = 1;

    int ok = 1;
    for (int i = 0; i < m0 && ok; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { ok = 0; break; }
        if (u < 0 || v < 0 || u >= N0 || v >= N0 || u == v) { ok = 0; break; }
        if (am[(size_t)u * N + v]) { ok = 0; break; }
        am[(size_t)u * N + v] = 1; am[(size_t)v * N + u] = 1;
        tdeg[u]++; tdeg[v]++;
        eu[i] = u; ev[i] = v;
    }
    for (int v = 0; v < N0 && ok; v++) if (tdeg[v] > DEG) ok = 0;

    /* Bipartition of the start graph by BFS colouring. */
    for (int v = 0; v < N; v++) col[v] = -1;
    for (int s = 0; s < N0 && ok; s++) {
        if (col[s] != -1) continue;
        col[s] = 0;
        int qh = 0, qt = 0;
        ql[qt++] = s;
        while (qh < qt && ok) {
            int u = ql[qh++];
            for (int v = 0; v < N0; v++) {
                if (!am[(size_t)u * N + v]) continue;
                if (col[v] == -1) { col[v] = 1 - col[u]; ql[qt++] = v; }
                else if (col[v] == col[u]) { ok = 0; break; }
            }
        }
    }
    if (!ok) { printf("0 0\n"); return 0; }

    /* Reset adjacency and set sides; new A vertices first, then new B. */
    memset(am, 0, (size_t)N * N);
    for (int v = 0; v < N0; v++) side[v] = col[v];
    for (int v = N0; v < N; v++) side[v] = (v < N0 + EXTRA) ? 0 : 1;

    NE = 0;
    for (int i = 0; i < m0; i++) {
        int u = eu[i], v = ev[i];
        if (side[u] == 0) put_edge(NE, u, v);
        else put_edge(NE, v, u);
        NE++;
    }

    /* Splice each new pair (x in A, y in B) into a random old edge (a, b):
       the edge becomes (a, y) and (x, b), and (x, y) is added. */
    for (int i = 0; i < EXTRA && N0 > 0 && NE > 0; i++) {
        int x = N0 + i, y = N0 + EXTRA + i;
        int e = -1;
        for (int tr = 0; tr < 4000; tr++) {
            int c = rndint(NE);
            if (ea[c] < N0 && eb[c] < N0) { e = c; break; }
        }
        if (e < 0) break;
        int a = ea[e], b = eb[e];
        del_edge(e);
        put_edge(e, a, y);
        put_edge(NE, x, b);
        NE++;
        put_edge(NE, x, y);
        NE++;
    }

    initial_fill();

    long long cur = cost_fn();
    clock_t t0 = clock();
    const double T0 = 3.0, T1 = 0.05;
    double T = T0;
    long long it = 0;

    while (cur > 0) {
        if ((it & 15) == 0) {
            double el = elapsed(t0);
            if (el >= slice) break;
            double fr = el / slice;
            T = T0 * pow(T1 / T0, fr);
        }
        it++;

        if (rnd01() < 0.05) {
            /* Greedy addition between deficient vertices; never raises the cost. */
            int na = 0, nb2 = 0;
            for (int v = 0; v < N; v++) {
                if (ndeg[v] >= DEG) continue;
                if (side[v] == 0) dA[na++] = v;
                else dB[nb2++] = v;
            }
            if (na > 0 && nb2 > 0) {
                for (int tr = 0; tr < 50; tr++) {
                    int x = dA[rndint(na)], y = dB[rndint(nb2)];
                    if (!am[(size_t)x * N + y]) {
                        put_edge(NE, x, y);
                        NE++;
                        cur = cost_fn();
                        break;
                    }
                }
            }
            continue;
        }

        if (NE < 2) continue;
        int e1 = rndint(NE), e2 = rndint(NE);
        if (e1 == e2) continue;
        int a1 = ea[e1], b1 = eb[e1], a2 = ea[e2], b2 = eb[e2];
        if (a1 == a2 || b1 == b2) continue;
        if (am[(size_t)a1 * N + b2] || am[(size_t)a2 * N + b1]) continue;

        del_edge(e1); del_edge(e2);
        put_edge(e1, a1, b2); put_edge(e2, a2, b1);
        long long nc = cost_fn();
        if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
            cur = nc;
        } else {
            del_edge(e1); del_edge(e2);
            put_edge(e1, a1, b1); put_edge(e2, a2, b2);
        }
    }

    if (cur == 0) {
        printf("%d %d\n", N, NE);
        for (int e = 0; e < NE; e++) printf("%d %d\n", ea[e], eb[e]);
    } else {
        printf("0 0\n");
    }
    fflush(stdout);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact / safe constructions.
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
# Greedy spare-degree extension (no-op for regular graphs).
# ----------------------------------------------------------------------------

def _two_colour(n, edges):
    """Return a 0/1 side label per vertex (bipartition), or None if not bipartite."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    col = [-1] * n
    for s in range(n):
        if col[s] != -1:
            continue
        col[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if col[v] == -1:
                    col[v] = 1 - col[u]
                    stack.append(v)
                elif col[v] == col[u]:
                    return None
    return col


def _extend_spare(n, edges, d, D, deadline):
    """Greedily add fresh vertex pairs while the graph stays valid. Returns (n, edges)."""
    if d < 2:
        return n, edges
    col = _two_colour(n, edges)
    if col is None:
        return n, edges
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
    edges = list(edges)
    while time.monotonic() < deadline:
        A_sp = [v for v in range(n) if col[v] == 0 and deg[v] < d]
        B_sp = [v for v in range(n) if col[v] == 1 and deg[v] < d]
        if not A_sp or not B_sp:
            break
        grown = False
        for k in range(d - 1, 0, -1):
            if k > len(A_sp) or k > len(B_sp):
                continue
            a, b = n, n + 1
            cand_new = [(a, b)] + [(a, x) for x in B_sp[:k]] + [(b, y) for y in A_sp[:k]]
            cand = edges + cand_new
            if lib.is_valid(n + 2, cand, d, D):
                edges = cand
                n += 2
                col += [0, 1]
                deg += [0, 0]
                deg[a] = k + 1
                deg[b] = k + 1
                for x in B_sp[:k]:
                    deg[x] += 1
                for y in A_sp[:k]:
                    deg[y] += 1
                grown = True
                break
        if not grown:
            break
    return n, edges


# ----------------------------------------------------------------------------
# Group sampling (parent's lift search).
# ----------------------------------------------------------------------------

K2_CHOICES = [1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 21, 24,
              27, 28, 30, 36, 40, 42, 49, 54, 56, 63, 72, 81, 84, 96, 108, 121,
              128, 162, 243]

EXTRA_CHOICES = [2, 3, 4, 6, 8, 10, 12, 14, 16, 20, 24, 30]


def _sample_group(target, rng):
    """Return (m, k2, r) describing Z_m x|_r Z_k2 with order m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice(K2_CHOICES)
        m = max(2, -(-target // k2))
        r = 1
        if k2 > 1 and m > 2:
            cands = [c for c in range(2, m) if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m]
            if cands:
                r = rng.choice(cands)
        return m, k2, r
    return None


def _groups_of_order(n):
    """All (m, k2, r) with m*k2 == n giving Z_m x|_r Z_k2 (r = 1 is the direct product)."""
    out = []
    for k2 in range(1, n + 1):
        if n % k2:
            continue
        m = n // k2
        if m == 1:
            out.append((1, k2, 1))
        elif k2 == 1:
            out.append((m, 1, 1))
        else:
            for r in range(1, m):
                if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m:
                    out.append((m, k2, r))
    return out


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 5.0))
    deadline = start + budget
    lift_end = start + 0.20 * budget
    bicay_end = start + 0.40 * budget
    repair_end = start + 0.88 * budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
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

    # Phase B: voltage lifts over Z_m (parent baseline).
    while True:
        remaining = lift_end - time.monotonic()
        if remaining < 1.0:
            break
        slice_s = min(remaining, 12.0)
        k = rng.choice([1, 1, 2, 2, 3])
        base = best[0] // (2 * k)
        target = base + 1 + rng.randrange(0, max(2, base // 10 + 1))
        grp = _sample_group(target, rng)
        if grp is None:
            continue
        m, k2, r = grp
        try:
            out = lib.run_c(
                C_SOURCE,
                [d, D, k, m, k2, r, rng.randrange(1, 10 ** 9), f"{slice_s:.2f}"],
                timeout=slice_s + 10.0,
            )
        except RuntimeError:
            break
        try:
            n, e = lib.parse_graph_text(out)
        except ValueError:
            continue
        consider(n, e)

    # Phase A: bi-Cayley search over exact groups of order just above best/2.
    while True:
        remaining = bicay_end - time.monotonic()
        if remaining < 1.5:
            break
        n_lo = best[0] // 2 + 1
        n_grp = n_lo + rng.randrange(0, max(4, n_lo // 25))
        n_grp = max(n_grp, d + 1)
        if n_grp > 2400:
            break
        opts = _groups_of_order(n_grp)
        if not opts:
            continue
        m, k2, r = rng.choice(opts)
        slice_s = min(3.0, remaining)
        try:
            out = lib.run_c(
                BICAY_SOURCE,
                [d, D, m, k2, r, rng.randrange(1, 10 ** 9), f"{slice_s:.2f}"],
                timeout=slice_s + 10.0,
            )
        except RuntimeError:
            break
        try:
            n, e = lib.parse_graph_text(out)
        except ValueError:
            continue
        consider(n, e)

    # Phase C (new): whole-graph repair. Pad the current best with new vertex
    # pairs and anneal edge switches to kill all pairs at distance > D.
    # Occasionally start from scratch with a random bipartite graph.
    if d >= 3 and D >= 2:
        while True:
            remaining = repair_end - time.monotonic()
            if remaining < 2.0:
                break
            slice_s = min(remaining - 1.0, 6.0 + 4.0 * rng.random())
            if slice_s < 0.5:
                break
            if best[0] > 2 * d and rng.random() < 0.9:
                extra = rng.choice(EXTRA_CHOICES)
                stdin_g = best
            else:
                extra = max(d, best[0] // 2 + 2 + rng.randrange(0, 20))
                stdin_g = None
            try:
                out = lib.run_c(
                    REPAIR_SOURCE,
                    [d, D, extra, rng.randrange(1, 10 ** 9), f"{slice_s:.2f}"],
                    stdin_graph=stdin_g,
                    timeout=slice_s + 10.0,
                )
            except RuntimeError:
                break
            try:
                n, e = lib.parse_graph_text(out)
            except ValueError:
                continue
            consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))

    # Spare-degree extension with the remaining time.
    try:
        n2, e2 = _extend_spare(best[0], best[1], d, D, deadline)
        if n2 > best[0] and lib.is_valid(n2, e2, d, D):
            best = (n2, e2)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
