import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Engine R (new): bitset repair search with vertex-pair growth.
#
# Input: a valid bipartite graph (stdin, "n m" + edges) and `extra` new
# vertices (even count, alternating sides). The engine keeps the bipartition
# and the max degree, and runs simulated annealing over edge moves:
#   add an edge between two free vertices, move one endpoint of an edge to a
#   free vertex on either side, a degree-preserving 2-switch, or delete an edge.
# Cost = number of ordered vertex pairs at distance > D. All-pairs balls are
# computed with 64-bit bitsets (D rounds of OR over neighbour rows), so one
# evaluation is about D * 2M * W word operations. Undo keeps each move O(1).
# Output: a valid graph on n0 + extra vertices ("n m" + edges), or "0 0".
#
# Usage: prog DEG DIAM extra seed slice_seconds
# ----------------------------------------------------------------------------

REPAIR_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

static int DEG, DIAM, N, W, M, NA, NB;
static int *ea, *eb, *deg, *sideA, *sideB, *freeL, *ncnt, *nbr, *bestA, *bestB, bestM;
static unsigned char *adjM;
static uint64_t *R1, *R2;
static uint64_t rs = 88172645463325252ULL;

typedef struct { int t, x, y, z; } Op;
static Op ops[4];
static int nops = 0;

static inline uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static inline int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static inline double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double elapsed(clock_t t0) { return (double)(clock() - t0) / (double)CLOCKS_PER_SEC; }

static inline size_t AIDX(int a, int b) { return (size_t)a * (size_t)N + (size_t)b; }

static void add_edge(int a, int b) {
    ea[M] = a; eb[M] = b; M++;
    adjM[AIDX(a, b)] = 1; adjM[AIDX(b, a)] = 1;
    deg[a]++; deg[b]++;
}

static void remove_at(int e) {
    int a = ea[e], b = eb[e];
    adjM[AIDX(a, b)] = 0; adjM[AIDX(b, a)] = 0;
    deg[a]--; deg[b]--;
    M--;
    ea[e] = ea[M]; eb[e] = eb[M];
}

static void restore_at(int e, int a, int b) {
    ea[M] = ea[e]; eb[M] = eb[e];
    ea[e] = a; eb[e] = b;
    M++;
    adjM[AIDX(a, b)] = 1; adjM[AIDX(b, a)] = 1;
    deg[a]++; deg[b]++;
}

/* Replace the B endpoint of edge e by nb. */
static void rewire_b(int e, int nb) {
    int a = ea[e], ob = eb[e];
    adjM[AIDX(a, ob)] = 0; adjM[AIDX(ob, a)] = 0;
    adjM[AIDX(a, nb)] = 1; adjM[AIDX(nb, a)] = 1;
    deg[ob]--; deg[nb]++;
    eb[e] = nb;
}

/* Replace the A endpoint of edge e by na. */
static void rewire_a(int e, int na) {
    int oa = ea[e], b = eb[e];
    adjM[AIDX(oa, b)] = 0; adjM[AIDX(b, oa)] = 0;
    adjM[AIDX(na, b)] = 1; adjM[AIDX(b, na)] = 1;
    deg[oa]--; deg[na]++;
    ea[e] = na;
}

static int collect_free(int isA, int *out) {
    int *S = isA ? sideA : sideB;
    int ns = isA ? NA : NB;
    int c = 0;
    for (int i = 0; i < ns; i++) if (deg[S[i]] < DEG) out[c++] = S[i];
    return c;
}

static int try_add(void) {
    int *fa = freeL, *fb = freeL + N;
    int ca = collect_free(1, fa), cb = collect_free(0, fb);
    if (ca == 0 || cb == 0) return 0;
    for (int t = 0; t < 200; t++) {
        int a = fa[rndint(ca)], b = fb[rndint(cb)];
        if (adjM[AIDX(a, b)]) continue;
        add_edge(a, b);
        ops[0].t = 2; nops = 1;
        return 1;
    }
    return 0;
}

static int try_rewire(void) {
    if (M == 0) return 0;
    int side = rndint(2);             /* 0: replace B endpoint, 1: replace A endpoint */
    int cnt = collect_free(side == 1, freeL);
    if (cnt == 0) return 0;
    for (int t = 0; t < 60; t++) {
        int e = rndint(M);
        int v = freeL[rndint(cnt)];
        if (side == 0) {
            int a = ea[e];
            if (v == eb[e] || adjM[AIDX(a, v)]) continue;
            int ob = eb[e];
            rewire_b(e, v);
            ops[0].t = 1; ops[0].x = e; ops[0].y = ob; nops = 1;
            return 1;
        } else {
            int b = eb[e];
            if (v == ea[e] || adjM[AIDX(v, b)]) continue;
            int oa = ea[e];
            rewire_a(e, v);
            ops[0].t = 4; ops[0].x = e; ops[0].y = oa; nops = 1;
            return 1;
        }
    }
    return 0;
}

static int try_switch(void) {
    if (M < 2) return 0;
    for (int t = 0; t < 60; t++) {
        int e1 = rndint(M), e2 = rndint(M);
        if (e1 == e2) continue;
        int a1 = ea[e1], b1 = eb[e1], a2 = ea[e2], b2 = eb[e2];
        if (a1 == a2 || b1 == b2) continue;
        if (adjM[AIDX(a1, b2)] || adjM[AIDX(a2, b1)]) continue;
        rewire_b(e1, b2);
        rewire_b(e2, b1);
        ops[0].t = 1; ops[0].x = e1; ops[0].y = b1;
        ops[1].t = 1; ops[1].x = e2; ops[1].y = b2;
        nops = 2;
        return 1;
    }
    return 0;
}

static int try_remove(void) {
    if (M == 0) return 0;
    int e = rndint(M);
    int a = ea[e], b = eb[e];
    remove_at(e);
    ops[0].t = 3; ops[0].x = e; ops[0].y = a; ops[0].z = b; nops = 1;
    return 1;
}

static void undo_ops(void) {
    for (int i = nops - 1; i >= 0; i--) {
        Op o = ops[i];
        if (o.t == 1) rewire_b(o.x, o.y);
        else if (o.t == 4) rewire_a(o.x, o.y);
        else if (o.t == 2) remove_at(M - 1);
        else if (o.t == 3) restore_at(o.x, o.y, o.z);
    }
    nops = 0;
}

static void save_best(void) {
    bestM = M;
    memcpy(bestA, ea, sizeof(int) * (size_t)M);
    memcpy(bestB, eb, sizeof(int) * (size_t)M);
}

static void restore_best(void) {
    memset(adjM, 0, (size_t)N * (size_t)N);
    memset(deg, 0, sizeof(int) * (size_t)N);
    M = 0;
    for (int e = 0; e < bestM; e++) add_edge(bestA[e], bestB[e]);
}

/* Number of ordered pairs (u, v) with dist(u, v) > DIAM. */
static int eval_cost(void) {
    memset(ncnt, 0, sizeof(int) * (size_t)N);
    for (int e = 0; e < M; e++) {
        int a = ea[e], b = eb[e];
        nbr[(size_t)a * DEG + ncnt[a]++] = b;
        nbr[(size_t)b * DEG + ncnt[b]++] = a;
    }
    memset(R1, 0, sizeof(uint64_t) * (size_t)N * (size_t)W);
    for (int v = 0; v < N; v++) R1[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    uint64_t *cur = R1, *nxt = R2;
    for (int r = 0; r < DIAM; r++) {
        for (int v = 0; v < N; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            const uint64_t *src = cur + (size_t)v * W;
            memcpy(dst, src, sizeof(uint64_t) * (size_t)W);
            for (int k = 0; k < ncnt[v]; k++) {
                const uint64_t *s2 = cur + (size_t)nbr[(size_t)v * DEG + k] * W;
                for (int w = 0; w < W; w++) dst[w] |= s2[w];
            }
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
    }
    int cost = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        const uint64_t *src = cur + (size_t)v * W;
        for (int w = 0; w < W; w++) c += __builtin_popcountll(src[w]);
        cost += N - c;
    }
    return cost;
}

int main(int argc, char **argv) {
    if (argc < 6) { printf("0 0\n"); return 0; }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    int extra = atoi(argv[3]);
    uint64_t seed = strtoull(argv[4], NULL, 10);
    double slice = atof(argv[5]);
    rs = seed * 0x9E3779B97F4A7C15ULL ^ 0x7777ULL;
    if (rs == 0) rs = 1;

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 < 1 || m0 < 0 || DEG < 1 || DIAM < 1
        || extra < 0 || extra > 200) {
        printf("0 0\n");
        return 0;
    }
    N = n0 + extra;
    W = (N + 63) / 64;
    int *bu = malloc(sizeof(int) * (size_t)(m0 + 1));
    int *bv = malloc(sizeof(int) * (size_t)(m0 + 1));
    if (!bu || !bv) { printf("0 0\n"); return 0; }
    for (int i = 0; i < m0; i++) {
        if (scanf("%d %d", &bu[i], &bv[i]) != 2) { printf("0 0\n"); return 0; }
        if (bu[i] < 0 || bu[i] >= n0 || bv[i] < 0 || bv[i] >= n0 || bu[i] == bv[i]) {
            printf("0 0\n");
            return 0;
        }
    }

    /* Bipartition of the base graph (propagation), new vertices alternate sides. */
    int *col = malloc(sizeof(int) * (size_t)N);
    for (int v = 0; v < N; v++) col[v] = -1;
    for (int v = 0; v < n0; v++) {
        if (col[v] >= 0) continue;
        col[v] = 0;
        int changed = 1;
        while (changed) {
            changed = 0;
            for (int e = 0; e < m0; e++) {
                int u = bu[e], w = bv[e];
                if (col[u] >= 0 && col[w] < 0) { col[w] = 1 - col[u]; changed = 1; }
                else if (col[w] >= 0 && col[u] < 0) { col[u] = 1 - col[w]; changed = 1; }
            }
        }
    }
    for (int e = 0; e < m0; e++) if (col[bu[e]] == col[bv[e]]) { printf("0 0\n"); return 0; }
    for (int j = 0; j < extra; j++) col[n0 + j] = j & 1;

    ea = malloc(sizeof(int) * ((size_t)N * DEG + 4));
    eb = malloc(sizeof(int) * ((size_t)N * DEG + 4));
    bestA = malloc(sizeof(int) * ((size_t)N * DEG + 4));
    bestB = malloc(sizeof(int) * ((size_t)N * DEG + 4));
    deg = calloc((size_t)N, sizeof(int));
    sideA = malloc(sizeof(int) * (size_t)N);
    sideB = malloc(sizeof(int) * (size_t)N);
    freeL = malloc(sizeof(int) * (size_t)(2 * N));
    ncnt = malloc(sizeof(int) * (size_t)N);
    nbr = malloc(sizeof(int) * ((size_t)N * DEG + 1));
    adjM = calloc((size_t)N * (size_t)N, 1);
    R1 = malloc(sizeof(uint64_t) * (size_t)N * (size_t)W);
    R2 = malloc(sizeof(uint64_t) * (size_t)N * (size_t)W);
    if (!ea || !eb || !bestA || !bestB || !deg || !sideA || !sideB || !freeL
        || !ncnt || !nbr || !adjM || !R1 || !R2) {
        printf("0 0\n");
        return 0;
    }

    NA = NB = 0;
    for (int v = 0; v < N; v++) {
        if (col[v] == 0) sideA[NA++] = v;
        else sideB[NB++] = v;
    }
    if (NA == 0 || NB == 0) { printf("0 0\n"); return 0; }

    M = 0;
    for (int e = 0; e < m0; e++) {
        int u = bu[e], w = bv[e];
        int a = (col[u] == 0) ? u : w;
        int b = (col[u] == 0) ? w : u;
        if (adjM[AIDX(a, b)]) continue;
        if (deg[a] >= DEG || deg[b] >= DEG) { printf("0 0\n"); return 0; }
        add_edge(a, b);
    }

    save_best();
    int cur = eval_cost();
    int bestCost = cur;
    int found = (cur == 0);

    clock_t t0 = clock();
    const int RL = 20000;
    const double T0 = 8.0, T1 = 0.2;
    int phase = 0;
    while (!found) {
        if ((phase & 63) == 0 && elapsed(t0) >= slice) break;
        double T = T0 * pow(T1 / T0, (double)phase / RL);
        double p = rnd01();
        int ok;
        nops = 0;
        if (p < 0.35) ok = try_add();
        else if (p < 0.65) ok = try_rewire();
        else if (p < 0.95) ok = try_switch();
        else ok = try_remove();
        if (ok) {
            int nc = eval_cost();
            if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
                cur = nc;
                if (cur < bestCost) { bestCost = cur; save_best(); }
                if (cur == 0) found = 1;
            } else {
                undo_ops();
            }
        }
        nops = 0;
        if (++phase >= RL) {
            phase = 0;
            restore_best();
            for (int k = 0; k < 3; k++) try_switch();
            nops = 0;
            cur = eval_cost();
        }
    }

    if (found) {
        printf("%d %d\n", N, M);
        for (int e = 0; e < M; e++) printf("%d %d\n", ea[e], eb[e]);
    } else {
        printf("0 0\n");
    }
    fflush(stdout);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Engine A: bi-Cayley lifts over a single group, K = 1 (from the parent).
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
# Engine B: voltage annealing of general bi-Cayley lifts with K base vertices
# per side (from the parent).
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
# Exact / safe constructions (from the parent).
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
# Group sampling (from the parent).
# ----------------------------------------------------------------------------

K2_CHOICES = [1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 21, 24,
              27, 28, 30, 36, 40, 42, 49, 54, 56, 63, 72, 81, 84, 96, 108, 121,
              128, 162, 243]


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
# Pipeline: exact constructions -> short voltage / bi-Cayley searches ->
# repair-and-grow loop (engine R adds 2 vertices at a time to the current best)
# -> spare-degree extension.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 5.0))
    deadline = start + budget
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

    # Phase B: general lift annealing (voltage search), until 25% of the budget.
    phaseB_end = start + 0.25 * budget
    while True:
        remaining = phaseB_end - time.monotonic()
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

    # Phase A: K = 1 bi-Cayley search, until 45% of the budget.
    phaseA_end = start + 0.45 * budget
    while True:
        remaining = phaseA_end - time.monotonic()
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

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))

    # Repair-and-grow: each step adds 2 vertices to the current best and lets the
    # bitset annealer (engine R) repair the graph. Stops after 3 failed steps in a row.
    repair_end = start + 0.92 * budget
    fails = 0
    while fails < 3:
        remaining = repair_end - time.monotonic()
        if remaining < 2.0:
            break
        slice_s = min(remaining - 1.0, 10.0)
        try:
            out = lib.run_c(
                REPAIR_SOURCE,
                [d, D, 2, rng.randrange(1, 10 ** 9), f"{slice_s:.2f}"],
                stdin_graph=best,
                timeout=slice_s + 10.0,
            )
        except RuntimeError:
            break
        try:
            n, e = lib.parse_graph_text(out)
        except ValueError:
            fails += 1
            continue
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
            fails = 0
        else:
            fails += 1

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
