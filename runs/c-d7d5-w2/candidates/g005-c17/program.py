import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Engine A: bi-Cayley lifts over a single group, K = 1 (baseline, short phase).
#
# Usage: prog DEG DIAM m k2 r seed slice_seconds
# Prints a valid graph ("n m" + edges) or "0 0".
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
# Engine B: voltage annealing of general bi-Cayley lifts (baseline).
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
# Engine C (new, bold): unstructured graph search with growth.
#
# The graph is kept as an explicit bipartite multigraph-free adjacency list
# with sides col[v] in {0,1} and max degree DEGB. The cost is the number of
# ordered vertex pairs at distance > DM, computed exactly with bitset BFS
# (DM rounds of OR over neighbours). Moves preserve bipartiteness:
#   add      : join a deficient A vertex to a deficient B vertex
#   switch   : 2-switch (a,b),(c,e) -> (a,e),(c,b) on the same sides
#   endpoint : move one endpoint of an edge to a deficient vertex on that side
# Simulated annealing runs on a fixed vertex count. When it reaches cost 0,
# the graph is saved and grown by two vertices using a degree-preserving
# edge-surgery insertion (remove d-1 disjoint edges, reconnect to a new A/B
# pair), then annealing repairs the result.
#
# Usage: prog DEGB DM CAP seed slice NSTART
#   stdin: "n m" + edges (or "0 0"). Prints best valid graph or "0 0".
# ----------------------------------------------------------------------------

GROW_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXCAP 2600

static int DEGB, DM, CAP, WMAX, N;
static int *nb, *dg, *col;
static unsigned char *adj;
static uint64_t *cur, *nxt;
static int *ledA, *ledB, *pa, *pb;
static uint64_t rs = 88172645463325252ULL;

typedef struct { int N; int *nb, *dg, *col; } State;
static State VAL, STG;

typedef struct { int type, u, v; } Op;
static Op LOG[16];
static int nlog = 0;

static uint64_t rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double clk(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void add_arc(int u, int v) { nb[(size_t)u * DEGB + dg[u]] = v; dg[u]++; }

static void del_arc(int u, int v) {
    int *r = nb + (size_t)u * DEGB;
    int k = dg[u];
    for (int i = 0; i < k; i++) {
        if (r[i] == v) { r[i] = r[k - 1]; dg[u] = k - 1; return; }
    }
}

static void add_edge(int u, int v) {
    add_arc(u, v); add_arc(v, u);
    adj[(size_t)u * CAP + v] = 1;
    adj[(size_t)v * CAP + u] = 1;
}

static void del_edge(int u, int v) {
    del_arc(u, v); del_arc(v, u);
    adj[(size_t)u * CAP + v] = 0;
    adj[(size_t)v * CAP + u] = 0;
}

static void L_add(int u, int v) {
    add_edge(u, v);
    LOG[nlog].type = 0; LOG[nlog].u = u; LOG[nlog].v = v; nlog++;
}

static void L_del(int u, int v) {
    del_edge(u, v);
    LOG[nlog].type = 1; LOG[nlog].u = u; LOG[nlog].v = v; nlog++;
}

static void undo(void) {
    while (nlog > 0) {
        nlog--;
        Op o = LOG[nlog];
        if (o.type == 0) del_edge(o.u, o.v);
        else add_edge(o.u, o.v);
    }
    nlog = 0;
}

/* Collect vertices of a side (side -1 = any). mode 0: deg > 0; mode 1: deg < DEGB. */
static int collect(int side, int mode, int *buf) {
    int k = 0;
    for (int v = 0; v < N; v++) {
        if (side >= 0 && col[v] != side) continue;
        if (mode == 0 && dg[v] == 0) continue;
        if (mode == 1 && dg[v] >= DEGB) continue;
        buf[k++] = v;
    }
    return k;
}

/* Number of ordered pairs at distance > DM. */
static long long cost_fn(void) {
    int W = (N + 63) >> 6;
    for (int v = 0; v < N; v++) {
        uint64_t *r = cur + (size_t)v * WMAX;
        for (int w = 0; w < W; w++) r[w] = 0;
        r[v >> 6] |= 1ULL << (v & 63);
    }
    for (int t = 0; t < DM; t++) {
        for (int v = 0; v < N; v++) {
            uint64_t *o = nxt + (size_t)v * WMAX;
            const uint64_t *s = cur + (size_t)v * WMAX;
            for (int w = 0; w < W; w++) o[w] = s[w];
            const int *row = nb + (size_t)v * DEGB;
            for (int i = 0; i < dg[v]; i++) {
                const uint64_t *su = cur + (size_t)row[i] * WMAX;
                for (int w = 0; w < W; w++) o[w] |= su[w];
            }
        }
        uint64_t *tmp = cur; cur = nxt; nxt = tmp;
    }
    long long bad = 0;
    for (int v = 0; v < N; v++) {
        const uint64_t *r = cur + (size_t)v * WMAX;
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(r[w]);
        bad += N - c;
    }
    return bad;
}

static void st_alloc(State *s) {
    s->nb = malloc(sizeof(int) * (size_t)CAP * DEGB);
    s->dg = malloc(sizeof(int) * (size_t)CAP);
    s->col = malloc(sizeof(int) * (size_t)CAP);
    s->N = 0;
}

static void st_save(State *s) {
    s->N = N;
    memcpy(s->nb, nb, sizeof(int) * (size_t)CAP * DEGB);
    memcpy(s->dg, dg, sizeof(int) * (size_t)CAP);
    memcpy(s->col, col, sizeof(int) * (size_t)CAP);
}

static void rebuild_adj(void) {
    memset(adj, 0, (size_t)CAP * CAP);
    for (int v = 0; v < N; v++)
        for (int i = 0; i < dg[v]; i++)
            adj[(size_t)v * CAP + nb[(size_t)v * DEGB + i]] = 1;
}

static void st_load(State *s) {
    N = s->N;
    memcpy(nb, s->nb, sizeof(int) * (size_t)CAP * DEGB);
    memcpy(dg, s->dg, sizeof(int) * (size_t)CAP);
    memcpy(col, s->col, sizeof(int) * (size_t)CAP);
    rebuild_adj();
}

static int move_add(void) {
    int ka = collect(0, 1, ledA);
    int kb = collect(1, 1, ledB);
    if (ka == 0 || kb == 0) return 0;
    for (int t = 0; t < 20; t++) {
        int x = ledA[rndint(ka)], y = ledB[rndint(kb)];
        if (!adj[(size_t)x * CAP + y]) { L_add(x, y); return 1; }
    }
    return 0;
}

static int move_switch(void) {
    int k = collect(-1, 0, ledA);
    if (k < 2) return 0;
    int a = ledA[rndint(k)];
    int b = nb[(size_t)a * DEGB + rndint(dg[a])];
    int kc = collect(col[a], 0, ledB);
    if (kc < 1) return 0;
    int c = ledB[rndint(kc)];
    if (c == a) return 0;
    int e = nb[(size_t)c * DEGB + rndint(dg[c])];
    if (e == b) return 0;
    if (adj[(size_t)a * CAP + e] || adj[(size_t)c * CAP + b]) return 0;
    L_del(a, b); L_del(c, e);
    L_add(a, e); L_add(c, b);
    return 1;
}

static int move_endpoint(void) {
    int k = collect(-1, 0, ledA);
    if (k < 1) return 0;
    int a = ledA[rndint(k)];
    int b = nb[(size_t)a * DEGB + rndint(dg[a])];
    int s = rndint(2);
    int p, q;
    if (col[a] == s) { p = a; q = b; } else { p = b; q = a; }
    int kx = collect(s, 1, ledB);
    if (kx < 1) return 0;
    int x = ledB[rndint(kx)];
    if (x == p || adj[(size_t)x * CAP + q]) return 0;
    L_del(p, q);
    L_add(x, q);
    return 1;
}

/* Degree-preserving growth by two vertices (one per side). */
static void grow_pair(void) {
    int x = N, y = N + 1;
    N += 2;
    col[x] = 0; col[y] = 1;
    dg[x] = 0; dg[y] = 0;
    int want = DEGB - 1;
    int ka = collect(0, 0, ledA);
    int np = 0, tries = 0;
    while (np < want && tries < 1000 && ka > 0) {
        tries++;
        int a = ledA[rndint(ka)];
        int b = nb[(size_t)a * DEGB + rndint(dg[a])];
        int clash = 0;
        for (int i = 0; i < np; i++) {
            if (pa[i] == a || pb[i] == b) { clash = 1; break; }
        }
        if (!clash) { pa[np] = a; pb[np] = b; np++; }
    }
    for (int i = 0; i < np; i++) del_edge(pa[i], pb[i]);
    for (int i = 0; i < np; i++) {
        add_edge(x, pb[i]);
        add_edge(pa[i], y);
    }
    if (!adj[(size_t)x * CAP + y] && dg[x] < DEGB && dg[y] < DEGB) add_edge(x, y);
}

/* Simulated annealing at fixed N. Returns 1 if cost 0 is reached (state left at cost 0),
   otherwise restores the stage best and returns 0. */
static int anneal(double deadline) {
    long long cc = cost_fn();
    if (cc == 0) return 1;
    st_save(&STG);
    long long sc = cc;
    const int CYCLE = 3000;
    const double T0 = 4.0, T1 = 0.25;
    int ci = 0;
    unsigned long long it = 0;
    while (1) {
        if ((it & 63) == 0 && clk() >= deadline) break;
        it++;
        if (ci >= CYCLE) {
            ci = 0;
            if (cc > sc) { st_load(&STG); cc = sc; }
        }
        double T = T0 * pow(T1 / T0, (double)ci / CYCLE);
        ci++;
        nlog = 0;
        double r = rnd01();
        int ok;
        if (r < 0.25) ok = move_add();
        else if (r < 0.65) ok = move_switch();
        else ok = move_endpoint();
        if (!ok) { nlog = 0; continue; }
        long long nc = cost_fn();
        if (nc <= cc || rnd01() < exp(-(double)(nc - cc) / T)) {
            cc = nc;
            nlog = 0;
            if (cc < sc) {
                sc = cc;
                st_save(&STG);
                if (cc == 0) return 1;
            }
        } else {
            undo();
        }
    }
    st_load(&STG);
    return sc == 0;
}

int main(int argc, char **argv) {
    if (argc < 6) { printf("0 0\n"); return 0; }
    DEGB = atoi(argv[1]);
    DM = atoi(argv[2]);
    CAP = atoi(argv[3]);
    uint64_t seed = strtoull(argv[4], NULL, 10);
    double slice = atof(argv[5]);
    int NSTART = argc > 6 ? atoi(argv[6]) : 0;
    if (DEGB < 2 || DM < 1 || CAP < 4 || CAP > MAXCAP) { printf("0 0\n"); return 0; }

    rs = seed * 0x9E3779B97F4A7C15ULL ^ 0x5DEECE66DULL;
    if (rs == 0) rs = 1;
    WMAX = (CAP + 63) >> 6;

    nb = malloc(sizeof(int) * (size_t)CAP * DEGB);
    dg = calloc((size_t)CAP, sizeof(int));
    col = calloc((size_t)CAP, sizeof(int));
    adj = calloc((size_t)CAP * CAP, 1);
    cur = calloc((size_t)CAP * WMAX, sizeof(uint64_t));
    nxt = calloc((size_t)CAP * WMAX, sizeof(uint64_t));
    ledA = malloc(sizeof(int) * (size_t)CAP);
    ledB = malloc(sizeof(int) * (size_t)CAP);
    pa = malloc(sizeof(int) * (size_t)CAP);
    pb = malloc(sizeof(int) * (size_t)CAP);
    if (!nb || !dg || !col || !adj || !cur || !nxt || !ledA || !ledB || !pa || !pb) {
        printf("0 0\n");
        return 0;
    }
    st_alloc(&VAL);
    st_alloc(&STG);

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) { n = 0; m = 0; }
    int ok = (n >= 0 && n <= CAP && m >= 0);
    int *eu = NULL, *ev = NULL;
    if (ok && m > 0) {
        eu = malloc(sizeof(int) * (size_t)m);
        ev = malloc(sizeof(int) * (size_t)m);
        if (!eu || !ev) { printf("0 0\n"); return 0; }
        for (int i = 0; i < m; i++) {
            if (scanf("%d %d", &eu[i], &ev[i]) != 2) { ok = 0; break; }
        }
    }
    N = n;
    if (ok) {
        for (int i = 0; i < m; i++) {
            int u = eu[i], v = ev[i];
            if (u < 0 || v < 0 || u >= n || v >= n || u == v) { ok = 0; break; }
            if (adj[(size_t)u * CAP + v]) { ok = 0; break; }
            if (dg[u] >= DEGB || dg[v] >= DEGB) { ok = 0; break; }
            add_edge(u, v);
        }
    }
    if (ok) {
        for (int v = 0; v < N; v++) col[v] = -1;
        for (int s = 0; s < N && ok; s++) {
            if (col[s] != -1) continue;
            col[s] = 0;
            int sp = 0;
            ledA[sp++] = s;
            while (sp > 0 && ok) {
                int u = ledA[--sp];
                for (int i = 0; i < dg[u]; i++) {
                    int v = nb[(size_t)u * DEGB + i];
                    if (col[v] == -1) {
                        col[v] = 1 - col[u];
                        ledA[sp++] = v;
                    } else if (col[v] == col[u]) {
                        ok = 0;
                        break;
                    }
                }
            }
        }
    }
    if (!ok) { printf("0 0\n"); return 0; }
    if (N == 0) {
        if (NSTART < 4 || NSTART > CAP) { printf("0 0\n"); return 0; }
        N = NSTART;
        for (int v = 0; v < N; v++) { col[v] = v & 1; dg[v] = 0; }
        rebuild_adj();
    }

    double t_end = clk() + slice;
    int have = 0;
    if (anneal(t_end)) { st_save(&VAL); have = 1; }

    int fails = 0;
    while (have && clk() < t_end && N + 2 <= CAP) {
        st_load(&VAL);
        double rem = t_end - clk();
        double stage = 0.4 * rem;
        if (stage < 1.0) stage = 1.0;
        if (stage > rem) stage = rem;
        grow_pair();
        if (anneal(clk() + stage)) {
            st_save(&VAL);
            fails = 0;
        } else {
            if (++fails >= 2) break;
        }
    }

    if (!have) { printf("0 0\n"); fflush(stdout); return 0; }
    st_load(&VAL);
    long long me = 0;
    for (int v = 0; v < N; v++) me += dg[v];
    me /= 2;
    printf("%d %lld\n", N, me);
    for (int v = 0; v < N; v++)
        for (int i = 0; i < dg[v]; i++) {
            int u = nb[(size_t)v * DEGB + i];
            if (u > v) printf("%d %d\n", v, u);
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
# Group sampling (for the lift engines).
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

    # Phase B: general lift annealing (baseline), short.
    t_B = start + 0.22 * budget
    while True:
        remaining = t_B - time.monotonic()
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

    # Phase A: K = 1 bi-Cayley search over groups of order just above best/2.
    t_A = start + 0.36 * budget
    while True:
        remaining = t_A - time.monotonic()
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

    # Phase C (bold): unstructured annealing with degree-preserving growth,
    # started from the best graph found so far.
    cap_extra = 120
    t_C = start + 0.92 * budget
    if d >= 3 and best[0] + cap_extra <= 2500:
        remaining = t_C - time.monotonic()
        if remaining > 2.0:
            slice_s = remaining - 0.5
            try:
                out = lib.run_c(
                    GROW_SOURCE,
                    [d, D, best[0] + cap_extra, rng.randrange(1, 10 ** 9),
                     f"{slice_s:.2f}", 0],
                    stdin_graph=best,
                    timeout=slice_s + 15.0,
                )
                n2, e2 = lib.parse_graph_text(out)
                consider(n2, e2)
            except (RuntimeError, ValueError):
                pass

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
