import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine 1: simulated annealing over the voltages of a bi-Cayley lift
# over the group Z_m x|_r Z_k2 (element (a, b) coded as a*k2 + b).
#
# Usage: prog d D K m k2 r seed slice_seconds
# Prints a valid graph ("n m" + edges) or "0 0".
# ----------------------------------------------------------------------------

C_LIFT = r"""
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

    const int LMAX = DIAM + 3;
    const int UNREACH_W = LMAX - DIAM + 2;
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
        for (int lv = 0; lv < LMAX && fn > 0; lv++) {
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
            if (lv + 1 > DIAM) total += (lv + 1 - DIAM) * nn;
            int *tmp = cur; cur = nxt; nxt = tmp;
            fn = nn;
        }
        total += (N - reached) * UNREACH_W;
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
# C engine 2: direct bipartite annealing with grow-and-repair.
#
# State: a bipartite graph (A-vertices, B-vertices) with max degree DEG.
# Moves: degree-preserving edge switches (a1-b1, a2-b2) -> (a1-b2, a2-b1).
# Cost: number of ordered vertex pairs at distance > DIAM, from bitset BFS.
# When the cost is zero and the graph is DEG-regular, grow by two vertices:
# remove DEG-1 edges of a matching, attach x to their B ends, y to their A
# ends, and join x-y. The graph stays DEG-regular, then annealing repairs it.
# If repair fails, revert to the last valid anchor and grow differently.
#
# Usage: prog d D nmax slice_seconds seed  (graph text on stdin)
# Prints the largest valid graph found ("n m" + edges), or "0 0".
# ----------------------------------------------------------------------------

C_SA = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

static int DEG, DIAM, NMAX, NEMAX, W, NCUR, NE;
static int *ea, *eb, *ancEa, *ancEb;
static int *nbl, *dg, *usedA, *usedB;
static int ustamp = 0;
static unsigned char *adjm;
static uint64_t *RA, *RB;
static int ancN, ancNE;
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

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void list_replace(int v, int oldu, int newu) {
    int *L = nbl + (size_t)v * DEG;
    for (int j = 0; j < dg[v]; j++) {
        if (L[j] == oldu) { L[j] = newu; return; }
    }
}

static void list_add(int v, int u) {
    nbl[(size_t)v * DEG + dg[v]] = u;
    dg[v]++;
}

/* Edges e1=(a1,b1), e2=(a2,b2) become (a1,b2), (a2,b1). Caller checks validity.
   Calling it again on the same pair undoes the move. */
static void do_switch(int e1, int e2) {
    int a1 = ea[e1], b1 = eb[e1], a2 = ea[e2], b2 = eb[e2];
    adjm[(size_t)a1 * NMAX + b1] = 0;
    adjm[(size_t)a2 * NMAX + b2] = 0;
    adjm[(size_t)a1 * NMAX + b2] = 1;
    adjm[(size_t)a2 * NMAX + b1] = 1;
    list_replace(a1, b1, b2);
    list_replace(b1, a1, a2);
    list_replace(a2, b2, b1);
    list_replace(b2, a2, a1);
    eb[e1] = b2;
    eb[e2] = b1;
}

static void rebuild(void) {
    memset(adjm, 0, (size_t)NMAX * NMAX);
    memset(dg, 0, sizeof(int) * NMAX);
    for (int e = 0; e < NE; e++) {
        int a = ea[e], b = eb[e];
        adjm[(size_t)a * NMAX + b] = 1;
        list_add(a, b);
        list_add(b, a);
    }
}

/* Sum over vertices of the number of vertices not within DIAM steps. */
static long long evaluate(void) {
    int n = NCUR, Wc = (n + 63) >> 6;
    uint64_t *cur = RA, *nxt = RB;
    for (int v = 0; v < n; v++) {
        uint64_t *row = cur + (size_t)v * W;
        memset(row, 0, sizeof(uint64_t) * (size_t)Wc);
        row[v >> 6] |= 1ULL << (v & 63);
    }
    for (int t = 0; t < DIAM; t++) {
        for (int v = 0; v < n; v++) {
            uint64_t *out = nxt + (size_t)v * W;
            const uint64_t *in = cur + (size_t)v * W;
            memcpy(out, in, sizeof(uint64_t) * (size_t)Wc);
            const int *L = nbl + (size_t)v * DEG;
            for (int j = 0; j < dg[v]; j++) {
                const uint64_t *src = cur + (size_t)L[j] * W;
                for (int w = 0; w < Wc; w++) out[w] |= src[w];
            }
        }
        uint64_t *tmp = cur; cur = nxt; nxt = tmp;
    }
    long long cost = 0;
    for (int v = 0; v < n; v++) {
        const uint64_t *row = cur + (size_t)v * W;
        int pc = 0;
        for (int w = 0; w < Wc; w++) pc += popc(row[w]);
        cost += n - pc;
    }
    return cost;
}

static int is_regular(void) {
    for (int v = 0; v < NCUR; v++) if (dg[v] != DEG) return 0;
    return 1;
}

/* Grow by two vertices, keeping the graph DEG-regular. Returns 1 on success. */
static int grow(void) {
    int k = DEG - 1;
    if (k < 1 || k > 255 || NCUR + 2 > NMAX || NE + DEG > NEMAX || !is_regular()) return 0;
    ustamp++;
    int chosen[256];
    int cnt = 0;
    for (long tries = 0; tries < 200000 && cnt < k; tries++) {
        int e = rndint(NE);
        int a = ea[e], b = eb[e];
        if (usedA[a] == ustamp || usedB[b] == ustamp) continue;
        usedA[a] = ustamp;
        usedB[b] = ustamp;
        chosen[cnt++] = e;
    }
    if (cnt < k) return 0;
    int x = NCUR, y = NCUR + 1;
    NCUR += 2;
    dg[x] = 0;
    dg[y] = 0;
    for (int i = 0; i < k; i++) {
        int e = chosen[i];
        int a = ea[e], b = eb[e];
        /* (a,b) becomes (a,y); new edge (x,b) */
        adjm[(size_t)a * NMAX + b] = 0;
        adjm[(size_t)a * NMAX + y] = 1;
        adjm[(size_t)x * NMAX + b] = 1;
        list_replace(a, b, y);
        list_replace(b, a, x);
        list_add(x, b);
        list_add(y, a);
        eb[e] = y;
        ea[NE] = x; eb[NE] = b; NE++;
    }
    list_add(x, y);
    list_add(y, x);
    adjm[(size_t)x * NMAX + y] = 1;
    ea[NE] = x; eb[NE] = y; NE++;
    return 1;
}

static void save_anchor(void) {
    ancN = NCUR;
    ancNE = NE;
    memcpy(ancEa, ea, sizeof(int) * (size_t)NE);
    memcpy(ancEb, eb, sizeof(int) * (size_t)NE);
}

static void restore_anchor(void) {
    NCUR = ancN;
    NE = ancNE;
    memcpy(ea, ancEa, sizeof(int) * (size_t)NE);
    memcpy(eb, ancEb, sizeof(int) * (size_t)NE);
    rebuild();
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D nmax slice [seed]\n");
        return 1;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    NMAX = atoi(argv[3]);
    double slice = atof(argv[4]);
    uint64_t seed = argc > 5 ? strtoull(argv[5], NULL, 10) : 1ULL;
    rs = seed * 0x9E3779B97F4A7C15ULL ^ 0x5DEECE66DULL;
    if (rs == 0) rs = 1;

    if (DEG < 2 || DIAM < 1 || NMAX < 4 || NMAX > 4000) { printf("0 0\n"); return 0; }
    W = (NMAX + 63) >> 6;

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { printf("0 0\n"); return 0; }
    if (n0 < 2 || n0 > NMAX || m0 < 2 || m0 > DEG * NMAX) { printf("0 0\n"); return 0; }

    NEMAX = DEG * NMAX + DEG + 4;
    int *ru = malloc(sizeof(int) * (size_t)m0);
    int *rv = malloc(sizeof(int) * (size_t)m0);
    int *rd = calloc((size_t)n0, sizeof(int));
    if (!ru || !rv || !rd) { printf("0 0\n"); return 0; }
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= n0 || v >= n0 || u == v) {
            printf("0 0\n");
            return 0;
        }
        ru[i] = u; rv[i] = v;
        rd[u]++; rd[v]++;
    }
    for (int v = 0; v < n0; v++) if (rd[v] > DEG) { printf("0 0\n"); return 0; }

    /* 2-colouring to orient every edge from side A (colour 0) to side B. */
    int *off = calloc((size_t)n0 + 1, sizeof(int));
    int *fillp = malloc(sizeof(int) * (size_t)(n0 + 1));
    int *csr = malloc(sizeof(int) * (size_t)(2 * m0));
    int *col = malloc(sizeof(int) * (size_t)n0);
    int *qu = malloc(sizeof(int) * (size_t)n0);
    if (!off || !fillp || !csr || !col || !qu) { printf("0 0\n"); return 0; }
    for (int v = 0; v < n0; v++) off[v + 1] = off[v] + rd[v];
    for (int v = 0; v < n0; v++) fillp[v] = off[v];
    for (int i = 0; i < m0; i++) {
        csr[fillp[ru[i]]++] = rv[i];
        csr[fillp[rv[i]]++] = ru[i];
    }
    for (int v = 0; v < n0; v++) col[v] = -1;
    for (int s = 0; s < n0; s++) {
        if (col[s] != -1) continue;
        col[s] = 0;
        int qh = 0, qt = 0;
        qu[qt++] = s;
        while (qh < qt) {
            int u = qu[qh++];
            for (int j = off[u]; j < off[u + 1]; j++) {
                int v = csr[j];
                if (col[v] < 0) { col[v] = 1 - col[u]; qu[qt++] = v; }
                else if (col[v] == col[u]) { printf("0 0\n"); return 0; }
            }
        }
    }

    ea = malloc(sizeof(int) * (size_t)NEMAX);
    eb = malloc(sizeof(int) * (size_t)NEMAX);
    ancEa = malloc(sizeof(int) * (size_t)NEMAX);
    ancEb = malloc(sizeof(int) * (size_t)NEMAX);
    nbl = malloc(sizeof(int) * (size_t)NMAX * DEG);
    dg = calloc((size_t)NMAX, sizeof(int));
    usedA = calloc((size_t)NMAX, sizeof(int));
    usedB = calloc((size_t)NMAX, sizeof(int));
    adjm = calloc((size_t)NMAX * NMAX, 1);
    RA = malloc(sizeof(uint64_t) * (size_t)NMAX * W);
    RB = malloc(sizeof(uint64_t) * (size_t)NMAX * W);
    if (!ea || !eb || !ancEa || !ancEb || !nbl || !dg || !usedA || !usedB || !adjm || !RA || !RB) {
        printf("0 0\n");
        return 0;
    }

    NE = 0;
    for (int i = 0; i < m0; i++) {
        int u = ru[i], v = rv[i];
        if (col[u] == col[v]) { printf("0 0\n"); return 0; }
        int a = (col[u] == 0) ? u : v;
        int b = (col[u] == 0) ? v : u;
        if (adjm[(size_t)a * NMAX + b]) { printf("0 0\n"); return 0; }
        adjm[(size_t)a * NMAX + b] = 1;
        ea[NE] = a; eb[NE] = b; NE++;
    }
    NCUR = n0;
    rebuild();
    if (NE < 2) { printf("0 0\n"); return 0; }

    long long cur = evaluate();
    save_anchor();
    int anchorValid = (cur == 0);

    clock_t t0 = clock();
    const int ITER = 6000;
    while (elapsed(t0) < slice) {
        if (cur == 0) {
            save_anchor();
            anchorValid = 1;
            if (!grow()) break;
            cur = evaluate();
            continue;
        }
        const double T0 = 10.0, T1 = 0.2;
        for (int it = 0; it < ITER && cur != 0; it++) {
            if ((it & 31) == 0 && elapsed(t0) >= slice) break;
            int e1 = rndint(NE), e2 = rndint(NE);
            if (e1 == e2) continue;
            int a1 = ea[e1], b1 = eb[e1], a2 = ea[e2], b2 = eb[e2];
            if (a1 == a2 || b1 == b2) continue;
            if (adjm[(size_t)a1 * NMAX + b2] || adjm[(size_t)a2 * NMAX + b1]) continue;
            do_switch(e1, e2);
            long long nc = evaluate();
            double T = T0 * pow(T1 / T0, (double)it / ITER);
            if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
                cur = nc;
            } else {
                do_switch(e1, e2);
            }
        }
        if (cur != 0 && elapsed(t0) < slice) {
            restore_anchor();
            cur = evaluate();
        }
    }

    if (anchorValid) {
        printf("%d %d\n", ancN, ancNE);
        for (int e = 0; e < ancNE; e++) printf("%d %d\n", ancEa[e], ancEb[e]);
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


def _adopt(best, n, e, d, D):
    """Return (n, e) if it is larger than best and valid, else best."""
    if n > best[0] and lib.is_valid(n, e, d, D):
        return (n, e)
    return best


# ----------------------------------------------------------------------------
# Greedy spare-degree extension (used only after the search).
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
# Group sampling and the lift phase.
# ----------------------------------------------------------------------------

K2_CHOICES = [1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 21, 24,
              27, 28, 30, 36, 40, 42, 49, 54, 56, 63, 72, 81, 84, 96, 108, 121,
              128, 162, 243]


def _sample_group(target, rng):
    """Return (m, k2, r) describing Z_m x|_r Z_k2 with order m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice(K2_CHOICES)
        m0 = max(2, -(-target // k2))
        for m in range(m0, m0 + 40):
            if k2 == 1:
                return m, 1, 1
            nontrivial = [c for c in range(2, m)
                          if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m]
            if nontrivial:
                return m, k2, rng.choice(nontrivial)
            if pow(1, k2, m) == 1 % m and math.gcd(1, m) == 1:
                return m, k2, 1
    return None


def _lift_phase(d, D, rng, best, lift_end):
    """Search voltage lifts until lift_end. Returns the best valid (n, edges) found."""
    step = 0.08
    retry = None
    while True:
        remaining = lift_end - time.monotonic()
        if remaining < 1.0:
            break
        slice_s = min(remaining, 10.0)
        if retry is not None:
            k, m, k2, r = retry
            retry = None
            is_retry = True
        else:
            is_retry = False
            k = rng.choice([1, 1, 2, 2, 3])
            want = best[0] * (1.0 + step)
            target = max(2, math.ceil(want / (2 * k)))
            grp = _sample_group(target, rng)
            if grp is None:
                continue
            m, k2, r = grp
        try:
            out = lib.run_c(
                C_LIFT,
                [d, D, k, m, k2, r, rng.randrange(1, 10 ** 9), f"{slice_s:.2f}"],
                timeout=slice_s + 10.0,
            )
        except RuntimeError:
            break
        ok = False
        try:
            n, e = lib.parse_graph_text(out)
            new_best = _adopt(best, n, e, d, D)
            if new_best is not best:
                best = new_best
                ok = True
        except ValueError:
            ok = False
        if ok:
            step = min(0.4, step * 1.25)
        elif not is_retry:
            retry = (k, m, k2, r)
        else:
            step = max(0.005, step * 0.7)
    return best


def _grow_sa(d, D, graph, nmax, slice_s, seed):
    """Run the grow-and-repair annealer from a regular bipartite graph. Returns (n, edges)."""
    n, edges = graph
    out = lib.run_c(
        C_SA,
        [d, D, nmax, f"{slice_s:.2f}", seed],
        stdin_graph=(n, edges),
        timeout=slice_s + 10.0,
    )
    return lib.parse_graph_text(out)


def build(d, D, seed, time_limit):
    t_start = time.monotonic()
    budget = max(1.0, min(0.9 * time_limit, time_limit - 4.0))
    deadline = t_start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    # Exact constructions.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            best = _adopt(best, pg[0], pg[1], d, D)
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            best = _adopt(best, gq[0], gq[1], d, D)
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Phase 1: voltage-lift search (about 35% of the budget when the grow phase runs).
    grow_enabled = d >= 3 and D >= 3
    frac_lift = 0.35 if grow_enabled else 0.92
    best = _lift_phase(d, D, rng, best, t_start + frac_lift * budget)

    # Phase 2: grow-and-repair annealing starting from the best regular graph.
    if grow_enabled:
        sa_end = t_start + 0.88 * budget
        slice_s = sa_end - time.monotonic() - 3.0
        if slice_s >= 3.0 and best[0] >= 2 * d:
            nmax = min(2400, int(best[0] * 1.25) + 8)
            try:
                n2, e2 = _grow_sa(d, D, best, nmax, slice_s, rng.randrange(1, 10 ** 9))
                best = _adopt(best, n2, e2, d, D)
            except (RuntimeError, ValueError):
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))

    # Spare-degree extension with the remaining time.
    try:
        n3, e3 = _extend_spare(best[0], best[1], d, D, deadline)
        if n3 > best[0] and lib.is_valid(n3, e3, d, D):
            best = (n3, e3)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
