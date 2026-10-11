import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Engine 1 (C_LIFT): annealing over voltages of a bi-Cayley lift over
# Z_m x|_r Z_k2 (element (a, b) coded as a*k2 + b). Kept from the parent
# program; it produces the structured starting graph.
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
# Engine 2 (C_GROW): a different construction. Grow-and-repair.
#
# State: a d-regular bipartite graph with S vertices per side, stored as an
# edge list (EA[e] in A, EB[e] in B) with adjacency lists on both sides.
# Moves:
#   * exchange: two edges (a1,b1),(a2,b2) become (a1,b2),(a2,b1). Degrees
#     are preserved. This move is an involution, so undo = same call.
#   * grow: pick d edges (a_i,b_i) with distinct endpoints and split each one
#     into (a_i,b*) and (a*,b_i) for a new pair (a*,b*). Degrees stay d.
# Cost = number of unordered vertex pairs at distance > D (bitset BFS).
# Cost 0 means the graph is valid (regular, bipartite, diameter <= D).
#
# Loop: start from the input graph (or a random Haar graph if the input is
# not d-regular and bipartite with equal sides). Repeatedly grow by one pair
# and anneal until cost 0. The last valid graph is always kept and printed.
#
# Usage: prog d D S0 seed slice_seconds   (stdin: graph in "n m" format)
# ----------------------------------------------------------------------------

C_GROW = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define ITER_REPAIR 20000
#define ITER_STEP 2000
#define MAXF 3

static int D_, DEG, S, SMAX, NE, WMAX, W;
static int bestS = 0, bestNE = 0;
static int *EA, *EB, *adjA, *adjB, *posB, *nbr, *cntA, *cntB;
static int *markA, *markB, *mk, *bestEA, *bestEB;
static int stampc = 0;
static uint64_t *bufA, *bufB;
static uint64_t rs = 88172645463325252ULL;
static clock_t t0;
static double slice_s;

static inline uint64_t rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static inline double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double elapsed(void) { return (double)(clock() - t0) / (double)CLOCKS_PER_SEC; }

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void rebuild(void) {
    memset(cntA, 0, sizeof(int) * (size_t)S);
    memset(cntB, 0, sizeof(int) * (size_t)S);
    for (int e = 0; e < NE; e++) {
        int a = EA[e], b = EB[e];
        adjA[a * DEG + cntA[a]++] = e;
        posB[e] = cntB[b];
        adjB[b * DEG + cntB[b]++] = e;
    }
}

/* Number of pairs at distance > D_ (unordered), 0 iff valid. */
static int cost_fn(void) {
    int N = 2 * S;
    for (int a = 0; a < S; a++)
        for (int k = 0; k < DEG; k++)
            nbr[a * DEG + k] = S + EB[adjA[a * DEG + k]];
    for (int b = 0; b < S; b++)
        for (int k = 0; k < DEG; k++)
            nbr[(S + b) * DEG + k] = EA[adjB[b * DEG + k]];

    W = (N + 63) >> 6;
    uint64_t *cur = bufA, *nxt = bufB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)N * W);
    for (int v = 0; v < N; v++) cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int st = 0; st < D_; st++) {
        for (int v = 0; v < N; v++) {
            uint64_t *o = nxt + (size_t)v * W;
            const uint64_t *c = cur + (size_t)v * W;
            for (int w = 0; w < W; w++) o[w] = c[w];
            for (int k = 0; k < DEG; k++) {
                const uint64_t *c2 = cur + (size_t)nbr[v * DEG + k] * W;
                for (int w = 0; w < W; w++) o[w] |= c2[w];
            }
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
    }
    long bad = 0;
    for (int v = 0; v < N; v++) {
        int pc = 0;
        const uint64_t *c = cur + (size_t)v * W;
        for (int w = 0; w < W; w++) pc += pc64(c[w]);
        bad += N - pc;
    }
    return (int)(bad / 2);
}

/* Exchange the B-endpoints of e1 and e2. This is an involution. */
static void exchange(int e1, int e2) {
    int b1 = EB[e1], b2 = EB[e2];
    int p1 = posB[e1], p2 = posB[e2];
    adjB[b1 * DEG + p1] = e2;
    adjB[b2 * DEG + p2] = e1;
    posB[e1] = p2;
    posB[e2] = p1;
    EB[e1] = b2;
    EB[e2] = b1;
}

static int valid_exchange(int e1, int e2) {
    int a1 = EA[e1], a2 = EA[e2], b1 = EB[e1], b2 = EB[e2];
    if (a1 == a2 || b1 == b2) return 0;
    for (int k = 0; k < DEG; k++) {
        if (EB[adjA[a1 * DEG + k]] == b2) return 0;
        if (EB[adjA[a2 * DEG + k]] == b1) return 0;
    }
    return 1;
}

static void haar_init(void) {
    int *pool = malloc(sizeof(int) * (size_t)S);
    int *sh = malloc(sizeof(int) * (size_t)DEG);
    for (int i = 0; i < S; i++) pool[i] = i;
    for (int j = 0; j < DEG; j++) {
        int r = j + rndint(S - j);
        int t = pool[j]; pool[j] = pool[r]; pool[r] = t;
        sh[j] = pool[j];
    }
    NE = S * DEG;
    for (int i = 0; i < S; i++)
        for (int j = 0; j < DEG; j++) {
            int e = i * DEG + j;
            EA[e] = i;
            EB[e] = (i + sh[j]) % S;
        }
    rebuild();
    free(pool);
    free(sh);
}

static int load_graph(void) {
    int n, m;
    if (scanf("%d %d", &n, &m) != 2) return 0;
    if (n <= 0 || m <= 0 || (n & 1)) return 0;
    if (n / 2 > SMAX || m != (n / 2) * DEG) return 0;
    int *eu = malloc(sizeof(int) * (size_t)m);
    int *ev = malloc(sizeof(int) * (size_t)m);
    int *deg = calloc((size_t)n, sizeof(int));
    int *st = malloc(sizeof(int) * (size_t)(n + 1));
    int *pos = malloc(sizeof(int) * (size_t)n);
    int *nb = malloc(sizeof(int) * (size_t)(2 * m));
    int *col = malloc(sizeof(int) * (size_t)n);
    int *stk = malloc(sizeof(int) * (size_t)n);
    int *idx = malloc(sizeof(int) * (size_t)n);
    int ok = 1;
    for (int i = 0; i < m && ok; i++) {
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) ok = 0;
        else if (eu[i] < 0 || eu[i] >= n || ev[i] < 0 || ev[i] >= n || eu[i] == ev[i]) ok = 0;
        else { deg[eu[i]]++; deg[ev[i]]++; }
    }
    for (int v = 0; v < n && ok; v++) if (deg[v] != DEG) ok = 0;
    if (ok) {
        st[0] = 0;
        for (int v = 0; v < n; v++) st[v + 1] = st[v] + deg[v];
        for (int v = 0; v < n; v++) pos[v] = st[v];
        for (int i = 0; i < m; i++) {
            nb[pos[eu[i]]++] = ev[i];
            nb[pos[ev[i]]++] = eu[i];
        }
        for (int v = 0; v < n; v++) col[v] = -1;
        for (int s = 0; s < n && ok; s++) {
            if (col[s] != -1) continue;
            col[s] = 0;
            int sp = 0;
            stk[sp++] = s;
            while (sp > 0 && ok) {
                int u = stk[--sp];
                for (int j = st[u]; j < st[u + 1]; j++) {
                    int w = nb[j];
                    if (col[w] == -1) { col[w] = 1 - col[u]; stk[sp++] = w; }
                    else if (col[w] == col[u]) { ok = 0; break; }
                }
            }
        }
    }
    if (ok) {
        int c0 = 0, c0i = 0, c1i = 0;
        for (int v = 0; v < n; v++) if (col[v] == 0) c0++;
        if (c0 != n / 2) ok = 0;
        for (int v = 0; v < n; v++) idx[v] = (col[v] == 0) ? c0i++ : c1i++;
        if (ok) {
            S = n / 2;
            NE = m;
            for (int i = 0; i < m; i++) {
                int u = eu[i], v = ev[i];
                if (col[u] == 1) { int t = u; u = v; v = t; }
                EA[i] = idx[u];
                EB[i] = idx[v];
            }
            rebuild();
            for (int a = 0; a < S && ok; a++) {
                stampc++;
                for (int k = 0; k < DEG; k++) {
                    int b = EB[adjA[a * DEG + k]];
                    if (mk[b] == stampc) { ok = 0; break; }
                    mk[b] = stampc;
                }
            }
        }
    }
    free(eu); free(ev); free(deg); free(st); free(pos); free(nb);
    free(col); free(stk); free(idx);
    return ok;
}

/* Split d edges with pairwise distinct endpoints around a new pair (a*, b*). */
static int grow(void) {
    if (S + 1 > SMAX || DEG > 64) return 0;
    int chosen[64];
    memset(markA, 0, sizeof(int) * (size_t)S);
    memset(markB, 0, sizeof(int) * (size_t)S);
    for (int i = 0; i < DEG; i++) {
        int e = -1;
        for (int tries = 0; tries < 100000; tries++) {
            int c = rndint(NE);
            if (!markA[EA[c]] && !markB[EB[c]]) { e = c; break; }
        }
        if (e < 0) return 0;
        markA[EA[e]] = 1;
        markB[EB[e]] = 1;
        chosen[i] = e;
    }
    for (int i = 0; i < DEG; i++) {
        int e = chosen[i], f = NE + i;
        int bi = EB[e];
        EB[e] = S;        /* (a_i, b*) */
        EA[f] = S;        /* (a*, b_i) */
        EB[f] = bi;
    }
    NE += DEG;
    S += 1;
    rebuild();
    return 1;
}

static void save_best(void) {
    bestS = S;
    bestNE = NE;
    memcpy(bestEA, EA, sizeof(int) * (size_t)NE);
    memcpy(bestEB, EB, sizeof(int) * (size_t)NE);
}

static void restore_best(void) {
    S = bestS;
    NE = bestNE;
    memcpy(EA, bestEA, sizeof(int) * (size_t)NE);
    memcpy(EB, bestEB, sizeof(int) * (size_t)NE);
    rebuild();
}

static int anneal(int iters, double T0) {
    int cur = cost_fn();
    if (cur == 0) return 1;
    for (int it = 0; it < iters; it++) {
        if ((it & 63) == 0 && elapsed() >= slice_s) return 0;
        double T = T0 * (1.0 - (double)it / iters) + 0.05;
        int e1 = rndint(NE), e2 = rndint(NE);
        if (!valid_exchange(e1, e2)) continue;
        exchange(e1, e2);
        int nc = cost_fn();
        if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
            cur = nc;
            if (cur == 0) return 1;
        } else {
            exchange(e1, e2);
        }
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 6) { printf("0 0\n"); return 0; }
    DEG = atoi(argv[1]);
    D_ = atoi(argv[2]);
    int S0 = atoi(argv[3]);
    uint64_t seed = strtoull(argv[4], NULL, 10);
    slice_s = atof(argv[5]);
    if (DEG < 1 || DEG > 64 || D_ < 1 || S0 < 1) { printf("0 0\n"); return 0; }
    rs = seed * 0x9E3779B97F4A7C15ULL ^ 0x5DEECE66DULL;
    if (rs == 0) rs = 1;

    SMAX = S0 + 400;
    WMAX = (2 * SMAX + 63) >> 6;
    size_t ecap = (size_t)SMAX * DEG + DEG;
    EA = malloc(sizeof(int) * ecap);
    EB = malloc(sizeof(int) * ecap);
    bestEA = malloc(sizeof(int) * ecap);
    bestEB = malloc(sizeof(int) * ecap);
    adjA = malloc(sizeof(int) * ecap);
    adjB = malloc(sizeof(int) * ecap);
    posB = malloc(sizeof(int) * ecap);
    nbr = malloc(sizeof(int) * 2 * (size_t)SMAX * DEG);
    cntA = malloc(sizeof(int) * (size_t)SMAX);
    cntB = malloc(sizeof(int) * (size_t)SMAX);
    markA = malloc(sizeof(int) * (size_t)SMAX);
    markB = malloc(sizeof(int) * (size_t)SMAX);
    mk = calloc((size_t)SMAX, sizeof(int));
    size_t bcap = (size_t)2 * SMAX * WMAX + 64;
    bufA = malloc(sizeof(uint64_t) * bcap);
    bufB = malloc(sizeof(uint64_t) * bcap);
    if (!EA || !EB || !bestEA || !bestEB || !adjA || !adjB || !posB || !nbr ||
        !cntA || !cntB || !markA || !markB || !mk || !bufA || !bufB) {
        printf("0 0\n");
        return 0;
    }

    t0 = clock();
    int have = 0;
    if (!load_graph()) {
        S = S0;
        if (S < DEG) { printf("0 0\n"); return 0; }
        haar_init();
    }
    if (cost_fn() == 0) {
        save_best();
        have = 1;
    } else if (anneal(ITER_REPAIR, 2.0)) {
        save_best();
        have = 1;
    }
    while (!have && elapsed() < slice_s) {
        haar_init();
        if (anneal(ITER_REPAIR, 2.0)) { save_best(); have = 1; }
    }
    if (!have) { printf("0 0\n"); return 0; }

    int fails = 0;
    while (fails < MAXF && elapsed() < slice_s) {
        restore_best();
        if (!grow()) { fails++; continue; }
        if (anneal(ITER_STEP, 2.0)) { save_best(); fails = 0; }
        else fails++;
    }

    restore_best();
    printf("%d %d\n", 2 * S, NE);
    for (int e = 0; e < NE; e++) printf("%d %d\n", EA[e], S + EB[e]);
    fflush(stdout);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact / safe constructions and Python glue.
# ----------------------------------------------------------------------------

K2_CHOICES = [1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 21, 24,
              27, 28, 30, 36, 40, 42, 49, 54, 56, 63, 72, 81, 84, 96, 108, 121,
              128, 162, 243]


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _better(best, cand, d, D):
    """Return cand if it is larger than best and valid, else best."""
    n, e = cand
    if n > best[0] and lib.is_valid(n, e, d, D):
        return (n, e)
    return best


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


def _lift_search(d, D, best, rng, stop):
    """Annealed bi-Cayley lift search until `stop` (a time.monotonic value)."""
    step = 0.08
    retry = None
    while True:
        remaining = stop - time.monotonic()
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
        try:
            n, e = lib.parse_graph_text(out)
        except ValueError:
            n, e = 0, []
        new_best = _better(best, (n, e), d, D)
        ok = new_best is not best
        best = new_best
        if ok:
            step = min(0.4, step * 1.25)
        elif not is_retry:
            retry = (k, m, k2, r)
        else:
            step = max(0.005, step * 0.7)
    return best


def _grow_repair(d, D, best, seconds, rng):
    """Grow-and-repair from the best valid graph for about `seconds` seconds."""
    if seconds < 2.0:
        return best
    try:
        out = lib.run_c(
            C_GROW,
            [d, D, best[0] // 2, rng.randrange(1, 10 ** 9), f"{seconds:.2f}"],
            stdin_graph=best,
            timeout=seconds + 10.0,
        )
        n, e = lib.parse_graph_text(out)
    except (RuntimeError, ValueError):
        return best
    return _better(best, (n, e), d, D)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.9 * time_limit, time_limit - 4.0))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            best = _better(best, pg, d, D)
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    # Two phases for D >= 3: a lift search for the structured start, then a
    # grow-and-repair search that adds vertex pairs to that start graph.
    grow_on = D >= 3 and d >= 3
    lift_stop = start + (0.4 if grow_on else 0.92) * budget
    best = _lift_search(d, D, best, rng, lift_stop)

    if grow_on:
        secs = start + 0.92 * budget - time.monotonic()
        best = _grow_repair(d, D, best, secs, rng)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
