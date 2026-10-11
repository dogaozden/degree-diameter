import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Engine A: bi-Cayley lift over one group (K = 1), simulated annealing on S.
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
# Engine B: voltage annealing of bi-Cayley lifts with K base vertices per side.
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
# Engine C (new, bold): grow-and-rewire search on an explicit bipartite graph.
#
# Reads a valid start graph ("n m" + edges) on stdin. Repeatedly:
#   - adds one new A/B vertex pair (with zero degree), then
#   - anneals over degree-preserving 2-switches and "add an edge, evicting
#     one edge from any saturated endpoint" moves, minimising the number of
#     vertex pairs at distance > D (bitset BFS, all sources at once).
# Each time the cost reaches 0 the graph is saved as a snapshot and grown
# again. On failure the last valid snapshot is restored and retried.
# Output: the largest valid graph found ("n m" + edges), or "0 0".
#
# Usage: prog DEG DIAM seed slice_seconds
# ----------------------------------------------------------------------------

REWIRE_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define NMAX 2600
#define WMAX ((NMAX + 63) / 64)
#define STALL 6000

static int DEGC, DIAMC, N;
static double SLICE;
static clock_t T0C;
static unsigned char *adjm;
static int *nb, *deg, *col, *pa, *pb, npa, npb;
static uint64_t *R1, *R2;
static int *eu, *ev, *snapu, *snapv, *snapcol, snapN, snapm;
static uint64_t rs = 88172645463325252ULL;

static inline uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static inline int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static inline double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double elapsed(void) { return (double)(clock() - T0C) / (double)CLOCKS_PER_SEC; }

static void add_edge(int u, int v) {
    adjm[(size_t)u * NMAX + v] = 1;
    adjm[(size_t)v * NMAX + u] = 1;
    nb[(size_t)u * DEGC + deg[u]++] = v;
    nb[(size_t)v * DEGC + deg[v]++] = u;
}

static void del_one(int u, int v) {
    int *row = nb + (size_t)u * DEGC;
    for (int i = 0; i < deg[u]; i++) {
        if (row[i] == v) { row[i] = row[--deg[u]]; return; }
    }
}

static void rem_edge(int u, int v) {
    adjm[(size_t)u * NMAX + v] = 0;
    adjm[(size_t)v * NMAX + u] = 0;
    del_one(u, v);
    del_one(v, u);
}

static void rebuild_lists(void) {
    npa = npb = 0;
    for (int v = 0; v < N; v++) {
        if (col[v] == 0) pa[npa++] = v;
        else pb[npb++] = v;
    }
}

/* Number of ordered (source, vertex) pairs at distance > DIAMC. */
static int cost_eval(void) {
    int Wn = (N + 63) >> 6;
    uint64_t *cur = R1, *nxt = R2;
    memset(cur, 0, sizeof(uint64_t) * (size_t)N * Wn);
    for (int v = 0; v < N; v++) cur[(size_t)v * Wn + (v >> 6)] |= 1ULL << (v & 63);
    for (int lv = 0; lv < DIAMC; lv++) {
        for (int v = 0; v < N; v++) {
            uint64_t *dst = nxt + (size_t)v * Wn;
            const uint64_t *src = cur + (size_t)v * Wn;
            memcpy(dst, src, sizeof(uint64_t) * Wn);
            const int *row = nb + (size_t)v * DEGC;
            for (int i = 0; i < deg[v]; i++) {
                const uint64_t *s2 = cur + (size_t)row[i] * Wn;
                for (int w = 0; w < Wn; w++) dst[w] |= s2[w];
            }
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
    }
    int bad = 0;
    for (int v = 0; v < N; v++) {
        const uint64_t *src = cur + (size_t)v * Wn;
        int c = 0;
        for (int w = 0; w < Wn; w++) c += __builtin_popcountll(src[w]);
        bad += N - c;
    }
    return bad;
}

/* Double-edge swap: (a1,b1),(a2,b2) -> (a1,b2),(a2,b1). Degrees preserved. */
static int move_swap(int *ops) {
    if (npa < 2) return 0;
    int a1 = -1, a2 = -1;
    for (int t = 0; t < 20 && a1 < 0; t++) {
        int x = pa[rndint(npa)];
        if (deg[x] > 0) a1 = x;
    }
    for (int t = 0; t < 20 && a2 < 0; t++) {
        int x = pa[rndint(npa)];
        if (deg[x] > 0) a2 = x;
    }
    if (a1 < 0 || a2 < 0 || a1 == a2) return 0;
    int b1 = nb[(size_t)a1 * DEGC + rndint(deg[a1])];
    int b2 = nb[(size_t)a2 * DEGC + rndint(deg[a2])];
    if (b1 == b2) return 0;
    if (adjm[(size_t)a1 * NMAX + b2] || adjm[(size_t)a2 * NMAX + b1]) return 0;
    rem_edge(a1, b1);
    rem_edge(a2, b2);
    add_edge(a1, b2);
    add_edge(a2, b1);
    ops[0] = a1; ops[1] = b1; ops[2] = a2; ops[3] = b2;
    return 1;
}

static void undo_swap(const int *ops) {
    int a1 = ops[0], b1 = ops[1], a2 = ops[2], b2 = ops[3];
    rem_edge(a1, b2);
    rem_edge(a2, b1);
    add_edge(a1, b1);
    add_edge(a2, b2);
}

/* Add edge (a,b); if a or b is saturated, first evict one random edge there. */
static int move_add(int *ops) {
    if (npa == 0 || npb == 0) return 0;
    int a = pa[rndint(npa)], b = pb[rndint(npb)];
    if (adjm[(size_t)a * NMAX + b]) return 0;
    int ra = -1, rb = -1;
    if (deg[a] >= DEGC) {
        ra = nb[(size_t)a * DEGC + rndint(deg[a])];
        rem_edge(a, ra);
    }
    if (deg[b] >= DEGC) {
        rb = nb[(size_t)b * DEGC + rndint(deg[b])];
        rem_edge(rb, b);
    }
    add_edge(a, b);
    ops[0] = a; ops[1] = b; ops[2] = ra; ops[3] = rb;
    return 1;
}

static void undo_add(const int *ops) {
    int a = ops[0], b = ops[1], ra = ops[2], rb = ops[3];
    rem_edge(a, b);
    if (ra >= 0) add_edge(a, ra);
    if (rb >= 0) add_edge(rb, b);
}

static void save_snapshot(void) {
    snapN = N;
    snapm = 0;
    for (int u = 0; u < N; u++) {
        for (int i = 0; i < deg[u]; i++) {
            int v = nb[(size_t)u * DEGC + i];
            if (u < v) { snapu[snapm] = u; snapv[snapm] = v; snapm++; }
        }
    }
    memcpy(snapcol, col, sizeof(int) * (size_t)N);
}

static void load_edges(int n, const int *us, const int *vs, int m) {
    memset(adjm, 0, (size_t)NMAX * NMAX);
    memset(deg, 0, sizeof(int) * NMAX);
    N = n;
    for (int i = 0; i < m; i++) add_edge(us[i], vs[i]);
}

static void restore_snapshot(void) {
    load_edges(snapN, snapu, snapv, snapm);
    memcpy(col, snapcol, sizeof(int) * (size_t)snapN);
    rebuild_lists();
}

static void grow(void) {
    int a = N, b = N + 1;
    deg[a] = 0; deg[b] = 0;
    col[a] = 0; col[b] = 1;
    N += 2;
    rebuild_lists();
}

static void print_current(void) {
    long m2 = 0;
    for (int u = 0; u < N; u++) m2 += deg[u];
    printf("%d %ld\n", N, m2 / 2);
    for (int u = 0; u < N; u++)
        for (int i = 0; i < deg[u]; i++) {
            int v = nb[(size_t)u * DEGC + i];
            if (u < v) printf("%d %d\n", u, v);
        }
}

static void print_snapshot(void) {
    printf("%d %d\n", snapN, snapm);
    for (int i = 0; i < snapm; i++) printf("%d %d\n", snapu[i], snapv[i]);
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    DEGC = atoi(argv[1]);
    DIAMC = atoi(argv[2]);
    uint64_t seed = strtoull(argv[3], NULL, 10);
    SLICE = atof(argv[4]);
    rs = seed * 0x9E3779B97F4A7C15ULL ^ 0x2545F4914F6CDD1DULL;
    if (rs == 0) rs = 1;
    T0C = clock();
    if (DEGC < 1 || DIAMC < 1) { printf("0 0\n"); return 0; }

    int n, m;
    if (scanf("%d %d", &n, &m) != 2 || n < 1 || n + 2 > NMAX || m < 0 || m > n * DEGC) {
        printf("0 0\n");
        return 0;
    }

    adjm = calloc((size_t)NMAX * NMAX, 1);
    nb = malloc(sizeof(int) * (size_t)NMAX * DEGC);
    deg = calloc(NMAX, sizeof(int));
    col = calloc(NMAX, sizeof(int));
    pa = malloc(sizeof(int) * NMAX);
    pb = malloc(sizeof(int) * NMAX);
    R1 = malloc(sizeof(uint64_t) * (size_t)NMAX * WMAX);
    R2 = malloc(sizeof(uint64_t) * (size_t)NMAX * WMAX);
    eu = malloc(sizeof(int) * (size_t)NMAX * DEGC);
    ev = malloc(sizeof(int) * (size_t)NMAX * DEGC);
    snapu = malloc(sizeof(int) * (size_t)NMAX * DEGC);
    snapv = malloc(sizeof(int) * (size_t)NMAX * DEGC);
    snapcol = malloc(sizeof(int) * NMAX);
    int *q = malloc(sizeof(int) * NMAX);
    if (!adjm || !nb || !deg || !col || !pa || !pb || !R1 || !R2 ||
        !eu || !ev || !snapu || !snapv || !snapcol || !q) {
        printf("0 0\n");
        return 0;
    }

    N = n;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { printf("0 0\n"); return 0; }
        if (u < 0 || u >= n || v < 0 || v >= n || u == v ||
            adjm[(size_t)u * NMAX + v] || deg[u] >= DEGC || deg[v] >= DEGC) {
            printf("0 0\n");
            return 0;
        }
        add_edge(u, v);
    }

    /* Bipartition by BFS; reject if not bipartite. */
    for (int v = 0; v < n; v++) col[v] = -1;
    for (int s = 0; s < n; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int qh = 0, qt = 0;
        q[qt++] = s;
        while (qh < qt) {
            int u = q[qh++];
            for (int i = 0; i < deg[u]; i++) {
                int v = nb[(size_t)u * DEGC + i];
                if (col[v] < 0) { col[v] = 1 - col[u]; q[qt++] = v; }
                else if (col[v] == col[u]) { printf("0 0\n"); return 0; }
            }
        }
    }
    rebuild_lists();

    int cur = cost_eval();
    int have_snap = 0;
    if (cur == 0) { save_snapshot(); have_snap = 1; }

    while (elapsed() < SLICE) {
        if (cur == 0) {
            if (N + 2 > NMAX) break;
            save_snapshot();
            have_snap = 1;
            grow();
            cur = cost_eval();
        }
        int runBest = cur, since = 0;
        for (long it = 0; ; it++) {
            if ((it & 127) == 0 && elapsed() >= SLICE) break;
            if (since > STALL) break;
            double T = 3.0 * (1.0 - (double)since / STALL) + 0.2;
            int ops[4];
            int kind, ok;
            if (rnd01() < 0.5) { kind = 0; ok = move_swap(ops); }
            else { kind = 1; ok = move_add(ops); }
            if (!ok) { since++; continue; }
            int nc = cost_eval();
            if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
                cur = nc;
            } else {
                if (kind == 0) undo_swap(ops);
                else undo_add(ops);
            }
            if (cur < runBest) { runBest = cur; since = 0; }
            else since++;
            if (cur == 0) break;
        }
        if (cur != 0 && have_snap) {
            restore_snapshot();
            cur = cost_eval();
        }
    }

    if (cur == 0) print_current();
    else if (have_snap) print_snapshot();
    else printf("0 0\n");
    fflush(stdout);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Constructions and helpers.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


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
    t0 = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 5.0))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is bipartite.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    pg = _best_pg(d)
    if pg is not None:
        consider(pg[0], pg[1])
        if D == 3 and lib.is_prime_power(d - 1):
            return best

    def at(frac):
        return t0 + frac * budget

    def run_voltage(end_t):
        """Engine B: voltage lifts with K base vertices per side."""
        nonlocal best
        while True:
            remaining = end_t - time.monotonic()
            if remaining < 1.0:
                return
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
                return
            try:
                n, e = lib.parse_graph_text(out)
            except ValueError:
                continue
            consider(n, e)

    def run_bicay(end_t):
        """Engine A: single-group bi-Cayley lifts just above best/2 vertices per side."""
        nonlocal best
        while True:
            remaining = end_t - time.monotonic()
            if remaining < 1.5:
                return
            n_lo = best[0] // 2 + 1
            n_grp = n_lo + rng.randrange(0, max(4, n_lo // 25))
            n_grp = max(n_grp, d + 1)
            if n_grp > 2400:
                return
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
                return
            try:
                n, e = lib.parse_graph_text(out)
            except ValueError:
                continue
            consider(n, e)

    def run_rewire(end_t):
        """Engine C: grow the best graph by vertex pairs and rewire it to restore diameter D."""
        remaining = end_t - time.monotonic()
        if remaining < 2.0:
            return
        try:
            out = lib.run_c(
                REWIRE_SOURCE,
                [d, D, rng.randrange(1, 10 ** 9), f"{remaining:.2f}"],
                stdin_graph=best,
                timeout=remaining + 10.0,
            )
        except RuntimeError:
            return
        try:
            n, e = lib.parse_graph_text(out)
        except ValueError:
            return
        consider(n, e)

    run_voltage(at(0.30))
    run_bicay(at(0.55))
    run_rewire(at(0.92))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
