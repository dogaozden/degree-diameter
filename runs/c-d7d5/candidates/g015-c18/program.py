import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Seed engine (unchanged from the parent): simulated annealing over the voltages
# of a bi-Cayley lift over Z_m x|_r Z_k2. It supplies a valid d-regular bipartite
# graph to start from.
# Usage: prog d D K m k2 r seed slice_seconds
# ----------------------------------------------------------------------------

LIFT_C = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define PEN 1000
#define BIGCOST (1 << 30)

static int DEG, DIAM, K, MM, K2, G, N, NE;
static int POWR[64];
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

    if (DEG < 1 || DIAM < 1 || K < 1 || MM < 1 || K2 < 1 || K2 > 60) {
        printf("0 0\n");
        return 0;
    }
    if (gcd_int(r, MM) != 1) { printf("0 0\n"); return 0; }
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
# New engine: degree-preserving 2-switch annealing on the whole graph, with
# vertex-pair insertion. Starting from a valid d-regular bipartite graph, it
# inserts one A-vertex and one B-vertex (each gets d edges taken from a matching
# of existing edges), then anneals with bipartite 2-switches to drive the number
# of pairs at distance > D back to zero. Each success is recorded and the graph
# grows again. Cost = unordered pairs at distance > D, computed by bitset BFS.
#
# Usage: prog d D NCAP n0 seed slice_seconds   (stdin: start graph or "0 0")
# Prints the largest valid graph found ("n m" + edges) or "0 0".
# ----------------------------------------------------------------------------

AUG_C = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

static int DEG, DIAM, NCAP, W, n, ecount, ecap, best_n, best_e;
static int *ea, *eb, *best_ea, *best_eb, *cyc_ea, *cyc_eb;
static unsigned char *has;
static int *nbr, *dg, *chosen, *colr, *qu, *ord, *cand;
static unsigned char *usedA, *usedB;
static uint64_t *bufA, *bufB;
static uint64_t rs = 88172645463325252ULL;
static clock_t t0;

static inline uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static inline int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }
static inline double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double elapsed(void) { return (double)(clock() - t0) / (double)CLOCKS_PER_SEC; }

static inline int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Unordered pairs at distance > DIAM. */
static long long cost_fn(void) {
    int N = n;
    for (int v = 0; v < N; v++) dg[v] = 0;
    for (int e = 0; e < ecount; e++) {
        int a = ea[e], b = eb[e];
        nbr[(size_t)a * DEG + dg[a]++] = b;
        nbr[(size_t)b * DEG + dg[b]++] = a;
    }
    uint64_t *cur = bufA, *nxt = bufB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)N * W);
    for (int v = 0; v < N; v++) cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int s = 0; s < DIAM; s++) {
        for (int v = 0; v < N; v++) {
            uint64_t *o = nxt + (size_t)v * W;
            const uint64_t *c = cur + (size_t)v * W;
            memcpy(o, c, sizeof(uint64_t) * W);
            const int *nb = nbr + (size_t)v * DEG;
            int k = dg[v];
            for (int t = 0; t < k; t++) {
                const uint64_t *cu = cur + (size_t)nb[t] * W;
                for (int w = 0; w < W; w++) o[w] |= cu[w];
            }
        }
        uint64_t *tmp = cur; cur = nxt; nxt = tmp;
    }
    long long cnt = 0;
    for (size_t i = 0; i < (size_t)N * W; i++) cnt += popc(cur[i]);
    return ((long long)N * N - cnt) / 2;
}

static void rebuild_has(void) {
    for (int i = 0; i < n; i++) memset(has + (size_t)i * NCAP, 0, (size_t)n);
    for (int e = 0; e < ecount; e++) has[(size_t)ea[e] * NCAP + eb[e]] = 1;
}

static void save_best(void) {
    memcpy(best_ea, ea, sizeof(int) * ecount);
    memcpy(best_eb, eb, sizeof(int) * ecount);
    best_n = n;
    best_e = ecount;
}

static void save_cyc(void) {
    memcpy(cyc_ea, ea, sizeof(int) * ecount);
    memcpy(cyc_eb, eb, sizeof(int) * ecount);
}

static void load_cyc(void) {
    memcpy(ea, cyc_ea, sizeof(int) * ecount);
    memcpy(eb, cyc_eb, sizeof(int) * ecount);
    rebuild_has();
}

/* Read a d-regular bipartite start graph. Returns 1 on success. */
static int read_start(void) {
    int nn = 0, mm = 0;
    if (scanf("%d %d", &nn, &mm) != 2) return 0;
    if (nn < 2 || nn > NCAP || mm <= 0 || mm > ecap) return 0;
    if ((long long)nn * DEG != 2LL * mm) return 0;
    n = nn;
    ecount = mm;
    memset(has, 0, (size_t)NCAP * NCAP);
    for (int e = 0; e < mm; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) goto fail;
        if (u < 0 || v < 0 || u >= nn || v >= nn || u == v) goto fail;
        if (has[(size_t)u * NCAP + v] || has[(size_t)v * NCAP + u]) goto fail;
        has[(size_t)u * NCAP + v] = 1;
        ea[e] = u;
        eb[e] = v;
    }
    for (int v = 0; v < nn; v++) dg[v] = 0;
    for (int e = 0; e < mm; e++) { dg[ea[e]]++; dg[eb[e]]++; }
    for (int v = 0; v < nn; v++) if (dg[v] != DEG) goto fail;
    for (int v = 0; v < nn; v++) dg[v] = 0;
    for (int e = 0; e < mm; e++) {
        int a = ea[e], b = eb[e];
        nbr[(size_t)a * DEG + dg[a]++] = b;
        nbr[(size_t)b * DEG + dg[b]++] = a;
    }
    for (int v = 0; v < nn; v++) colr[v] = -1;
    for (int s = 0; s < nn; s++) {
        if (colr[s] >= 0) continue;
        colr[s] = 0;
        int qh = 0, qt = 0;
        qu[qt++] = s;
        while (qh < qt) {
            int u = qu[qh++];
            for (int k = 0; k < DEG; k++) {
                int v = nbr[(size_t)u * DEG + k];
                if (colr[v] < 0) {
                    colr[v] = 1 - colr[u];
                    qu[qt++] = v;
                } else if (colr[v] == colr[u]) {
                    goto fail;
                }
            }
        }
    }
    for (int e = 0; e < mm; e++) {
        if (colr[ea[e]] != 0) { int t = ea[e]; ea[e] = eb[e]; eb[e] = t; }
    }
    rebuild_has();
    return 1;
fail:
    memset(has, 0, (size_t)NCAP * NCAP);
    return 0;
}

/* Random d-regular bipartite graph on N vertices (A = 0..h-1, B = h..N-1). */
static int random_start(int N) {
    int h = N / 2;
    n = N;
    ecount = 0;
    memset(has, 0, (size_t)NCAP * NCAP);
    for (int layer = 0; layer < DEG; layer++) {
        int ok = 0;
        for (int att = 0; att < 400 && !ok; att++) {
            int base = ecount;
            for (int i = 0; i < h; i++) ord[i] = i;
            for (int i = h - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int t = ord[i]; ord[i] = ord[j]; ord[j] = t;
            }
            memset(usedB, 0, (size_t)NCAP);
            ok = 1;
            for (int q = 0; q < h && ok; q++) {
                int i = ord[q], nc = 0;
                for (int j = 0; j < h; j++)
                    if (!usedB[j] && !has[(size_t)i * NCAP + h + j]) cand[nc++] = j;
                if (nc == 0) { ok = 0; break; }
                int j = cand[rndint(nc)];
                usedB[j] = 1;
                has[(size_t)i * NCAP + h + j] = 1;
                ea[ecount] = i;
                eb[ecount] = h + j;
                ecount++;
            }
            if (!ok) {
                for (int e = base; e < ecount; e++) has[(size_t)ea[e] * NCAP + eb[e]] = 0;
                ecount = base;
            }
        }
        if (!ok) return 0;
    }
    return 1;
}

/* Add one A-vertex x = n and one B-vertex y = n+1. Take a matching of DEG edges
   (distinct A ends and distinct B ends); each chosen (a,b) becomes (x,b) and
   (a,y). Degrees of old vertices are unchanged; x and y get DEG edges each. */
static int insert_pair(void) {
    if (n + 2 > NCAP) return 0;
    if (ecount + DEG > ecap) return 0;
    int cnt = 0, tries = 0;
    while (cnt < DEG && tries < 200000) {
        tries++;
        int e = rndint(ecount);
        int a = ea[e], b = eb[e];
        if (usedA[a] || usedB[b]) continue;
        usedA[a] = 1;
        usedB[b] = 1;
        chosen[cnt++] = e;
    }
    for (int i = 0; i < cnt; i++) {
        usedA[ea[chosen[i]]] = 0;
        usedB[eb[chosen[i]]] = 0;
    }
    if (cnt < DEG) return 0;
    int x = n, y = n + 1;
    for (int i = 0; i < cnt; i++) {
        int e = chosen[i];
        int a = ea[e], b = eb[e];
        has[(size_t)a * NCAP + b] = 0;
        ea[e] = x;
        eb[e] = b;
        has[(size_t)x * NCAP + b] = 1;
        ea[ecount] = a;
        eb[ecount] = y;
        has[(size_t)a * NCAP + y] = 1;
        ecount++;
    }
    n += 2;
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 7) {
        printf("0 0\n");
        return 0;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    NCAP = atoi(argv[3]);
    int n0 = atoi(argv[4]);
    uint64_t seed = strtoull(argv[5], NULL, 10);
    double slice = atof(argv[6]);
    if (DEG < 1 || DIAM < 1 || NCAP < 2 * DEG + 2 || NCAP > 6000) {
        printf("0 0\n");
        return 0;
    }
    W = (NCAP + 63) / 64;
    ecap = NCAP * DEG / 2 + 2 * DEG + 4;
    rs = seed * 0x9E3779B97F4A7C15ULL ^ 0x51ED2701ULL;
    if (rs == 0) rs = 1;

    ea = malloc(sizeof(int) * ecap);
    eb = malloc(sizeof(int) * ecap);
    best_ea = malloc(sizeof(int) * ecap);
    best_eb = malloc(sizeof(int) * ecap);
    cyc_ea = malloc(sizeof(int) * ecap);
    cyc_eb = malloc(sizeof(int) * ecap);
    has = calloc((size_t)NCAP * NCAP, 1);
    nbr = malloc(sizeof(int) * (size_t)NCAP * DEG);
    dg = malloc(sizeof(int) * NCAP);
    chosen = malloc(sizeof(int) * DEG);
    colr = malloc(sizeof(int) * NCAP);
    qu = malloc(sizeof(int) * NCAP);
    ord = malloc(sizeof(int) * NCAP);
    cand = malloc(sizeof(int) * NCAP);
    usedA = calloc(NCAP, 1);
    usedB = calloc(NCAP, 1);
    bufA = calloc((size_t)NCAP * W, sizeof(uint64_t));
    bufB = calloc((size_t)NCAP * W, sizeof(uint64_t));
    if (!ea || !eb || !best_ea || !best_eb || !cyc_ea || !cyc_eb || !has || !nbr || !dg ||
        !chosen || !colr || !qu || !ord || !cand || !usedA || !usedB || !bufA || !bufB) {
        printf("0 0\n");
        return 0;
    }

    t0 = clock();
    best_e = 0;
    best_n = 0;

    if (!read_start()) {
        int N = n0;
        if (N < 2 * DEG) N = 2 * DEG;
        if (N & 1) N++;
        if (N > NCAP) N = NCAP - (NCAP & 1);
        if (N < 2 * DEG || !random_start(N)) {
            printf("0 0\n");
            return 0;
        }
    }

    const int L = 3000;
    const double T0 = 1.5, T1 = 0.08;
    while (elapsed() < slice) {
        long long cur = cost_fn();
        if (cur == 0) {
            save_best();
            if (!insert_pair()) break;
            continue;
        }
        long long cbest = cur;
        save_cyc();
        for (int it = 0; it < L && elapsed() < slice; it++) {
            int e1 = rndint(ecount), e2 = rndint(ecount);
            if (e1 == e2) continue;
            int a = ea[e1], b = eb[e1], c = ea[e2], d = eb[e2];
            if (a == c || b == d) continue;
            if (has[(size_t)a * NCAP + d] || has[(size_t)c * NCAP + b]) continue;
            double T = T0 * pow(T1 / T0, (double)it / L);
            has[(size_t)a * NCAP + b] = 0;
            has[(size_t)c * NCAP + d] = 0;
            has[(size_t)a * NCAP + d] = 1;
            has[(size_t)c * NCAP + b] = 1;
            eb[e1] = d;
            eb[e2] = b;
            long long nc = cost_fn();
            if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
                cur = nc;
                if (cur < cbest) {
                    cbest = cur;
                    save_cyc();
                }
                if (cur == 0) break;
            } else {
                has[(size_t)a * NCAP + d] = 0;
                has[(size_t)c * NCAP + b] = 0;
                has[(size_t)a * NCAP + b] = 1;
                has[(size_t)c * NCAP + d] = 1;
                eb[e1] = b;
                eb[e2] = d;
            }
        }
        if (cur == 0) {
            save_best();
            if (!insert_pair()) break;
            continue;
        }
        if (cur > cbest) load_cyc();
    }

    if (best_e > 0) {
        printf("%d %d\n", best_n, best_e);
        for (int e = 0; e < best_e; e++) printf("%d %d\n", best_ea[e], best_eb[e]);
    } else {
        printf("0 0\n");
    }
    fflush(stdout);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python glue.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _sample_group(target, rng):
    """Return (m, k2, r) describing Z_m x|_r Z_k2 with order m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, -(-target // k2))
        r = 1
        if k2 > 1 and m > 2:
            cands = [c for c in range(2, m) if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m]
            if cands:
                r = rng.choice(cands)
        return m, k2, r
    return None


def _is_regular(n, edges, d):
    """True if every vertex 0..n-1 has degree exactly d."""
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
    return all(x == d for x in deg)


def build(d, D, seed, time_limit):
    t_start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 5.0))
    deadline = t_start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact constructions.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best
        if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                ap = lib.araujo_lopez_graph(d - 2)
                consider(ap[0], ap[1])
            except (ValueError, RuntimeError):
                pass

    # Phase 1: voltage-lift seed (the parent's construction), a minority of the budget.
    now = time.monotonic()
    lift_deadline = now + 0.35 * (deadline - now)
    while True:
        remaining = lift_deadline - time.monotonic()
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
                LIFT_C,
                [d, D, k, m, k2, r, rng.randrange(1, 10 ** 9), f"{slice_s:.2f}"],
                timeout=slice_s + 5.0,
            )
        except RuntimeError:
            break
        try:
            n, e = lib.parse_graph_text(out)
        except ValueError:
            continue
        consider(n, e)

    # Phase 2: grow from the best regular graph by vertex-pair insertion and
    # degree-preserving annealing (a different construction from voltage lifts).
    remaining = deadline - time.monotonic()
    ncap = min(lib.moore_bound(d, D), 4000)
    if remaining >= 3.0 and ncap >= best[0] + 2:
        start_graph = best if _is_regular(best[0], best[1], d) else None
        slice_s = remaining - 1.5
        try:
            out = lib.run_c(
                AUG_C,
                [d, D, ncap, 2 * d, rng.randrange(1, 10 ** 9), f"{slice_s:.2f}"],
                stdin_graph=start_graph,
                timeout=slice_s + 4.0,
            )
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
