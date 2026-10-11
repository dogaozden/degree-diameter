import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Engine A: simulated annealing over voltages of a bi-Cayley lift over
# Z_m x|_r Z_k2 (element (a, b) coded as a*k2 + b). Used to find a good start.
# Usage: prog d D K m k2 r seed slice
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
        printf("0 0\n");
        return 0;
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
# Engine B (new, bold): growth + annealing on general bipartite graphs.
#
# Start from a valid d-regular bipartite graph G with NA = NB vertices.
# Growth step: pick d edges (a_i, b_i) with all a_i distinct and all b_i
# distinct. Replace each (a_i, b_i) by (x, b_i), where x is a new A vertex,
# and add (a_i, y), where y is a new B vertex. Degrees are preserved and the
# order grows by 2. Then anneal with 2-switches (a1,b1),(a2,b2) ->
# (a1,b2),(a2,b1) to remove all pairs at distance > D.
# Cost = number of unordered pairs at distance > D, computed by bitset balls.
#
# Usage: prog d D seed slice ; stdin = start graph ("n m" + edges, or "0 0").
# Prints the largest valid graph found, or "0 0".
# ----------------------------------------------------------------------------

GROW_C = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

static int DEG, DIAM, HALF, CAP, W, NA, NB, M, EMAX;
static int *ea, *eb, *dg, *nbr, *bestEA, *bestEB, *used, *chosen;
static unsigned char *mat;
static uint64_t *rowX, *rowY;
static int bestM, bestNA, bestNB, hasBest;
static long CURC;
static int stampVal = 0;
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

static int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void rebuild_nbr(void) {
    for (int v = 0; v < NA; v++) dg[v] = 0;
    for (int v = HALF; v < HALF + NB; v++) dg[v] = 0;
    for (int e = 0; e < M; e++) {
        int a = ea[e], b = eb[e];
        nbr[a * DEG + dg[a]++] = b;
        nbr[b * DEG + dg[b]++] = a;
    }
}

/* Number of unordered pairs of active vertices at distance > DIAM. */
static long cost_eval(void) {
    rebuild_nbr();
    for (int s = 0; s < 2; s++) {
        int lo = s ? HALF : 0, hi = s ? HALF + NB : NA;
        for (int v = lo; v < hi; v++) {
            uint64_t *r = rowX + (size_t)v * W;
            memset(r, 0, sizeof(uint64_t) * W);
            r[v >> 6] |= 1ULL << (v & 63);
        }
    }
    uint64_t *cur = rowX, *nxt = rowY;
    for (int lv = 0; lv < DIAM; lv++) {
        for (int s = 0; s < 2; s++) {
            int lo = s ? HALF : 0, hi = s ? HALF + NB : NA;
            for (int v = lo; v < hi; v++) {
                uint64_t *dst = nxt + (size_t)v * W;
                const uint64_t *src = cur + (size_t)v * W;
                memcpy(dst, src, sizeof(uint64_t) * W);
                for (int k = 0; k < dg[v]; k++) {
                    const uint64_t *su = cur + (size_t)nbr[v * DEG + k] * W;
                    for (int w = 0; w < W; w++) dst[w] |= su[w];
                }
            }
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
    }
    long total = 0;
    int tot = NA + NB;
    for (int s = 0; s < 2; s++) {
        int lo = s ? HALF : 0, hi = s ? HALF + NB : NA;
        for (int v = lo; v < hi; v++) {
            const uint64_t *r = cur + (size_t)v * W;
            int pc = 0;
            for (int w = 0; w < W; w++) pc += popc64(r[w]);
            total += tot - pc;
        }
    }
    return total / 2;
}

static void load_state(const int *EA, const int *EB, int m, int na, int nb) {
    M = m; NA = na; NB = nb;
    memcpy(ea, EA, sizeof(int) * (size_t)m);
    memcpy(eb, EB, sizeof(int) * (size_t)m);
    memset(mat, 0, (size_t)CAP * CAP);
    for (int e = 0; e < M; e++) mat[(size_t)ea[e] * CAP + eb[e]] = 1;
}

static void save_best(void) {
    bestM = M; bestNA = NA; bestNB = NB;
    memcpy(bestEA, ea, sizeof(int) * (size_t)M);
    memcpy(bestEB, eb, sizeof(int) * (size_t)M);
    hasBest = 1;
}

static int grow(void) {
    if (NA >= HALF || NB >= HALF) return 0;
    stampVal++;
    int cnt = 0;
    long tries = 0;
    while (cnt < DEG && tries < 2000000) {
        tries++;
        int e = rndint(M);
        int a = ea[e], b = eb[e];
        if (used[a] == stampVal || used[b] == stampVal) continue;
        used[a] = stampVal;
        used[b] = stampVal;
        chosen[cnt++] = e;
    }
    if (cnt < DEG) return 0;
    int newA = NA, newB = HALF + NB;
    for (int i = 0; i < DEG; i++) {
        int e = chosen[i];
        int a = ea[e], b = eb[e];
        mat[(size_t)a * CAP + b] = 0;
        ea[e] = newA;                       /* (a,b) becomes (newA,b) */
        mat[(size_t)newA * CAP + b] = 1;
        ea[M] = a; eb[M] = newB;            /* new edge (a,newB) */
        mat[(size_t)a * CAP + newB] = 1;
        M++;
    }
    NA++; NB++;
    return 1;
}

/* Anneal with 2-switches; returns 1 as soon as cost reaches 0 (state saved). */
static int anneal(int iters, double T0, double T1, clock_t t0, double slice) {
    for (int it = 0; it < iters; it++) {
        if ((it & 63) == 0 && elapsed(t0) >= slice) return 0;
        double T = T0 + (T1 - T0) * (double)it / (double)iters;
        int e1 = rndint(M), e2 = rndint(M);
        if (e1 == e2) continue;
        int a1 = ea[e1], b1 = eb[e1], a2 = ea[e2], b2 = eb[e2];
        if (a1 == a2 || b1 == b2) continue;
        if (mat[(size_t)a1 * CAP + b2] || mat[(size_t)a2 * CAP + b1]) continue;
        mat[(size_t)a1 * CAP + b1] = 0;
        mat[(size_t)a2 * CAP + b2] = 0;
        mat[(size_t)a1 * CAP + b2] = 1;
        mat[(size_t)a2 * CAP + b1] = 1;
        eb[e1] = b2; eb[e2] = b1;
        long nc = cost_eval();
        if (nc <= CURC || rnd01() < exp(-(double)(nc - CURC) / T)) {
            CURC = nc;
            if (CURC == 0) { save_best(); return 1; }
        } else {
            mat[(size_t)a1 * CAP + b2] = 0;
            mat[(size_t)a2 * CAP + b1] = 0;
            mat[(size_t)a1 * CAP + b1] = 1;
            mat[(size_t)a2 * CAP + b2] = 1;
            eb[e1] = b1; eb[e2] = b2;
        }
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t seed = strtoull(argv[3], NULL, 10);
    double slice = atof(argv[4]);
    rs = seed * 0x9E3779B97F4A7C15ULL ^ 0xABCDEFULL;
    if (rs == 0) rs = 1;
    if (DEG < 1 || DIAM < 1) { printf("0 0\n"); return 0; }

    int n0, m0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 <= 0 || m0 < 0) { printf("0 0\n"); return 0; }
    int *U = malloc(sizeof(int) * (size_t)(m0 + 1));
    int *V = malloc(sizeof(int) * (size_t)(m0 + 1));
    for (int e = 0; e < m0; e++) {
        if (scanf("%d %d", &U[e], &V[e]) != 2) { printf("0 0\n"); return 0; }
        if (U[e] < 0 || U[e] >= n0 || V[e] < 0 || V[e] >= n0 || U[e] == V[e]) { printf("0 0\n"); return 0; }
    }

    /* Bipartition by BFS. */
    int *deg0 = calloc(n0, sizeof(int));
    for (int e = 0; e < m0; e++) { deg0[U[e]]++; deg0[V[e]]++; }
    int *off = malloc(sizeof(int) * (n0 + 1));
    off[0] = 0;
    for (int i = 0; i < n0; i++) off[i + 1] = off[i] + deg0[i];
    int *pos = malloc(sizeof(int) * n0);
    memcpy(pos, off, sizeof(int) * n0);
    int *adjl = malloc(sizeof(int) * (size_t)(2 * m0 + 1));
    for (int e = 0; e < m0; e++) {
        adjl[pos[U[e]]++] = V[e];
        adjl[pos[V[e]]++] = U[e];
    }
    int *col = malloc(sizeof(int) * n0);
    int *q = malloc(sizeof(int) * n0);
    for (int i = 0; i < n0; i++) col[i] = -1;
    for (int s = 0; s < n0; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int head = 0, tail = 0;
        q[tail++] = s;
        while (head < tail) {
            int x = q[head++];
            for (int k = off[x]; k < off[x + 1]; k++) {
                int y = adjl[k];
                if (col[y] < 0) { col[y] = 1 - col[x]; q[tail++] = y; }
                else if (col[y] == col[x]) { printf("0 0\n"); return 0; }
            }
        }
    }

    int nA0 = 0, nB0 = 0;
    for (int i = 0; i < n0; i++) { if (col[i] == 0) nA0++; else nB0++; }
    if (nA0 == 0 || nB0 == 0) { printf("0 0\n"); return 0; }

    const int GROW = 200;
    HALF = (nA0 > nB0 ? nA0 : nB0) + GROW;
    CAP = 2 * HALF;
    if ((double)CAP * (double)CAP > 3.0e8) { printf("0 0\n"); return 0; }
    W = (CAP + 63) / 64;
    EMAX = DEG * HALF + DEG + 8;

    ea = malloc(sizeof(int) * EMAX);
    eb = malloc(sizeof(int) * EMAX);
    bestEA = malloc(sizeof(int) * EMAX);
    bestEB = malloc(sizeof(int) * EMAX);
    dg = calloc(CAP, sizeof(int));
    nbr = malloc(sizeof(int) * (size_t)CAP * DEG);
    used = calloc(CAP, sizeof(int));
    chosen = malloc(sizeof(int) * DEG);
    mat = calloc((size_t)CAP * CAP, 1);
    rowX = malloc(sizeof(uint64_t) * (size_t)CAP * W);
    rowY = malloc(sizeof(uint64_t) * (size_t)CAP * W);
    if (!ea || !eb || !bestEA || !bestEB || !dg || !nbr || !used || !chosen || !mat || !rowX || !rowY) {
        printf("0 0\n");
        return 0;
    }

    /* Map vertices: A ids 0.., B ids HALF.. . */
    int *vid = malloc(sizeof(int) * n0);
    int ca = 0, cb = 0;
    for (int i = 0; i < n0; i++) {
        if (col[i] == 0) vid[i] = ca++;
        else vid[i] = HALF + cb++;
    }
    NA = nA0; NB = nB0;
    M = 0;
    int *cntd = dg; /* reuse as degree counter before rebuild */
    for (int e = 0; e < m0; e++) {
        int a, b;
        if (col[U[e]] == 0) { a = vid[U[e]]; b = vid[V[e]]; }
        else { a = vid[V[e]]; b = vid[U[e]]; }
        if (mat[(size_t)a * CAP + b]) { printf("0 0\n"); return 0; }
        mat[(size_t)a * CAP + b] = 1;
        cntd[a]++; cntd[b]++;
        if (cntd[a] > DEG || cntd[b] > DEG) { printf("0 0\n"); return 0; }
        ea[M] = a; eb[M] = b; M++;
    }
    hasBest = 0;

    clock_t t0 = clock();
    CURC = cost_eval();
    if (CURC == 0) save_best();

    const int ITER = 1500;
    int need_new = hasBest;
    int fails = 0;
    while (elapsed(t0) < slice) {
        if (need_new) {
            load_state(bestEA, bestEB, bestM, bestNA, bestNB);
            if (!grow()) break;
            CURC = cost_eval();
            need_new = 0;
            fails = 0;
            if (CURC == 0) { save_best(); need_new = 1; continue; }
        }
        int ok = anneal(ITER, 0.8, 0.1, t0, slice);
        if (ok) {
            need_new = 1;
        } else {
            fails++;
            if (fails >= 8 && hasBest) { need_new = 1; fails = 0; }
        }
    }

    if (!hasBest) { printf("0 0\n"); return 0; }
    printf("%d %d\n", bestNA + bestNB, bestM);
    for (int e = 0; e < bestM; e++) {
        int a = bestEA[e];
        int b = bestNA + (bestEB[e] - HALF);
        printf("%d %d\n", a, b);
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
# Group sampling and the two-phase driver.
# ----------------------------------------------------------------------------

def _sample_group(target, rng):
    """Return (m, k2, r) describing Z_m x|_r Z_k2 with order m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, -(-target // k2))
        r = 1  # r = 1 is the direct product, always valid
        if k2 > 1 and m > 2:
            cands = [c for c in range(2, m) if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m]
            if cands:
                r = rng.choice(cands)
        return m, k2, r
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
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

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Phase A (about 30% of the budget): bi-Cayley lift search for a strong start.
    phase_a_deadline = start + 0.30 * budget
    while True:
        remaining = phase_a_deadline - time.monotonic()
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
                timeout=slice_s + 10.0,
            )
        except RuntimeError:
            break
        try:
            n, e = lib.parse_graph_text(out)
        except ValueError:
            continue
        consider(n, e)

    # Phase B (the rest): grow the best graph by 2 vertices at a time and repair
    # by 2-switch annealing on the exact count of too-distant pairs.
    remaining = deadline - time.monotonic()
    if remaining > 3.0 and best[0] <= 6000:
        try:
            out = lib.run_c(
                GROW_C,
                [d, D, rng.randrange(1, 10 ** 9), f"{remaining - 1.0:.2f}"],
                stdin_graph=best,
                timeout=remaining + 3.0,
            )
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
