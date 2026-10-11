import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine 1: simulated annealing over the voltages of a bi-Cayley lift over
# Z_m x|_r Z_k2 (element (a, b) coded as a*k2 + b). Cost = excess distance.
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
# C engine 2 (new, non-symmetric): grow a regular bipartite graph by two
# vertices and repair it by edge-switch annealing. Each switch replaces
# (a1,b1),(a2,b2) by (a1,b2),(a2,b1), so degrees and bipartiteness are kept.
# Cost = number of ordered vertex pairs not joined by a walk of length <= D,
# computed with bitsets. The state is valid iff cost == 0.
# Input: graph on stdin ("n m" + edges), must be d-regular and bipartite.
# Usage: prog d D seed slice_seconds
# Prints the largest valid graph found, or "0 0".
# ----------------------------------------------------------------------------

GROW_C = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXG 150
#define MAXD 40
#define ATT_IT 15000

static int DG, DIAM, NCAP, n, nA, nB;
static int *adj, *Alist, *Blist;
static unsigned char *adjM;
static uint64_t *R1, *R2;
static int *bAdj, *bAlist, *bBlist, bn, bnA, bnB;
static uint64_t rs = 88172645463325252ULL;

#define MADJ(a, b) adjM[(size_t)(a) * NCAP + (b)]

static inline uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static inline int rndint(int m) { return (int)(rnd64() % (uint64_t)m); }
static inline double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static double elapsed_s(clock_t t0) {
    return (double)(clock() - t0) / (double)CLOCKS_PER_SEC;
}

static int find_slot(int v, int target) {
    for (int k = 0; k < DG; k++) if (adj[v * DG + k] == target) return k;
    return -1;
}

/* Number of ordered pairs (v,u) with dist(v,u) > DIAM. */
static int cost_fn(void) {
    int W = (n + 63) >> 6;
    uint64_t *cur = R1, *nxt = R2;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int r = 0; r < DIAM; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *o = nxt + (size_t)v * W;
            const uint64_t *c = cur + (size_t)v * W;
            memcpy(o, c, sizeof(uint64_t) * W);
            for (int k = 0; k < DG; k++) {
                const uint64_t *cu = cur + (size_t)adj[v * DG + k] * W;
                for (int w = 0; w < W; w++) o[w] |= cu[w];
            }
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
    }
    long long total = 0;
    for (int v = 0; v < n; v++) {
        const uint64_t *c = cur + (size_t)v * W;
        int pc = 0;
        for (int w = 0; w < W; w++) pc += pc64(c[w]);
        total += n - pc;
    }
    return (int)total;
}

/* Replace edges (a1,b1),(a2,b2) by (a1,b2),(a2,b1). An involution for fixed slots. */
static void do_switch(int a1, int i1, int a2, int i2) {
    int b1 = adj[a1 * DG + i1], b2 = adj[a2 * DG + i2];
    int s1 = find_slot(b1, a1), s2 = find_slot(b2, a2);
    adj[a1 * DG + i1] = b2;
    adj[a2 * DG + i2] = b1;
    adj[b1 * DG + s1] = a2;
    adj[b2 * DG + s2] = a1;
    MADJ(a1, b1) = 0; MADJ(b1, a1) = 0;
    MADJ(a2, b2) = 0; MADJ(b2, a2) = 0;
    MADJ(a1, b2) = 1; MADJ(b2, a1) = 1;
    MADJ(a2, b1) = 1; MADJ(b1, a2) = 1;
}

static int anneal(clock_t t0, double slice, int cur) {
    for (int it = 0; it < ATT_IT && cur > 0; it++) {
        if ((it & 31) == 0 && elapsed_s(t0) >= slice) break;
        double T = 3.0 * (1.0 - (double)it / ATT_IT) + 0.1;
        int a1 = Alist[rndint(nA)], a2 = Alist[rndint(nA)];
        if (a1 == a2) continue;
        int i1 = rndint(DG), i2 = rndint(DG);
        int b1 = adj[a1 * DG + i1], b2 = adj[a2 * DG + i2];
        if (b1 == b2) continue;
        if (MADJ(a1, b2) || MADJ(a2, b1)) continue;
        do_switch(a1, i1, a2, i2);
        int nc = cost_fn();
        if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
            cur = nc;
        } else {
            do_switch(a1, i1, a2, i2);
        }
    }
    return cur;
}

/* Add a fresh A-vertex a = n and B-vertex b = n+1 (edge a-b). Remove DG-1 edges
   (x_j, y_j) with distinct endpoints and replace them by x_j-b and y_j-a. Degrees stay DG. */
static int grow(void) {
    if (nA == 0 || n + 2 > NCAP) return 0;
    int X[MAXD], Y[MAXD], k = 0;
    for (int tries = 0; tries < 5000 && k < DG - 1; tries++) {
        int x = Alist[rndint(nA)], i = rndint(DG), y = adj[x * DG + i];
        int ok = 1;
        for (int j = 0; j < k; j++) if (X[j] == x || Y[j] == y) { ok = 0; break; }
        if (ok) { X[k] = x; Y[k] = y; k++; }
    }
    if (k < DG - 1) return 0;
    int a = n, b = n + 1;
    Alist[nA++] = a;
    Blist[nB++] = b;
    n += 2;
    for (int j = 0; j < k; j++) {
        int x = X[j], y = Y[j];
        int sx = find_slot(x, y), sy = find_slot(y, x);
        adj[x * DG + sx] = b;
        adj[y * DG + sy] = a;
        MADJ(x, y) = 0; MADJ(y, x) = 0;
        MADJ(x, b) = 1; MADJ(b, x) = 1;
        MADJ(y, a) = 1; MADJ(a, y) = 1;
        adj[a * DG + j] = y;
        adj[b * DG + j] = x;
    }
    adj[a * DG + DG - 1] = b;
    adj[b * DG + DG - 1] = a;
    MADJ(a, b) = 1; MADJ(b, a) = 1;
    return 1;
}

static void save_base(void) {
    bn = n; bnA = nA; bnB = nB;
    memcpy(bAdj, adj, sizeof(int) * (size_t)n * DG);
    memcpy(bAlist, Alist, sizeof(int) * nA);
    memcpy(bBlist, Blist, sizeof(int) * nB);
}

static void restore_base(void) {
    n = bn; nA = bnA; nB = bnB;
    memcpy(adj, bAdj, sizeof(int) * (size_t)n * DG);
    memcpy(Alist, bAlist, sizeof(int) * nA);
    memcpy(Blist, bBlist, sizeof(int) * nB);
    memset(adjM, 0, (size_t)NCAP * NCAP);
    for (int v = 0; v < n; v++)
        for (int k = 0; k < DG; k++) MADJ(v, adj[v * DG + k]) = 1;
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    DG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t seed = strtoull(argv[3], NULL, 10);
    double slice = atof(argv[4]);
    rs = seed * 0x9E3779B97F4A7C15ULL ^ 0xABCDEFULL;
    if (rs == 0) rs = 1;
    if (DG < 2 || DG > MAXD || DIAM < 1) { printf("0 0\n"); return 0; }

    int n0, m0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 < 2 || m0 < 0) { printf("0 0\n"); return 0; }
    NCAP = n0 + 2 * MAXG;
    int WMAX = (NCAP + 63) / 64;
    adj = malloc(sizeof(int) * (size_t)NCAP * DG);
    bAdj = malloc(sizeof(int) * (size_t)NCAP * DG);
    Alist = malloc(sizeof(int) * NCAP);
    Blist = malloc(sizeof(int) * NCAP);
    bAlist = malloc(sizeof(int) * NCAP);
    bBlist = malloc(sizeof(int) * NCAP);
    adjM = calloc((size_t)NCAP * NCAP, 1);
    R1 = malloc(sizeof(uint64_t) * (size_t)NCAP * WMAX);
    R2 = malloc(sizeof(uint64_t) * (size_t)NCAP * WMAX);
    int *dg = calloc(NCAP, sizeof(int));
    int *side = malloc(sizeof(int) * NCAP);
    int *stk = malloc(sizeof(int) * NCAP);
    if (!adj || !bAdj || !Alist || !Blist || !bAlist || !bBlist || !adjM ||
        !R1 || !R2 || !dg || !side || !stk) { printf("0 0\n"); return 0; }

    int ok = 1;
    for (int e = 0; e < m0 && ok; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { ok = 0; break; }
        if (u < 0 || v < 0 || u >= n0 || v >= n0 || u == v ||
            dg[u] >= DG || dg[v] >= DG || MADJ(u, v)) { ok = 0; break; }
        adj[u * DG + dg[u]++] = v;
        adj[v * DG + dg[v]++] = u;
        MADJ(u, v) = 1; MADJ(v, u) = 1;
    }
    for (int v = 0; v < n0 && ok; v++) if (dg[v] != DG) ok = 0;
    for (int v = 0; v < n0; v++) side[v] = -1;
    for (int s = 0; s < n0 && ok; s++) {
        if (side[s] != -1) continue;
        side[s] = 0;
        int sp = 0;
        stk[sp++] = s;
        while (sp > 0 && ok) {
            int u = stk[--sp];
            for (int k = 0; k < DG; k++) {
                int v = adj[u * DG + k];
                if (side[v] == -1) { side[v] = 1 - side[u]; stk[sp++] = v; }
                else if (side[v] == side[u]) { ok = 0; break; }
            }
        }
    }
    if (!ok) { printf("0 0\n"); return 0; }
    nA = 0; nB = 0;
    for (int v = 0; v < n0; v++) {
        if (side[v] == 0) Alist[nA++] = v;
        else Blist[nB++] = v;
    }
    if (nA == 0 || nB == 0) { printf("0 0\n"); return 0; }
    n = n0;

    clock_t t0 = clock();
    int cur = cost_fn();
    while (cur > 0 && elapsed_s(t0) < slice) cur = anneal(t0, slice, cur);
    if (cur != 0) { printf("0 0\n"); return 0; }
    save_base();

    while (elapsed_s(t0) < slice) {
        if (n + 2 > NCAP) break;
        restore_base();
        if (!grow()) continue;
        cur = cost_fn();
        cur = anneal(t0, slice, cur);
        if (cur == 0) save_base();
    }

    printf("%d %d\n", bn, bnA * DG);
    for (int i = 0; i < bnA; i++) {
        int a = bAlist[i];
        for (int k = 0; k < DG; k++) printf("%d %d\n", a, bAdj[a * DG + k]);
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
# Helpers.
# ----------------------------------------------------------------------------

def _is_regular(n, edges, d):
    """True if every vertex of the graph has degree exactly d."""
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
    return all(x == d for x in deg)


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


def _grow(best, d, D, seed, end_time):
    """Run the switch-annealing grower on a regular graph; return a larger valid graph or None."""
    n, edges = best
    slice_s = end_time - time.monotonic()
    if slice_s < 2.0:
        return None
    try:
        out = lib.run_c(GROW_C, [d, D, seed, f"{slice_s:.2f}"],
                        stdin_graph=(n, edges), timeout=slice_s + 10.0)
        n2, e2 = lib.parse_graph_text(out)
    except (RuntimeError, ValueError):
        return None
    if n2 > n and lib.is_valid(n2, e2, d, D):
        return n2, e2
    return None


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.9 * time_limit, time_limit - 4.0))
    deadline = start + budget
    lift_deadline = start + 0.45 * budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        """Adopt (n, e) if it is larger and valid."""
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
            return True
        return False

    # Exact constructions.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() < lift_deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Stage 1: group-lift annealing (the strongest known structure so far).
    step = 0.08
    while True:
        remaining = lift_deadline - time.monotonic()
        if remaining < 1.0:
            break
        slice_s = min(remaining, 10.0)
        k = rng.choice([1, 1, 2, 2, 3])
        want = best[0] * (1.0 + step)
        target = max(2, math.ceil(want / (2 * k)))
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
            step = max(0.005, step * 0.7)
            continue
        if consider(n, e):
            step = min(0.4, step * 1.25)
        else:
            step = max(0.005, step * 0.7)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))

    # Stage 2 (new): grow the best regular graph by two vertices at a time and
    # repair with edge-switch annealing. Non-symmetric, so it can leave the
    # group-lift family.
    grow_end = deadline - 1.5
    if time.monotonic() < grow_end - 2.0 and _is_regular(best[0], best[1], d):
        grown = _grow(best, d, D, rng.randrange(1, 10 ** 9), grow_end)
        if grown is not None:
            best = grown

    # Spare-degree extension on the best graph.
    try:
        n2, e2 = _extend_spare(best[0], best[1], d, D, deadline)
        if n2 > best[0] and lib.is_valid(n2, e2, d, D):
            best = (n2, e2)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
