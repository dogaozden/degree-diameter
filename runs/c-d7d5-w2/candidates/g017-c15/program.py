import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Engine 1 (lift search): simulated annealing over the voltages of a bi-Cayley
# lift over Z_m x|_r Z_k2. Produces the regular starting graph.
# Usage: prog d D K m k2 r seed slice_seconds. Prints a valid graph or "0 0".
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
# Engine 2 (growth + repair, a different construction family from lifts):
# works on a d-regular bipartite graph given on stdin. Repeatedly:
#   1. Restore the best valid graph.
#   2. Add two vertices a (side A) and b (side B) while keeping regularity:
#      remove d-1 edges x_i-y_i with distinct endpoints, add x_i-b, a-y_i, and a-b.
#   3. Repair by simulated annealing with degree-preserving 2-switches
#      (a1-b1, a2-b2 -> a1-b2, a2-b1), minimising the number of vertex pairs
#      at distance > D. Distances come from bit-parallel ball expansion.
# Output is always the largest valid graph found (the input if nothing better).
# Usage: prog d D seed slice_seconds. Prints "n m" plus edges, or "0 0".
# ----------------------------------------------------------------------------

REPAIR_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXADD 600
#define MAXDEG 200

static int DD, DIAM, N, NEDGE, NCAP, NEC, WCAP;
static int *eA, *eB, *bA, *bB, *adj, *cnt, *mk;
static int bestN, bestNE;
static uint64_t *bufX, *bufY;
static uint64_t rs = 88172645463325252ULL;
static int stampg = 0;
static int chosen[MAXDEG];
static clock_t T0G;
static double SLICE;

static inline uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static inline int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static inline double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double elapsed_s(void) {
    return (double)(clock() - T0G) / (double)CLOCKS_PER_SEC;
}

static inline int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void rebuild_adj(void) {
    memset(cnt, 0, sizeof(int) * (size_t)NCAP);
    for (int e = 0; e < NEDGE; e++) {
        int a = eA[e], b = eB[e];
        adj[(size_t)a * DD + cnt[a]++] = b;
        adj[(size_t)b * DD + cnt[b]++] = a;
    }
}

static int has_edge(int a, int b) {
    const int *p = adj + (size_t)a * DD;
    for (int k = 0; k < DD; k++) if (p[k] == b) return 1;
    return 0;
}

static void repl(int v, int o, int nw) {
    int *p = adj + (size_t)v * DD;
    for (int k = 0; k < DD; k++) if (p[k] == o) { p[k] = nw; return; }
}

/* Swap the B-ends of edges e1 and e2. Applying it twice restores the state. */
static void raw_swap(int e1, int e2) {
    int a1 = eA[e1], b1 = eB[e1], a2 = eA[e2], b2 = eB[e2];
    repl(a1, b1, b2);
    repl(b1, a1, a2);
    repl(a2, b2, b1);
    repl(b2, a2, a1);
    eB[e1] = b2;
    eB[e2] = b1;
}

/* Number of unordered vertex pairs at distance > DIAM. Zero iff valid. */
static long long cost_fn(void) {
    int W = (N + 63) / 64;
    uint64_t *cur = bufX, *nxt = bufY;
    memset(cur, 0, sizeof(uint64_t) * (size_t)N * W);
    for (int v = 0; v < N; v++) cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int t = 0; t < DIAM; t++) {
        for (int v = 0; v < N; v++) {
            uint64_t *o = nxt + (size_t)v * W;
            const uint64_t *c = cur + (size_t)v * W;
            memcpy(o, c, sizeof(uint64_t) * (size_t)W);
            const int *p = adj + (size_t)v * DD;
            for (int k = 0; k < DD; k++) {
                const uint64_t *c2 = cur + (size_t)p[k] * W;
                for (int w = 0; w < W; w++) o[w] |= c2[w];
            }
        }
        uint64_t *tmp = cur; cur = nxt; nxt = tmp;
    }
    long long reached = 0;
    size_t tot = (size_t)N * W;
    for (size_t i = 0; i < tot; i++) reached += popc64(cur[i]);
    return ((long long)N * N - reached) / 2;
}

/* Add a vertex pair (a = N on side A, b = N+1 on side B) keeping regularity. */
static int grow(void) {
    int k = DD - 1;
    if (N + 2 > NCAP) return 0;
    stampg++;
    int nch = 0, tries = 0;
    while (nch < k && tries < 200000) {
        tries++;
        int e = rndint(NEDGE);
        int a = eA[e], b = eB[e];
        if (mk[a] == stampg || mk[b] == stampg) continue;
        mk[a] = stampg;
        mk[b] = stampg;
        chosen[nch++] = e;
    }
    if (nch < k) return 0;
    int a = N, b = N + 1;
    for (int i = 0; i < k; i++) {
        int e = chosen[i];
        int y = eB[e];
        eB[e] = b;                      /* x - b */
        eA[NEDGE + i] = a;              /* a - y */
        eB[NEDGE + i] = y;
    }
    eA[NEDGE + k] = a;                  /* a - b */
    eB[NEDGE + k] = b;
    NEDGE += k + 1;
    N += 2;
    return 1;
}

static long long anneal(int iters, double Tstart) {
    rebuild_adj();
    long long cur = cost_fn();
    for (int it = 0; it < iters && cur > 0; it++) {
        if ((it & 63) == 0 && elapsed_s() >= SLICE) break;
        double T = Tstart * (1.0 - (double)it / iters) + 0.02;
        int e1 = rndint(NEDGE), e2 = rndint(NEDGE);
        if (e1 == e2) continue;
        int a1 = eA[e1], b1 = eB[e1], a2 = eA[e2], b2 = eB[e2];
        if (a1 == a2 || b1 == b2) continue;
        if (has_edge(a1, b2) || has_edge(a2, b1)) continue;
        raw_swap(e1, e2);
        long long nc = cost_fn();
        if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) cur = nc;
        else raw_swap(e1, e2);
    }
    return cur;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    DD = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t seed = strtoull(argv[3], NULL, 10);
    SLICE = atof(argv[4]);
    rs = seed * 0x9E3779B97F4A7C15ULL ^ 0x5DEECE66DULL;
    if (rs == 0) rs = 1;
    T0G = clock();

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 < 1 || m0 < 0 || DD < 2 || DD > MAXDEG || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    NCAP = n0 + 2 * MAXADD;
    WCAP = (NCAP + 63) / 64;
    NEC = (NCAP * DD) / 2 + DD + 4;
    eA = malloc(sizeof(int) * (size_t)NEC);
    eB = malloc(sizeof(int) * (size_t)NEC);
    bA = malloc(sizeof(int) * (size_t)NEC);
    bB = malloc(sizeof(int) * (size_t)NEC);
    adj = malloc(sizeof(int) * (size_t)NCAP * DD);
    cnt = malloc(sizeof(int) * (size_t)NCAP);
    mk = calloc((size_t)NCAP, sizeof(int));
    bufX = malloc(sizeof(uint64_t) * (size_t)NCAP * WCAP);
    bufY = malloc(sizeof(uint64_t) * (size_t)NCAP * WCAP);
    int *eu = malloc(sizeof(int) * (size_t)(m0 + 1));
    int *ev = malloc(sizeof(int) * (size_t)(m0 + 1));
    int *deg = calloc((size_t)n0, sizeof(int));
    int *col = malloc(sizeof(int) * (size_t)n0);
    int *st = malloc(sizeof(int) * (size_t)n0);
    if (!eA || !eB || !bA || !bB || !adj || !cnt || !mk || !bufX || !bufY ||
        !eu || !ev || !deg || !col || !st) {
        printf("0 0\n");
        return 0;
    }

    for (int e = 0; e < m0; e++) {
        if (scanf("%d %d", &eu[e], &ev[e]) != 2) { printf("0 0\n"); return 0; }
        if (eu[e] < 0 || eu[e] >= n0 || ev[e] < 0 || ev[e] >= n0 || eu[e] == ev[e]) {
            printf("0 0\n");
            return 0;
        }
        deg[eu[e]]++;
        deg[ev[e]]++;
    }
    for (int v = 0; v < n0; v++) if (deg[v] != DD) { printf("0 0\n"); return 0; }

    /* Bipartition by BFS. */
    memset(cnt, 0, sizeof(int) * (size_t)n0);
    for (int e = 0; e < m0; e++) {
        int u = eu[e], v = ev[e];
        adj[(size_t)u * DD + cnt[u]++] = v;
        adj[(size_t)v * DD + cnt[v]++] = u;
    }
    for (int v = 0; v < n0; v++) col[v] = -1;
    int bip = 1;
    for (int s = 0; s < n0 && bip; s++) {
        if (col[s] != -1) continue;
        col[s] = 0;
        int sp = 0;
        st[sp++] = s;
        while (sp && bip) {
            int u = st[--sp];
            for (int k = 0; k < DD; k++) {
                int v = adj[(size_t)u * DD + k];
                if (col[v] == -1) { col[v] = 1 - col[u]; st[sp++] = v; }
                else if (col[v] == col[u]) { bip = 0; break; }
            }
        }
    }
    if (!bip) { printf("0 0\n"); return 0; }

    for (int e = 0; e < m0; e++) {
        if (col[eu[e]] == 0) { eA[e] = eu[e]; eB[e] = ev[e]; }
        else { eA[e] = ev[e]; eB[e] = eu[e]; }
    }
    N = n0;
    NEDGE = m0;
    rebuild_adj();
    if (cost_fn() != 0) { printf("0 0\n"); return 0; }

    bestN = N;
    bestNE = NEDGE;
    memcpy(bA, eA, sizeof(int) * (size_t)NEDGE);
    memcpy(bB, eB, sizeof(int) * (size_t)NEDGE);

    /* Growth and repair loop. Each attempt restores the best state first. */
    while (elapsed_s() < SLICE) {
        if (N + 2 > NCAP) break;
        N = bestN;
        NEDGE = bestNE;
        memcpy(eA, bA, sizeof(int) * (size_t)NEDGE);
        memcpy(eB, bB, sizeof(int) * (size_t)NEDGE);
        if (!grow()) continue;
        long long c = anneal(12000, 2.0);
        if (c == 0) {
            bestN = N;
            bestNE = NEDGE;
            memcpy(bA, eA, sizeof(int) * (size_t)NEDGE);
            memcpy(bB, eB, sizeof(int) * (size_t)NEDGE);
        }
    }

    printf("%d %d\n", bestN, bestNE);
    for (int e = 0; e < bestNE; e++) printf("%d %d\n", bA[e], bB[e]);
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
# Group sampling for the lift phase.
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


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.9 * time_limit, time_limit - 4.0))
    deadline = start + budget
    lift_deadline = start + 0.55 * budget
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

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Phase 1: lift search for a large regular starting graph.
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
                C_SOURCE,
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

    # Phase 2: grow the best regular graph by vertex pairs and repair by annealing.
    # This replaces the lift family with a direct search on general bipartite graphs.
    rem = deadline - time.monotonic()
    if rem >= 2.0 and best[0] > 0:
        slice_s = rem - 1.0
        try:
            out = lib.run_c(
                REPAIR_SOURCE,
                [d, D, rng.randrange(1, 10 ** 9), f"{slice_s:.2f}"],
                stdin_graph=best,
                timeout=slice_s + 10.0,
            )
            n2, e2 = lib.parse_graph_text(out)
            consider(n2, e2)
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
