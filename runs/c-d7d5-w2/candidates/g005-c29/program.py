import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Engine C (new): fixed-vertex-set rewiring annealer on an arbitrary bipartite
# graph with max degree DEG and diameter DIAM.
#
# Input: a valid bipartite graph on n0 vertices (stdin, "n m" + edges) and a
# target order NT >= n0 (NT - n0 new vertices are added, alternating sides).
# Moves keep every degree <= DEG and every edge between the two sides:
#   rewire: move one endpoint of an edge to another vertex with spare degree;
#   swap:   2-switch (a1 b1, a2 b2) -> (a1 b2, a2 b1), degrees unchanged.
# After every move, every possible edge between spare-degree vertices is added
# (adding edges never increases the number of bad pairs).
# Cost = number of ordered pairs at distance > DIAM, computed with bitset
# ball expansion. Simulated annealing with periodic reloads of the best state.
#
# Usage: prog DEG DIAM NT seed slice_seconds
# Prints a valid graph ("n m" + edges) or "0 0".
# ----------------------------------------------------------------------------

REWIRE_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 4000

static int DEG, DIAM, N, NE, MAXE, W, n0s, n1s;
static int *deg, *ea, *eb, *sa, *sb, *ba, *bb, *nbr, *cnt, *list0, *list1, *tA, *tB;
static unsigned char *A;
static uint64_t *R1, *R2;
static int snapNE, bestNE;
static uint64_t rs = 88172645463325252ULL;

static inline uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static inline int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static inline double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double elapsed(clock_t t0) { return (double)(clock() - t0) / (double)CLOCKS_PER_SEC; }

static int popc(uint64_t x) {
    int c = 0;
    while (x) { x &= x - 1; c++; }
    return c;
}

static inline size_t AI(int a, int b) { return (size_t)a * (size_t)N + (size_t)b; }

static void add_edge(int a, int b) {
    ea[NE] = a; eb[NE] = b; NE++;
    A[AI(a, b)] = 1; A[AI(b, a)] = 1;
    deg[a]++; deg[b]++;
}

static void del_edge(int e) {
    int a = ea[e], b = eb[e];
    A[AI(a, b)] = 0; A[AI(b, a)] = 0;
    deg[a]--; deg[b]--;
    NE--;
    ea[e] = ea[NE]; eb[e] = eb[NE];
}

static void set_state(const int *xa, const int *xb, int m) {
    for (int e = 0; e < NE; e++) {
        A[AI(ea[e], eb[e])] = 0;
        A[AI(eb[e], ea[e])] = 0;
    }
    memset(deg, 0, sizeof(int) * (size_t)N);
    NE = 0;
    for (int e = 0; e < m; e++) add_edge(xa[e], xb[e]);
}

static void snapshot(void) {
    snapNE = NE;
    memcpy(sa, ea, sizeof(int) * (size_t)NE);
    memcpy(sb, eb, sizeof(int) * (size_t)NE);
}

static void save_best(void) {
    bestNE = NE;
    memcpy(ba, ea, sizeof(int) * (size_t)NE);
    memcpy(bb, eb, sizeof(int) * (size_t)NE);
}

/* Number of ordered pairs (u, v) with distance > DIAM (unreachable counts). */
static long long cost_fn(void) {
    for (int v = 0; v < N; v++) cnt[v] = 0;
    for (int e = 0; e < NE; e++) {
        int a = ea[e], b = eb[e];
        nbr[(size_t)a * DEG + cnt[a]++] = b;
        nbr[(size_t)b * DEG + cnt[b]++] = a;
    }
    uint64_t *cur = R1, *nxt = R2;
    for (int v = 0; v < N; v++) {
        uint64_t *row = cur + (size_t)v * W;
        memset(row, 0, sizeof(uint64_t) * (size_t)W);
        row[v >> 6] |= 1ULL << (v & 63);
    }
    for (int lv = 0; lv < DIAM; lv++) {
        for (int v = 0; v < N; v++) {
            uint64_t *out = nxt + (size_t)v * W;
            const uint64_t *in = cur + (size_t)v * W;
            memcpy(out, in, sizeof(uint64_t) * (size_t)W);
            for (int i = 0; i < cnt[v]; i++) {
                const uint64_t *src = cur + (size_t)nbr[(size_t)v * DEG + i] * W;
                for (int w = 0; w < W; w++) out[w] |= src[w];
            }
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
    }
    long long total = 0;
    for (int v = 0; v < N; v++) {
        const uint64_t *row = cur + (size_t)v * W;
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(row[w]);
        total += N - c;
    }
    return total;
}

/* Add edges between every pair of spare-degree vertices that are not adjacent. */
static void fill_pass(void) {
    int na = 0, nbd = 0;
    for (int i = 0; i < n0s; i++) if (deg[list0[i]] < DEG) tA[na++] = list0[i];
    for (int j = 0; j < n1s; j++) if (deg[list1[j]] < DEG) tB[nbd++] = list1[j];
    for (int i = 0; i < na; i++) {
        int a = tA[i];
        for (int j = 0; j < nbd && deg[a] < DEG; j++) {
            int b = tB[j];
            if (deg[b] < DEG && !A[AI(a, b)]) add_edge(a, b);
        }
    }
}

/* Move one endpoint of a random edge to a random vertex with spare degree. */
static int move_rewire(void) {
    if (NE == 0) return 0;
    int e = rndint(NE);
    int a = ea[e], b = eb[e];
    for (int t = 0; t < 8; t++) {
        if (rnd64() & 1) {
            int bp = list1[rndint(n1s)];
            if (bp == b || deg[bp] >= DEG || A[AI(a, bp)]) continue;
            del_edge(e);
            add_edge(a, bp);
            return 1;
        } else {
            int ap = list0[rndint(n0s)];
            if (ap == a || deg[ap] >= DEG || A[AI(ap, b)]) continue;
            del_edge(e);
            add_edge(ap, b);
            return 1;
        }
    }
    return 0;
}

/* 2-switch: (a1 b1), (a2 b2) -> (a1 b2), (a2 b1). Degrees unchanged. */
static int move_swap(void) {
    if (NE < 2) return 0;
    int e1 = rndint(NE), e2 = rndint(NE);
    if (e1 == e2) return 0;
    int a1 = ea[e1], b1 = eb[e1], a2 = ea[e2], b2 = eb[e2];
    if (a1 == a2 || b1 == b2) return 0;
    if (A[AI(a1, b2)] || A[AI(a2, b1)]) return 0;
    A[AI(a1, b1)] = 0; A[AI(b1, a1)] = 0;
    A[AI(a2, b2)] = 0; A[AI(b2, a2)] = 0;
    ea[e1] = a1; eb[e1] = b2;
    ea[e2] = a2; eb[e2] = b1;
    A[AI(a1, b2)] = 1; A[AI(b2, a1)] = 1;
    A[AI(a2, b1)] = 1; A[AI(b1, a2)] = 1;
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 6) { printf("0 0\n"); return 0; }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    int NT = atoi(argv[3]);
    uint64_t seed = strtoull(argv[4], NULL, 10);
    double slice = atof(argv[5]);
    rs = seed * 0x9E3779B97F4A7C15ULL ^ 0x5555AAAAULL;
    if (rs == 0) rs = 1;

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { printf("0 0\n"); return 0; }
    if (DEG < 1 || DIAM < 1 || NT < 2 || NT > MAXN || n0 < 0 || n0 > NT || m0 < 0) {
        printf("0 0\n");
        return 0;
    }
    int *iu = malloc(sizeof(int) * (size_t)(m0 + 1));
    int *iv = malloc(sizeof(int) * (size_t)(m0 + 1));
    int *col = malloc(sizeof(int) * (size_t)(NT + 1));
    if (!iu || !iv || !col) { printf("0 0\n"); return 0; }
    for (int e = 0; e < m0; e++) {
        if (scanf("%d %d", &iu[e], &iv[e]) != 2) { printf("0 0\n"); return 0; }
        if (iu[e] < 0 || iu[e] >= n0 || iv[e] < 0 || iv[e] >= n0 || iu[e] == iv[e]) {
            printf("0 0\n");
            return 0;
        }
    }

    /* 2-colour the input graph (per component, arbitrary root colour). */
    for (int v = 0; v < n0; v++) col[v] = -1;
    for (int s = 0; s < n0; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int changed = 1;
        while (changed) {
            changed = 0;
            for (int e = 0; e < m0; e++) {
                int u = iu[e], v = iv[e];
                if (col[u] >= 0 && col[v] < 0) { col[v] = 1 - col[u]; changed = 1; }
                else if (col[v] >= 0 && col[u] < 0) { col[u] = 1 - col[v]; changed = 1; }
            }
        }
    }
    for (int e = 0; e < m0; e++) {
        if (col[iu[e]] == col[iv[e]]) { printf("0 0\n"); return 0; }
    }

    N = NT;
    MAXE = N * DEG + 4;
    W = (N + 63) / 64;
    int *side = malloc(sizeof(int) * (size_t)N);
    list0 = malloc(sizeof(int) * (size_t)N);
    list1 = malloc(sizeof(int) * (size_t)N);
    tA = malloc(sizeof(int) * (size_t)N);
    tB = malloc(sizeof(int) * (size_t)N);
    deg = calloc((size_t)N, sizeof(int));
    cnt = calloc((size_t)N, sizeof(int));
    nbr = malloc(sizeof(int) * (size_t)N * DEG);
    ea = malloc(sizeof(int) * (size_t)MAXE);
    eb = malloc(sizeof(int) * (size_t)MAXE);
    sa = malloc(sizeof(int) * (size_t)MAXE);
    sb = malloc(sizeof(int) * (size_t)MAXE);
    ba = malloc(sizeof(int) * (size_t)MAXE);
    bb = malloc(sizeof(int) * (size_t)MAXE);
    A = calloc((size_t)N * (size_t)N, 1);
    R1 = calloc((size_t)N * W, sizeof(uint64_t));
    R2 = calloc((size_t)N * W, sizeof(uint64_t));
    if (!side || !list0 || !list1 || !tA || !tB || !deg || !cnt || !nbr || !ea || !eb ||
        !sa || !sb || !ba || !bb || !A || !R1 || !R2) {
        printf("0 0\n");
        return 0;
    }

    n0s = 0; n1s = 0;
    for (int v = 0; v < N; v++) {
        side[v] = (v < n0) ? col[v] : ((v - n0) & 1);
        if (side[v] == 0) list0[n0s++] = v; else list1[n1s++] = v;
    }
    if (n0s == 0 || n1s == 0) { printf("0 0\n"); return 0; }

    NE = 0;
    for (int e = 0; e < m0; e++) {
        int u = iu[e], v = iv[e];
        int a, b;
        if (side[u] == 0) { a = u; b = v; } else { a = v; b = u; }
        if (side[a] != 0 || side[b] != 1) { printf("0 0\n"); return 0; }
        if (deg[a] >= DEG || deg[b] >= DEG || A[AI(a, b)]) { printf("0 0\n"); return 0; }
        add_edge(a, b);
    }

    fill_pass();
    long long cur = cost_fn();
    long long best = cur;
    save_best();

    clock_t t0 = clock();
    const int RL = 2000;
    const double Tmax = 1.5, Tmin = 0.05;
    long long it = 0;
    while (cur > 0 && elapsed(t0) < slice) {
        if (it > 0 && it % RL == 0 && cur > best) {
            set_state(ba, bb, bestNE);
            cur = best;
        }
        double phase = (double)(it % RL) / (double)RL;
        double T = Tmax * pow(Tmin / Tmax, phase);
        snapshot();
        int moved = (rnd64() & 1) ? move_rewire() : move_swap();
        if (moved) {
            fill_pass();
            long long nc = cost_fn();
            if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
                cur = nc;
                if (cur < best) { best = cur; save_best(); }
            } else {
                set_state(sa, sb, snapNE);
            }
        }
        it++;
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
# Engine B: voltage annealing of general bi-Cayley lifts with K base vertices
# per side (the baseline lift engine).
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
# Group sampling for the lift engine.
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


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 5.0))
    lift_end = start + 0.30 * budget
    rewire_end = start + 0.80 * budget
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

    # Phase B: general lift annealing (baseline).
    while True:
        remaining = lift_end - time.monotonic()
        if remaining < 1.0:
            break
        slice_s = min(remaining, 10.0)
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

    # Phase C: grow the best graph by two vertices at a time with the rewiring
    # annealer. Each run starts from the current best and must reach a valid
    # graph on best + 2 vertices within its slice.
    while True:
        remaining = rewire_end - time.monotonic()
        if remaining < 2.0:
            break
        n0, e0 = best
        target = n0 + 2
        slice_s = min(remaining, 15.0)
        try:
            out = lib.run_c(
                REWIRE_SOURCE,
                [d, D, target, rng.randrange(1, 10 ** 9), f"{slice_s:.2f}"],
                stdin_graph=(n0, e0),
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
