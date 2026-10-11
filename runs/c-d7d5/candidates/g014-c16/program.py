import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Strategy
#   1. Lift phase: simulated annealing over voltages of bi-Cayley lifts
#      (C engine LIFT_SOURCE), as before, for a fraction of the budget.
#   2. Repair/growth phase (new): take the best valid graph and grow it by
#      adding a bipartite vertex pair (x in A, y in B) that takes over d
#      matching edges, keeping every degree <= d and the graph bipartite.
#      Then simulated annealing over 2-switches (a1-b1, a2-b2 -> a1-b2,
#      a2-b1), which preserve degrees and bipartiteness, minimises the number
#      of vertex pairs at distance > D. A success is accepted only at cost 0,
#      and the engine always prints the last valid checkpoint.
#   Python keeps the largest graph that passes lib.is_valid, so the lift
#   result is always the fallback.
# ----------------------------------------------------------------------------

LIFT_SOURCE = r"""
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


REPAIR_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXADD 800
#define START_STEPS 200000
#define STEPS 5000

static int DEG, DIAM, N, CAP, M, MCAP, WC;
static int *ea, *eb, *adj, *dg, *side;
static uint64_t *ra, *rb;
static int *sadj, *sdg, *sside, *sea, *seb;
static int sN, sM, have_best = 0;
static uint64_t rs = 88172645463325252ULL;
static clock_t T_START;
static double SLICE;

static inline uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static inline int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static inline double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double elapsed(void) { return (double)(clock() - T_START) / (double)CLOCKS_PER_SEC; }

static int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int a, int b) {
    const int *p = adj + (size_t)a * DEG;
    for (int t = 0; t < dg[a]; t++) if (p[t] == b) return 1;
    return 0;
}

static void replace_nb(int v, int old, int nw) {
    int *p = adj + (size_t)v * DEG;
    for (int t = 0; t < dg[v]; t++) {
        if (p[t] == old) { p[t] = nw; return; }
    }
    fprintf(stderr, "internal: missing neighbour\n");
    exit(2);
}

/* Exchange partners of edges i = (a1,b1) and j = (a2,b2) -> (a1,b2), (a2,b1). No checks. */
static void swap_raw(int i, int j) {
    int a1 = ea[i], b1 = eb[i], a2 = ea[j], b2 = eb[j];
    replace_nb(a1, b1, b2);
    replace_nb(b1, a1, a2);
    replace_nb(a2, b2, b1);
    replace_nb(b2, a2, a1);
    eb[i] = b2;
    eb[j] = b1;
}

/* Checked 2-switch: keeps degrees and bipartiteness, rejects duplicates. */
static int try_switch(int i, int j) {
    int a1 = ea[i], b1 = eb[i], a2 = ea[j], b2 = eb[j];
    if (a1 == a2 || b1 == b2) return 0;
    if (has_edge(a1, b2) || has_edge(a2, b1)) return 0;
    swap_raw(i, j);
    return 1;
}

/* Number of unordered pairs at distance > DIAM (bitset balls). */
static long long bad_pairs(void) {
    int W = (N + 63) >> 6;
    uint64_t *cur = ra, *nxt = rb;
    for (int v = 0; v < N; v++) {
        uint64_t *s = cur + (size_t)v * WC;
        for (int w = 0; w < W; w++) s[w] = 0;
        s[v >> 6] |= 1ULL << (v & 63);
    }
    for (int lv = 0; lv < DIAM; lv++) {
        for (int v = 0; v < N; v++) {
            uint64_t *o = nxt + (size_t)v * WC;
            const uint64_t *s = cur + (size_t)v * WC;
            for (int w = 0; w < W; w++) o[w] = s[w];
            const int *p = adj + (size_t)v * DEG;
            for (int t = 0; t < dg[v]; t++) {
                const uint64_t *su = cur + (size_t)p[t] * WC;
                for (int w = 0; w < W; w++) o[w] |= su[w];
            }
        }
        uint64_t *tmp = cur; cur = nxt; nxt = tmp;
    }
    long long tot = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        const uint64_t *s = cur + (size_t)v * WC;
        for (int w = 0; w < W; w++) c += popc64(s[w]);
        tot += N - c;
    }
    return tot / 2;
}

/* Add a bipartite pair x (side A), y (side B). Each of DEG matching edges (a_k,b_k)
   becomes (a_k,y), and a new edge (x,b_k) is added, so x and y get degree DEG. */
static int insert_pair(void) {
    if (N + 2 > CAP || M < DEG || M + DEG > MCAP) return 0;
    int chosen[64];
    int ok = 0;
    for (int att = 0; att < 20000 && !ok; att++) {
        int k;
        for (k = 0; k < DEG; k++) {
            int e = rndint(M);
            int bad = 0;
            for (int q = 0; q < k; q++) {
                if (chosen[q] == e || ea[chosen[q]] == ea[e] || eb[chosen[q]] == eb[e]) { bad = 1; break; }
            }
            if (bad) break;
            chosen[k] = e;
        }
        if (k == DEG) ok = 1;
    }
    if (!ok) return 0;
    int x = N, y = N + 1;
    side[x] = 0; side[y] = 1;
    dg[x] = 0; dg[y] = 0;
    N += 2;
    for (int k = 0; k < DEG; k++) {
        int e = chosen[k];
        int a = ea[e], b = eb[e];
        replace_nb(a, b, y);
        replace_nb(b, a, x);
        adj[(size_t)x * DEG + dg[x]++] = b;
        adj[(size_t)y * DEG + dg[y]++] = a;
        eb[e] = y;
        ea[M + k] = x;
        eb[M + k] = b;
    }
    M += DEG;
    return 1;
}

static void save_state(void) {
    memcpy(sadj, adj, sizeof(int) * (size_t)N * DEG);
    memcpy(sdg, dg, sizeof(int) * (size_t)N);
    memcpy(sside, side, sizeof(int) * (size_t)N);
    memcpy(sea, ea, sizeof(int) * (size_t)M);
    memcpy(seb, eb, sizeof(int) * (size_t)M);
    sN = N;
    sM = M;
    have_best = 1;
}

static void restore_state(void) {
    memcpy(adj, sadj, sizeof(int) * (size_t)sN * DEG);
    memcpy(dg, sdg, sizeof(int) * (size_t)sN);
    memcpy(side, sside, sizeof(int) * (size_t)sN);
    memcpy(ea, sea, sizeof(int) * (size_t)sM);
    memcpy(eb, seb, sizeof(int) * (size_t)sM);
    N = sN;
    M = sM;
}

/* Simulated annealing over 2-switches; returns 1 when cost reaches 0.
   On a timeout returns 0 (the caller restores its checkpoint). */
static int anneal(int steps, double T0, double T1) {
    if (M < 2) return 0;
    long long cur = bad_pairs();
    if (cur == 0) return 1;
    for (int it = 0; it < steps; it++) {
        if ((it & 31) == 0 && elapsed() >= SLICE) return 0;
        double T = T0 + (T1 - T0) * (double)it / (double)steps;
        int i = rndint(M), j = rndint(M);
        if (i == j) continue;
        if (!try_switch(i, j)) continue;
        long long nc = bad_pairs();
        if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
            cur = nc;
            if (cur == 0) return 1;
        } else {
            swap_raw(i, j);
        }
    }
    return cur == 0;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed slice\n");
        return 1;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t seed = strtoull(argv[3], NULL, 10);
    SLICE = atof(argv[4]);
    rs = seed * 0x9E3779B97F4A7C15ULL ^ 0xABCDEF123ULL;
    if (rs == 0) rs = 1;
    T_START = clock();

    if (DEG < 1 || DIAM < 1) { printf("0 0\n"); return 0; }

    int n, m;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || m < 0 || n > 200000) {
        printf("0 0\n");
        return 0;
    }
    int *ru = malloc(sizeof(int) * (size_t)(m + 1));
    int *rv = malloc(sizeof(int) * (size_t)(m + 1));
    if (!ru || !rv) { printf("0 0\n"); return 0; }
    for (int i = 0; i < m; i++) {
        if (scanf("%d %d", &ru[i], &rv[i]) != 2) { printf("0 0\n"); return 0; }
        if (ru[i] < 0 || ru[i] >= n || rv[i] < 0 || rv[i] >= n || ru[i] == rv[i]) {
            printf("0 0\n");
            return 0;
        }
    }

    CAP = n + 2 * MAXADD;
    MCAP = m + DEG * MAXADD + DEG;
    WC = (CAP + 63) >> 6;
    ea = malloc(sizeof(int) * (size_t)MCAP);
    eb = malloc(sizeof(int) * (size_t)MCAP);
    adj = calloc((size_t)CAP * DEG, sizeof(int));
    dg = calloc((size_t)CAP, sizeof(int));
    side = calloc((size_t)CAP, sizeof(int));
    ra = calloc((size_t)CAP * WC, sizeof(uint64_t));
    rb = calloc((size_t)CAP * WC, sizeof(uint64_t));
    sadj = calloc((size_t)CAP * DEG, sizeof(int));
    sdg = calloc((size_t)CAP, sizeof(int));
    sside = calloc((size_t)CAP, sizeof(int));
    sea = malloc(sizeof(int) * (size_t)MCAP);
    seb = malloc(sizeof(int) * (size_t)MCAP);
    int *stk = malloc(sizeof(int) * (size_t)(n + 1));
    if (!ea || !eb || !adj || !dg || !side || !ra || !rb || !sadj || !sdg || !sside || !sea || !seb || !stk) {
        printf("0 0\n");
        return 0;
    }

    N = n;
    M = 0;
    for (int i = 0; i < m; i++) {
        int u = ru[i], v = rv[i];
        if (dg[u] >= DEG || dg[v] >= DEG || has_edge(u, v)) { printf("0 0\n"); return 0; }
        adj[(size_t)u * DEG + dg[u]++] = v;
        adj[(size_t)v * DEG + dg[v]++] = u;
    }

    /* Bipartition by BFS; reject odd cycles. */
    for (int v = 0; v < n; v++) side[v] = -1;
    for (int s = 0; s < n; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int sp = 0;
        stk[sp++] = s;
        while (sp) {
            int u = stk[--sp];
            for (int t = 0; t < dg[u]; t++) {
                int w = adj[(size_t)u * DEG + t];
                if (side[w] < 0) {
                    side[w] = 1 - side[u];
                    stk[sp++] = w;
                } else if (side[w] == side[u]) {
                    printf("0 0\n");
                    return 0;
                }
            }
        }
    }
    for (int i = 0; i < m; i++) {
        int u = ru[i], v = rv[i];
        if (side[u] == 0) { ea[i] = u; eb[i] = v; }
        else { ea[i] = v; eb[i] = u; }
    }
    M = m;

    if (bad_pairs() == 0) save_state();
    while (!have_best && elapsed() < SLICE) {
        if (anneal(START_STEPS, 1.5, 0.15)) save_state();
    }

    while (have_best && elapsed() < SLICE) {
        if (!insert_pair()) break;
        if (anneal(STEPS, 1.0, 0.1)) save_state();
        else restore_state();
    }

    if (have_best) {
        printf("%d %d\n", sN, sM);
        for (int i = 0; i < sM; i++) printf("%d %d\n", sea[i], seb[i]);
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
# Group sampling for the lift phase.
# ----------------------------------------------------------------------------

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


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget
    lift_deadline = start + 0.35 * budget
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

    if D >= 4 and time.monotonic() < lift_deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Phase 1: lift search (voltage annealing over bi-Cayley lifts).
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
                LIFT_SOURCE,
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

    # Phase 2: grow the best valid graph by vertex-pair insertion plus 2-switch annealing.
    rem = deadline - time.monotonic()
    if rem > 3.0:
        try:
            out = lib.run_c(
                REPAIR_SOURCE,
                [d, D, rng.randrange(1, 10 ** 9), f"{rem - 1.5:.2f}"],
                stdin_graph=best,
                timeout=rem + 8.0,
            )
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
