import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Engine 1 (lift search): simulated annealing over the voltages of a bi-Cayley
# lift over Z_m x|_r Z_k2 (element (a, b) coded as a*k2 + b). Same engine as
# before. It supplies the starting graph.
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
# Engine 2 (graph-level growth and repair): a different construction.
#
# The lift is regular, so it has no spare degree to grow into. Instead, this
# engine works on the explicit graph:
#   1. Insert a new pair (a in A, b in B). Remove a matching of 2(d-1) edges
#      and reconnect their endpoints: a takes d-1 freed B-endpoints, b takes
#      d-1 freed A-endpoints, and the remaining d-1 freed A and B endpoints
#      are paired with each other. Degrees stay <= d and the edge count grows by d.
#   2. Anneal with degree-preserving double-edge swaps to minimise the number
#      of vertex pairs at distance > D. The cost is computed exactly with
#      bitset ball expansion.
#   3. Keep the grown graph only if the cost reaches zero. Otherwise restore
#      the last valid state.
# The output is always a valid graph (the input graph at worst).
#
# Usage: prog d D seed slice_seconds      (graph on stdin, "0 0" = none)
# ----------------------------------------------------------------------------

C_REPAIR = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define STEP_S 2.5

static int DEG, DIAM, N, CAP, NA;
static int *deg, *adj, *Alist;
static uint64_t *bufX, *bufY;
static int *bk_adj, *bk_deg, *bk_Alist;
static int bk_N, bk_NA;
static uint64_t rs = 88172645463325252ULL;
static clock_t T_START;

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

static int adjacent(int a, int b) {
    const int *p = adj + (size_t)a * DEG;
    for (int t = 0; t < deg[a]; t++) if (p[t] == b) return 1;
    return 0;
}

static void replace_nb(int v, int old, int nw) {
    int *p = adj + (size_t)v * DEG;
    for (int t = 0; t < deg[v]; t++) if (p[t] == old) { p[t] = nw; return; }
}

static void add_nb(int v, int u) {
    adj[(size_t)v * DEG + deg[v]] = u;
    deg[v]++;
}

static void rem_nb(int v, int u) {
    int *p = adj + (size_t)v * DEG;
    for (int t = 0; t < deg[v]; t++) {
        if (p[t] == u) {
            p[t] = p[deg[v] - 1];
            deg[v]--;
            return;
        }
    }
}

static void shuffle_arr(int *a, int n) {
    for (int i = n - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = a[i]; a[i] = a[j]; a[j] = t;
    }
}

/* Total number of unordered vertex pairs at distance > DIAM (unreachable included). */
static int eval_cost(void) {
    int W = (N + 63) / 64;
    uint64_t *X = bufX, *Y = bufY;
    memset(X, 0, sizeof(uint64_t) * (size_t)N * W);
    for (int v = 0; v < N; v++) X[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int lv = 0; lv < DIAM; lv++) {
        for (int v = 0; v < N; v++) {
            uint64_t *y = Y + (size_t)v * W;
            const uint64_t *x = X + (size_t)v * W;
            memcpy(y, x, sizeof(uint64_t) * (size_t)W);
            const int *p = adj + (size_t)v * DEG;
            for (int t = 0; t < deg[v]; t++) {
                const uint64_t *xu = X + (size_t)p[t] * W;
                for (int w = 0; w < W; w++) y[w] |= xu[w];
            }
        }
        uint64_t *tmp = X; X = Y; Y = tmp;
    }
    long long total = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        const uint64_t *x = X + (size_t)v * W;
        for (int w = 0; w < W; w++) c += popc64(x[w]);
        total += N - c;
    }
    return (int)(total / 2);
}

/* Insert a new pair (new A vertex na, new B vertex nb). Returns 0 with the state unchanged on failure. */
static int insert_pair(void) {
    if (DEG < 2) return 0;
    int r = 2 * (DEG - 1), k = DEG - 1;
    if (r > 64 || N + 2 > CAP || NA < 1) return 0;
    int oa[64], ob[64], xa[64], yb[64];
    int got = 0, tries = 0;
    while (got < r && tries < 4000) {
        tries++;
        int a = Alist[rndint(NA)];
        if (deg[a] == 0) continue;
        int b = adj[(size_t)a * DEG + rndint(deg[a])];
        int dup = 0;
        for (int i = 0; i < got; i++) {
            if (oa[i] == a || ob[i] == b) { dup = 1; break; }
        }
        if (dup) continue;
        oa[got] = a; ob[got] = b; got++;
    }
    if (got < r) return 0;

    for (int i = 0; i < r; i++) { rem_nb(oa[i], ob[i]); rem_nb(ob[i], oa[i]); }
    memcpy(xa, oa, sizeof(int) * (size_t)r);
    memcpy(yb, ob, sizeof(int) * (size_t)r);
    shuffle_arr(xa, r);
    shuffle_arr(yb, r);
    int *FA2 = xa + k;   /* the d-1 A-endpoints that get re-paired */
    int *FB2 = yb + k;   /* the d-1 B-endpoints that get re-paired */

    int ok = 0;
    for (int tr = 0; tr < 60 && !ok; tr++) {
        shuffle_arr(FB2, k);
        ok = 1;
        for (int i = 0; i < k; i++) {
            if (adjacent(FA2[i], FB2[i])) { ok = 0; break; }
        }
    }
    if (!ok) {
        for (int i = 0; i < r; i++) { add_nb(oa[i], ob[i]); add_nb(ob[i], oa[i]); }
        return 0;
    }

    int na = N, nb = N + 1;
    deg[na] = 0;
    deg[nb] = 0;
    Alist[NA++] = na;
    N += 2;
    add_nb(na, nb);
    add_nb(nb, na);
    for (int i = 0; i < k; i++) { add_nb(na, yb[i]); add_nb(yb[i], na); }
    for (int i = 0; i < k; i++) { add_nb(nb, xa[i]); add_nb(xa[i], nb); }
    for (int i = 0; i < k; i++) { add_nb(FA2[i], FB2[i]); add_nb(FB2[i], FA2[i]); }
    return 1;
}

/* Annealing with degree-preserving double-edge swaps. Returns 1 as soon as the cost is 0. */
static int anneal(double budget) {
    int cur = eval_cost();
    if (cur == 0) return 1;
    double ts = elapsed();
    double T0 = 1.0 + 0.05 * cur;
    for (;;) {
        double el = elapsed();
        if (el - ts >= budget) break;
        double frac = (el - ts) / budget;
        double T = T0 * (1.0 - frac) + 0.05;

        int a1 = Alist[rndint(NA)];
        int a2 = Alist[rndint(NA)];
        if (a1 == a2 || deg[a1] == 0 || deg[a2] == 0) continue;
        int b1 = adj[(size_t)a1 * DEG + rndint(deg[a1])];
        int b2 = adj[(size_t)a2 * DEG + rndint(deg[a2])];
        if (b1 == b2) continue;
        if (adjacent(a1, b2) || adjacent(a2, b1)) continue;

        replace_nb(a1, b1, b2);
        replace_nb(b1, a1, a2);
        replace_nb(a2, b2, b1);
        replace_nb(b2, a2, a1);
        int nc = eval_cost();
        if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
            cur = nc;
            if (cur == 0) return 1;
        } else {
            replace_nb(a1, b2, b1);
            replace_nb(b2, a1, a2);
            replace_nb(a2, b1, b2);
            replace_nb(b1, a2, a1);
        }
    }
    return 0;
}

static void save_state(void) {
    memcpy(bk_adj, adj, sizeof(int) * (size_t)CAP * DEG);
    memcpy(bk_deg, deg, sizeof(int) * (size_t)CAP);
    memcpy(bk_Alist, Alist, sizeof(int) * (size_t)CAP);
    bk_N = N;
    bk_NA = NA;
}

static void load_state(void) {
    memcpy(adj, bk_adj, sizeof(int) * (size_t)CAP * DEG);
    memcpy(deg, bk_deg, sizeof(int) * (size_t)CAP);
    memcpy(Alist, bk_Alist, sizeof(int) * (size_t)CAP);
    N = bk_N;
    NA = bk_NA;
}

#define FAIL() do { printf("0 0\n"); return 0; } while (0)

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t seed = strtoull(argv[3], NULL, 10);
    double slice = atof(argv[4]);
    if (DEG < 1 || DIAM < 1) FAIL();
    rs = seed * 0x9E3779B97F4A7C15ULL ^ 0x5DEECE66DULL;
    if (rs == 0) rs = 1;
    T_START = clock();

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || m < 0) FAIL();
    int *eu = malloc(sizeof(int) * (size_t)(m + 1));
    int *ev = malloc(sizeof(int) * (size_t)(m + 1));
    if (!eu || !ev) FAIL();
    for (int i = 0; i < m; i++) {
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) FAIL();
        if (eu[i] < 0 || ev[i] < 0 || eu[i] >= n || ev[i] >= n || eu[i] == ev[i]) FAIL();
    }

    CAP = n + 600;
    int WCAP = (CAP + 63) / 64;
    deg = calloc((size_t)CAP, sizeof(int));
    adj = calloc((size_t)CAP * DEG, sizeof(int));
    Alist = calloc((size_t)CAP, sizeof(int));
    bufX = calloc((size_t)CAP * WCAP, sizeof(uint64_t));
    bufY = calloc((size_t)CAP * WCAP, sizeof(uint64_t));
    bk_adj = calloc((size_t)CAP * DEG, sizeof(int));
    bk_deg = calloc((size_t)CAP, sizeof(int));
    bk_Alist = calloc((size_t)CAP, sizeof(int));
    int *col = malloc(sizeof(int) * (size_t)n);
    int *qu = malloc(sizeof(int) * (size_t)n);
    if (!deg || !adj || !Alist || !bufX || !bufY || !bk_adj || !bk_deg || !bk_Alist || !col || !qu) FAIL();

    for (int i = 0; i < m; i++) {
        int u = eu[i], v = ev[i];
        if (deg[u] >= DEG || deg[v] >= DEG || adjacent(u, v)) FAIL();
        add_nb(u, v);
        add_nb(v, u);
    }

    for (int i = 0; i < n; i++) col[i] = -1;
    for (int s = 0; s < n; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int h = 0, t = 0;
        qu[t++] = s;
        while (h < t) {
            int u = qu[h++];
            for (int k = 0; k < deg[u]; k++) {
                int v = adj[(size_t)u * DEG + k];
                if (col[v] < 0) { col[v] = 1 - col[u]; qu[t++] = v; }
                else if (col[v] == col[u]) FAIL();
            }
        }
    }
    N = n;
    NA = 0;
    for (int v = 0; v < n; v++) if (col[v] == 0) Alist[NA++] = v;
    if (NA < 1) FAIL();

    int ok = (eval_cost() == 0) ? 1 : anneal(0.3 * slice);
    if (!ok) FAIL();

    int fails = 0;
    while (elapsed() < slice) {
        double rem = slice - elapsed();
        if (rem < 0.3) break;
        save_state();
        if (!insert_pair()) {
            fails++;
            if (fails > 500) break;
            continue;
        }
        double bud = rem < STEP_S ? rem : STEP_S;
        if (!anneal(bud)) load_state();
    }

    long long me = 0;
    for (int i = 0; i < NA; i++) me += deg[Alist[i]];
    printf("%d %lld\n", N, me);
    for (int i = 0; i < NA; i++) {
        int a = Alist[i];
        for (int t = 0; t < deg[a]; t++) {
            printf("%d %d\n", a, adj[(size_t)a * DEG + t]);
        }
    }
    fflush(stdout);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact / safe constructions.
# ----------------------------------------------------------------------------

LIFT_FRAC = 0.5  # share of the search budget given to the lift engine


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
# Greedy spare-degree extension (Python fallback, used only at the end).
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
        r = 1  # r = 1 is the direct product, always valid
        if k2 > 1 and m > 2:
            cands = [c for c in range(2, m) if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m]
            if cands:
                r = rng.choice(cands)
        return m, k2, r
    return None


def _repair_phase(d, D, best, seed, seconds):
    """Grow and repair the best graph with the graph-level engine. Returns a valid (n, edges)."""
    if seconds < 2.0:
        return best
    try:
        out = lib.run_c(C_REPAIR, [d, D, seed, f"{seconds:.2f}"],
                        stdin_graph=best, timeout=seconds + 3.0)
        n, e = lib.parse_graph_text(out)
    except (RuntimeError, ValueError):
        return best
    if n > best[0] and lib.is_valid(n, e, d, D):
        return (n, e)
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.9 * time_limit, time_limit - 4.0))
    deadline = start + budget
    lift_deadline = start + LIFT_FRAC * budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        """Adopt (n, e) if it is larger and valid. Returns True when the best improved."""
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

    # Phase 1: lift search for a large regular bi-Cayley graph.
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

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))

    # Phase 2: graph-level growth and repair from the best graph found so far.
    rem = deadline - time.monotonic()
    best = _repair_phase(d, D, best, rng.randrange(1, 10 ** 9), rem - 0.5)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))

    # Spare-degree extension (cheap, only if time remains).
    try:
        n2, e2 = _extend_spare(best[0], best[1], d, D, deadline)
        if n2 > best[0] and lib.is_valid(n2, e2, d, D):
            best = (n2, e2)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
