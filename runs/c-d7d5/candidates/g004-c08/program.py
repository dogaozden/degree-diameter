import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Phase 1 engine (structured start): simulated annealing over the voltages of a
# bi-Cayley lift over Z_m x|_r Z_k2. Element (a, b) is coded as a*k2 + b.
# Usage: prog d D K m k2 r seed slice_seconds
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
# Phase 2 engine (bold, unstructured): vertex insertion plus edge-switch
# annealing on bipartite graphs.
#
# Input: a valid graph on stdin ("n m" + edges), or "0 0" to start from a
# circulant d-regular bipartite graph on `target` vertices.
# Insert: a new pair (a in side 0, b in side 1) takes d removed edges (x, y)
# as (a, y) and (x, b), so degrees stay <= d and the graph stays bipartite.
# Anneal: double-edge switches (x1,y1),(x2,y2) -> (x1,y2),(x2,y1), which keep
# degrees and bipartiteness. Cost = unordered pairs at distance > D, computed
# with bitsets. A success is recorded and the graph keeps growing. A failure
# restores the last valid graph.
#
# Usage: prog d D seed slice_seconds iters target
# Prints the largest valid graph found ("n m" + edges), or "0 0".
# ----------------------------------------------------------------------------

C_GROW = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXINS 1500

static int DEG, DIAM, N, NE, NCAP, WCAP;
static int *adj, *cnt, *eu, *ev, *seu, *sev;
static int sN, sNE;
static uint64_t *RA, *RB;
static double TLIM;
static uint64_t rs = 88172645463325252ULL;

static inline uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static inline int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static inline double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double now_s(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Number of unordered pairs at distance > DIAM. */
static int bad_cost(void) {
    int W = (N + 63) >> 6;
    uint64_t *A = RA, *B = RB;
    memset(A, 0, sizeof(uint64_t) * (size_t)N * (size_t)W);
    for (int v = 0; v < N; v++) A[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int r = 0; r < DIAM; r++) {
        for (int v = 0; v < N; v++) {
            uint64_t *bv = B + (size_t)v * W;
            const uint64_t *av = A + (size_t)v * W;
            memcpy(bv, av, sizeof(uint64_t) * (size_t)W);
            const int *nb = adj + (size_t)v * DEG;
            for (int k = 0; k < cnt[v]; k++) {
                const uint64_t *au = A + (size_t)nb[k] * W;
                for (int w = 0; w < W; w++) bv[w] |= au[w];
            }
        }
        uint64_t *t = A; A = B; B = t;
    }
    long long miss = 0;
    for (int v = 0; v < N; v++) {
        const uint64_t *av = A + (size_t)v * W;
        int c = 0;
        for (int w = 0; w < W; w++) c += popc64(av[w]);
        miss += N - c;
    }
    return (int)(miss / 2);
}

static int has_edge(int u, int v) {
    const int *p = adj + (size_t)u * DEG;
    for (int k = 0; k < cnt[u]; k++) if (p[k] == v) return 1;
    return 0;
}

static void repl(int u, int old, int nw) {
    int *p = adj + (size_t)u * DEG;
    for (int k = 0; k < cnt[u]; k++) {
        if (p[k] == old) { p[k] = nw; return; }
    }
}

static void push(int u, int x) {
    adj[(size_t)u * DEG + cnt[u]++] = x;
}

/* Edge e1 = (a,b), e2 = (c,d2) becomes (a,d2), (c,b). Applying it twice undoes it. */
static void do_swap(int e1, int e2) {
    int a = eu[e1], b = ev[e1], c = eu[e2], d2 = ev[e2];
    ev[e1] = d2;
    ev[e2] = b;
    repl(a, b, d2);
    repl(b, a, c);
    repl(c, d2, b);
    repl(d2, c, a);
}

static int build_adj(void) {
    memset(cnt, 0, sizeof(int) * (size_t)N);
    for (int e = 0; e < NE; e++) {
        int u = eu[e], v = ev[e];
        if (cnt[u] >= DEG || cnt[v] >= DEG) return 0;
        if (has_edge(u, v)) return 0;
        push(u, v);
        push(v, u);
    }
    return 1;
}

static void snapshot(void) {
    sN = N;
    sNE = NE;
    memcpy(seu, eu, sizeof(int) * (size_t)NE);
    memcpy(sev, ev, sizeof(int) * (size_t)NE);
}

static void restore(void) {
    N = sN;
    NE = sNE;
    memcpy(eu, seu, sizeof(int) * (size_t)NE);
    memcpy(ev, sev, sizeof(int) * (size_t)NE);
    build_adj();
}

/* Anneal on the switch moves. Returns 0 as soon as the cost is 0, else the final cost. */
static int anneal(long iters, double T0) {
    int cur = bad_cost();
    if (cur == 0) return 0;
    for (long it = 0; it < iters; it++) {
        if ((it & 63) == 0 && now_s() >= TLIM) break;
        double T = T0 * (1.0 - (double)it / (double)iters) + 0.05;
        int e1 = rndint(NE), e2 = rndint(NE);
        if (e1 == e2) continue;
        int a = eu[e1], b = ev[e1], c = eu[e2], d2 = ev[e2];
        if (a == c || b == d2) continue;
        if (has_edge(a, d2) || has_edge(c, b)) continue;
        do_swap(e1, e2);
        int nc = bad_cost();
        if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
            cur = nc;
            if (cur == 0) return 0;
        } else {
            do_swap(e1, e2);
        }
    }
    return cur;
}

static int settle(void) {
    while (now_s() < TLIM) {
        if (anneal(20000, 2.0) == 0) return 1;
    }
    return 0;
}

/* Insert a pair (a = N in side 0, b = N+1 in side 1) by re-routing DEG edges with distinct ends. */
static int insert_pair(void) {
    if (N + 2 > NCAP || NE + DEG > NCAP * DEG) return 0;
    int ex[64], ey[64], ee[64];
    int chosen = 0;
    for (int tries = 0; tries < 200000 && chosen < DEG; tries++) {
        int e = rndint(NE);
        int x = eu[e], y = ev[e];
        int ok = 1;
        for (int i = 0; i < chosen; i++) {
            if (ex[i] == x || ey[i] == y) { ok = 0; break; }
        }
        if (!ok) continue;
        ex[chosen] = x; ey[chosen] = y; ee[chosen] = e;
        chosen++;
    }
    if (chosen < DEG) return 0;
    int a = N, b = N + 1;
    cnt[a] = 0;
    cnt[b] = 0;
    for (int i = 0; i < chosen; i++) {
        int x = ex[i], y = ey[i], e = ee[i];
        eu[e] = a;                 /* edge (a, y) replaces (x, y) */
        eu[NE] = x;                /* new edge (x, b) */
        ev[NE] = b;
        NE++;
        repl(x, y, b);
        repl(y, x, a);
        push(a, y);
        push(b, x);
    }
    N += 2;
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed slice [iters] [target]\n");
        return 1;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t seed = strtoull(argv[3], NULL, 10);
    double slice = atof(argv[4]);
    long iters = argc > 5 ? atol(argv[5]) : 15000;
    int target = argc > 6 ? atoi(argv[6]) : 0;
    if (DEG < 1 || DEG > 64 || DIAM < 1 || iters < 1) { printf("0 0\n"); return 0; }

    rs = seed * 0x9E3779B97F4A7C15ULL ^ 0xABCDEF12345ULL;
    if (rs == 0) rs = 1;

    int n0, m0;
    if (scanf("%d %d", &n0, &m0) != 2) { printf("0 0\n"); return 0; }
    int random_mode = (n0 == 0 && m0 == 0);
    if (random_mode && target < 2 * DEG) { printf("0 0\n"); return 0; }
    if (!random_mode && (n0 < 2 || m0 < 0 || n0 > 200000)) { printf("0 0\n"); return 0; }

    int base = random_mode ? 2 * (target / 2) : n0;
    NCAP = base + 2 * MAXINS + 4;
    WCAP = (NCAP + 63) >> 6;
    adj = malloc(sizeof(int) * (size_t)NCAP * DEG);
    cnt = calloc((size_t)NCAP, sizeof(int));
    eu = malloc(sizeof(int) * (size_t)NCAP * DEG);
    ev = malloc(sizeof(int) * (size_t)NCAP * DEG);
    seu = malloc(sizeof(int) * (size_t)NCAP * DEG);
    sev = malloc(sizeof(int) * (size_t)NCAP * DEG);
    RA = malloc(sizeof(uint64_t) * (size_t)NCAP * WCAP);
    RB = malloc(sizeof(uint64_t) * (size_t)NCAP * WCAP);
    if (!adj || !cnt || !eu || !ev || !seu || !sev || !RA || !RB) { printf("0 0\n"); return 0; }

    if (random_mode) {
        int s = target / 2;
        N = 2 * s;
        NE = 0;
        for (int i = 0; i < s; i++) {
            for (int k = 0; k < DEG; k++) {
                int j = (i + k) % s;
                eu[NE] = i;
                ev[NE] = s + j;
                NE++;
            }
        }
        if (!build_adj()) { printf("0 0\n"); return 0; }
    } else {
        int *tu = malloc(sizeof(int) * (size_t)(m0 + 1));
        int *tv = malloc(sizeof(int) * (size_t)(m0 + 1));
        int *degc = calloc((size_t)n0, sizeof(int));
        int *off = malloc(sizeof(int) * (size_t)(n0 + 1));
        int *lst = malloc(sizeof(int) * (size_t)(2 * m0 + 1));
        int *fillc = calloc((size_t)n0, sizeof(int));
        int *col = malloc(sizeof(int) * (size_t)n0);
        int *q = malloc(sizeof(int) * (size_t)n0);
        if (!tu || !tv || !degc || !off || !lst || !fillc || !col || !q) { printf("0 0\n"); return 0; }
        for (int i = 0; i < m0; i++) {
            int u, v;
            if (scanf("%d %d", &u, &v) != 2) { printf("0 0\n"); return 0; }
            if (u < 0 || v < 0 || u >= n0 || v >= n0 || u == v) { printf("0 0\n"); return 0; }
            tu[i] = u; tv[i] = v;
            degc[u]++; degc[v]++;
        }
        off[0] = 0;
        for (int v = 0; v < n0; v++) off[v + 1] = off[v] + degc[v];
        for (int i = 0; i < m0; i++) {
            int u = tu[i], v = tv[i];
            lst[off[u] + fillc[u]++] = v;
            lst[off[v] + fillc[v]++] = u;
        }
        for (int v = 0; v < n0; v++) col[v] = -1;
        for (int s = 0; s < n0; s++) {
            if (col[s] >= 0) continue;
            col[s] = 0;
            int qh = 0, qt = 0;
            q[qt++] = s;
            while (qh < qt) {
                int u = q[qh++];
                for (int j = off[u]; j < off[u + 1]; j++) {
                    int w = lst[j];
                    if (col[w] < 0) {
                        col[w] = 1 - col[u];
                        q[qt++] = w;
                    } else if (col[w] == col[u]) {
                        printf("0 0\n");
                        return 0;
                    }
                }
            }
        }
        N = n0;
        NE = 0;
        for (int i = 0; i < m0; i++) {
            int u = tu[i], v = tv[i];
            if (col[u] == 0) { eu[NE] = u; ev[NE] = v; }
            else             { eu[NE] = v; ev[NE] = u; }
            NE++;
        }
        if (!build_adj()) { printf("0 0\n"); return 0; }
    }

    TLIM = now_s() + slice;

    if (bad_cost() != 0) {
        if (!settle()) { printf("0 0\n"); return 0; }
    }
    snapshot();

    while (now_s() < TLIM) {
        if (!insert_pair()) break;
        if (anneal(iters, 3.0) == 0) {
            snapshot();
        } else {
            restore();
        }
    }
    restore();

    printf("%d %d\n", sN, sNE);
    for (int e = 0; e < sNE; e++) printf("%d %d\n", seu[e], sev[e]);
    fflush(stdout);
    return 0;
}
"""

GROW_ITERS = 12000


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

    # Phase 1: structured start from the voltage-lift search (kept as the safe baseline).
    lift_deadline = start + 0.55 * budget
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
                C_LIFT,
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

    # Phase 2: unstructured growth. Insert vertex pairs into the best valid graph,
    # then re-anneal by edge switches. Failed attempts are rolled back in C.
    grow_slice = deadline - time.monotonic() - 3.0
    if grow_slice > 2.0 and lib.is_valid(best[0], best[1], d, D):
        try:
            out = lib.run_c(
                C_GROW,
                [d, D, rng.randrange(1, 10 ** 9), f"{grow_slice:.2f}", GROW_ITERS, 0],
                stdin_graph=best,
                timeout=grow_slice + 15.0,
            )
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
