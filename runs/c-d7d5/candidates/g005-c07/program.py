import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Stage 1 C engine: simulated annealing over the voltages of a bi-Cayley lift
# over Z_m x|_r Z_k2 (element (a, b) coded as a*k2 + b). It produces a valid
# regular bipartite start graph of order about 2*K*m*k2.
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
# Stage 2 C engine: vertex-insertion growth with repair.
#
# The graph stays bipartite with max degree DEG. A growth step removes DEG-1
# edges forming a matching (x_i in A, y_i in B), adds a new A-vertex u joined
# to every y_i and a new B-vertex w joined to every x_i, and adds u-w. Degrees
# are preserved (u and w get degree DEG), so the graph stays regular if it was.
# The cost is the number of ordered pairs at distance > DIAM, computed exactly
# with bitsets. Repair uses degree-preserving 2-switches with simulated
# annealing. Each success becomes the new base. Failed attempts restart from
# the base with a fresh random insertion.
#
# Usage: prog d D iters seed slice_seconds   (graph on stdin)
# Prints the largest valid graph found ("n m" + edges) or "0 0".
# ----------------------------------------------------------------------------

C_REPAIR = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 8192
#define WMAX ((MAXN + 63) / 64)

static int DEG, DIAM;
static int N, M;
static int *adj, *dg, *col, *EA, *EB;
static uint64_t *rA, *rB;
static int *badj, *bdg, *bcol, *bEA, *bEB;
static int bN, bM, have_base;
static uint64_t rs;
static unsigned int markA[MAXN], markB[MAXN];
static unsigned int gstamp = 0;

static uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double elapsed(clock_t t0) {
    return (double)(clock() - t0) / (double)CLOCKS_PER_SEC;
}

static int has_adj(int v, int u) {
    const int *a = adj + (size_t)v * DEG;
    for (int i = 0; i < dg[v]; i++) if (a[i] == u) return 1;
    return 0;
}
static void add_adj(int v, int u) { adj[(size_t)v * DEG + dg[v]++] = u; }
static void del_adj(int v, int u) {
    int *a = adj + (size_t)v * DEG;
    for (int i = 0; i < dg[v]; i++) {
        if (a[i] == u) { a[i] = a[--dg[v]]; return; }
    }
}
static void replace_adj(int v, int old, int nw) {
    int *a = adj + (size_t)v * DEG;
    for (int i = 0; i < dg[v]; i++) {
        if (a[i] == old) { a[i] = nw; return; }
    }
}
static void add_edge(int a, int b) {
    EA[M] = a; EB[M] = b; M++;
    add_adj(a, b); add_adj(b, a);
}
static void remove_edge_idx(int idx) {
    int a = EA[idx], b = EB[idx];
    del_adj(a, b); del_adj(b, a);
    M--;
    EA[idx] = EA[M]; EB[idx] = EB[M];
}
static int find_edge(int a, int b) {
    for (int i = 0; i < M; i++) if (EA[i] == a && EB[i] == b) return i;
    return -1;
}

/* Edges e1 = (a,b) and e2 = (c,e) become (a,e) and (c,b). Applying it again to
   e1 = (a,e), e2 = (c,b) restores the original pair. */
static void switch_edges(int e1, int e2) {
    int a = EA[e1], b = EB[e1], c = EA[e2], e = EB[e2];
    replace_adj(a, b, e);
    replace_adj(b, a, c);
    replace_adj(c, e, b);
    replace_adj(e, c, a);
    EB[e1] = e;
    EB[e2] = b;
}

/* Number of ordered pairs (v,w), v != w, at distance > DIAM. */
static long long cost_eval(void) {
    int W = (N + 63) >> 6;
    uint64_t *cur = rA, *nxt = rB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)N * W);
    for (int v = 0; v < N; v++) cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int lv = 0; lv < DIAM; lv++) {
        for (int v = 0; v < N; v++) {
            uint64_t *o = nxt + (size_t)v * W;
            const uint64_t *s = cur + (size_t)v * W;
            for (int w = 0; w < W; w++) o[w] = s[w];
            const int *a = adj + (size_t)v * DEG;
            for (int i = 0; i < dg[v]; i++) {
                const uint64_t *t = cur + (size_t)a[i] * W;
                for (int w = 0; w < W; w++) o[w] |= t[w];
            }
        }
        uint64_t *tmp = cur; cur = nxt; nxt = tmp;
    }
    long long bad = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        const uint64_t *s = cur + (size_t)v * W;
        for (int w = 0; w < W; w++) c += __builtin_popcountll(s[w]);
        bad += N - c;
    }
    return bad;
}

static void save_base(void) {
    bN = N; bM = M;
    memcpy(badj, adj, sizeof(int) * (size_t)N * DEG);
    memcpy(bdg, dg, sizeof(int) * (size_t)N);
    memcpy(bcol, col, sizeof(int) * (size_t)N);
    memcpy(bEA, EA, sizeof(int) * (size_t)M);
    memcpy(bEB, EB, sizeof(int) * (size_t)M);
    have_base = 1;
}

static void restore_base(void) {
    N = bN; M = bM;
    memcpy(adj, badj, sizeof(int) * (size_t)N * DEG);
    memcpy(dg, bdg, sizeof(int) * (size_t)N);
    memcpy(col, bcol, sizeof(int) * (size_t)N);
    memcpy(EA, bEA, sizeof(int) * (size_t)M);
    memcpy(EB, bEB, sizeof(int) * (size_t)M);
}

static int grow_once(void) {
    int k = DEG - 1;
    if (k < 0 || k > 63) return 0;
    if (N + 2 > MAXN || M < k || M < 1) return 0;
    int sx[64], sy[64];
    gstamp++;
    int cnt = 0;
    long long tries = 0, limit = 200LL * (M + 10);
    while (cnt < k && tries < limit) {
        tries++;
        int idx = rndint(M);
        int x = EA[idx], y = EB[idx];
        if (markA[x] == gstamp || markB[y] == gstamp) continue;
        markA[x] = gstamp; markB[y] = gstamp;
        sx[cnt] = x; sy[cnt] = y; cnt++;
    }
    if (cnt < k) return 0;
    for (int i = 0; i < k; i++) {
        int idx = find_edge(sx[i], sy[i]);
        if (idx < 0) return 0;
        remove_edge_idx(idx);
    }
    int u = N, w = N + 1;
    col[u] = 0; col[w] = 1;
    dg[u] = 0; dg[w] = 0;
    N += 2;
    for (int i = 0; i < k; i++) {
        add_edge(u, sy[i]);
        add_edge(sx[i], w);
    }
    add_edge(u, w);
    return 1;
}

static int anneal(int iters, double T0, clock_t t0, double slice) {
    if (M < 2) return 0;
    long long cur = cost_eval();
    if (cur == 0) return 1;
    for (int it = 0; it < iters; it++) {
        if ((it & 15) == 0 && elapsed(t0) >= slice) break;
        double T = T0 * (1.0 - (double)it / iters) + 0.05;
        int e1 = rndint(M), e2 = rndint(M);
        if (e1 == e2) continue;
        int a = EA[e1], b = EB[e1], c = EA[e2], e = EB[e2];
        if (a == c || b == e) continue;
        if (has_adj(a, e) || has_adj(c, b)) continue;
        switch_edges(e1, e2);
        long long nc = cost_eval();
        if (nc <= cur || rnd01() < exp((double)(cur - nc) / T)) {
            cur = nc;
            if (cur == 0) return 1;
        } else {
            switch_edges(e1, e2);
        }
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 6) { printf("0 0\n"); return 0; }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    int iters = atoi(argv[3]);
    uint64_t seed = strtoull(argv[4], NULL, 10);
    double slice = atof(argv[5]);
    if (DEG < 1 || DIAM < 1 || iters < 1) { printf("0 0\n"); return 0; }
    rs = seed * 0x9E3779B97F4A7C15ULL ^ 0xABCDEFULL;
    if (rs == 0) rs = 1;

    int n0, m0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 < 1 || n0 > MAXN - 2 || m0 < 0) {
        printf("0 0\n");
        return 0;
    }
    size_t NA = (size_t)MAXN * DEG;
    adj = malloc(sizeof(int) * NA);
    EA = malloc(sizeof(int) * NA);
    EB = malloc(sizeof(int) * NA);
    badj = malloc(sizeof(int) * NA);
    bEA = malloc(sizeof(int) * NA);
    bEB = malloc(sizeof(int) * NA);
    dg = calloc(MAXN, sizeof(int));
    col = calloc(MAXN, sizeof(int));
    bdg = calloc(MAXN, sizeof(int));
    bcol = calloc(MAXN, sizeof(int));
    rA = calloc((size_t)MAXN * WMAX, sizeof(uint64_t));
    rB = calloc((size_t)MAXN * WMAX, sizeof(uint64_t));
    int *U = malloc(sizeof(int) * (m0 + 1));
    int *V = malloc(sizeof(int) * (m0 + 1));
    int *q = malloc(sizeof(int) * MAXN);
    if (!adj || !EA || !EB || !badj || !bEA || !bEB || !dg || !col || !bdg || !bcol
        || !rA || !rB || !U || !V || !q) {
        printf("0 0\n");
        return 0;
    }

    int bad_input = 0;
    N = n0; M = 0;
    for (int i = 0; i < m0 && !bad_input; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { bad_input = 1; break; }
        if (u < 0 || v < 0 || u >= N || v >= N || u == v) { bad_input = 1; break; }
        if (has_adj(u, v)) { bad_input = 1; break; }
        if (dg[u] >= DEG || dg[v] >= DEG) { bad_input = 1; break; }
        add_adj(u, v); add_adj(v, u);
        U[i] = u; V[i] = v;
    }
    if (bad_input) { printf("0 0\n"); return 0; }

    for (int v = 0; v < N; v++) col[v] = -1;
    for (int s = 0; s < N && !bad_input; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int head = 0, tail = 0;
        q[tail++] = s;
        while (head < tail && !bad_input) {
            int x = q[head++];
            const int *ax = adj + (size_t)x * DEG;
            for (int i = 0; i < dg[x]; i++) {
                int y = ax[i];
                if (col[y] < 0) { col[y] = 1 - col[x]; q[tail++] = y; }
                else if (col[y] == col[x]) { bad_input = 1; break; }
            }
        }
    }
    if (bad_input) { printf("0 0\n"); return 0; }
    for (int i = 0; i < m0; i++) {
        int u = U[i], v = V[i];
        if (col[u] == 0) { EA[M] = u; EB[M] = v; }
        else { EA[M] = v; EB[M] = u; }
        M++;
    }

    clock_t t0 = clock();
    have_base = 0;
    if (anneal(iters, 2.0, t0, slice)) save_base();
    int fails = 0;
    while (elapsed(t0) < slice) {
        if (!have_base) {
            if (anneal(iters, 2.0, t0, slice)) save_base();
            else if (++fails > 50) break;
            continue;
        }
        restore_base();
        if (!grow_once()) {
            if (++fails > 1000) break;
            continue;
        }
        if (anneal(iters, 2.5, t0, slice)) save_base();
    }

    if (!have_base) { printf("0 0\n"); return 0; }
    printf("%d %d\n", bN, bM);
    for (int i = 0; i < bM; i++) printf("%d %d\n", bEA[i], bEB[i]);
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
# Group sampling for the lift stage.
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


# ----------------------------------------------------------------------------
# Driver: exact constructions, then lift search for a start graph, then the
# vertex-insertion repair engine that grows it.
# ----------------------------------------------------------------------------

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
        try:
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
        except Exception:
            pass

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
        try:
            gq = _best_gq(d)
        except Exception:
            gq = None
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Stage 1: lift search for a start graph (about the first 45% of the budget).
    lift_deadline = time.monotonic() + 0.45 * max(0.0, deadline - time.monotonic())
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

    # Stage 2: grow the best graph by vertex insertion with annealing repair.
    remaining = deadline - time.monotonic()
    if remaining > 4.0 and best[0] >= 2:
        slice_s = remaining - 2.0
        try:
            out = lib.run_c(
                C_REPAIR,
                [d, D, 6000, rng.randrange(1, 10 ** 9), f"{slice_s:.2f}"],
                stdin_graph=best,
                timeout=slice_s + 10.0,
            )
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
