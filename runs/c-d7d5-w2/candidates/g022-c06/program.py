import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Engine 1 (structured): simulated annealing over the voltages of a bi-Cayley
# lift over Z_m x|_r Z_k2 (element (a, b) coded as a*k2 + b). Excess-distance
# cost, zero iff the lift has diameter <= DIAM. Moves: change a voltage, or
# swap two targets inside one layer (keeps degrees).
#
# Usage: prog d D K m k2 r seed slice_seconds
# Prints a valid graph ("n m" + edges) or "0 0".
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
# Engine 2 (unstructured, new): grow-and-repair on a general bipartite graph.
#
# State: a bipartite graph with max degree DEG, kept as an edge list (EA on
# side 0, EB on side 1) plus adjacency lists.
#   * Growth: insert a fresh pair (a, b). Pick DEG edges (x_k, y_k) with
#     distinct x's and distinct y's, delete them, then join a to every y_k and
#     b to every x_k. Degrees of old vertices are unchanged, and a, b reach DEG.
#   * Repair: simulated annealing with edge exchanges (x1,y1),(x2,y2) ->
#     (x1,y2),(x2,y1). This keeps all degrees and bipartiteness.
#   * Cost: number of ordered vertex pairs at distance > DIAM, computed by
#     bitset ball expansion. Zero means a valid graph.
#   * Stagnation: after STAG non-improving moves, restore the best state of the
#     current phase and reheat.
#
# Usage: prog DEG DIAM seed time_seconds maxgrow < graph
# Reads "n m" + edges (must be a valid-degree bipartite graph) from stdin.
# Prints the largest valid graph found (at least the input when it is valid),
# or "0 0".
# ----------------------------------------------------------------------------

C_GROW = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXDEG 32
#define STAG 3000

typedef uint64_t u64;

static int DEG, DIAM, N, NE, CAP, W, SN, SNE, GN, GE;
static int *col, *dg, *adj, *EA, *EB, *SA_, *SB_, *GA, *GB;
static u64 *R0, *R1;
static u64 rs = 88172645463325252ULL;

static u64 rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int n) { return (int)(rnd64() % (u64)n); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int pc64(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int a, int b) {
    const int *p = adj + (size_t)a * DEG;
    for (int i = 0; i < dg[a]; i++) if (p[i] == b) return 1;
    return 0;
}

static void repl(int v, int old, int nw) {
    int *p = adj + (size_t)v * DEG;
    for (int i = 0; i < dg[v]; i++) if (p[i] == old) { p[i] = nw; return; }
}

static void push(int v, int w) { adj[(size_t)v * DEG + dg[v]++] = w; }

static void drop(int v, int w) {
    int *p = adj + (size_t)v * DEG;
    for (int i = 0; i < dg[v]; i++) {
        if (p[i] == w) { p[i] = p[dg[v] - 1]; dg[v]--; return; }
    }
}

/* Exchange the B endpoints of edges i and j. This is an involution. */
static void exch(int i, int j) {
    int a1 = EA[i], b1 = EB[i], a2 = EA[j], b2 = EB[j];
    repl(a1, b1, b2);
    repl(a2, b2, b1);
    repl(b1, a1, a2);
    repl(b2, a2, a1);
    EB[i] = b2;
    EB[j] = b1;
}

static void add_edge(int u, int v) {
    if (col[u] == 1) { int t = u; u = v; v = t; }
    EA[NE] = u; EB[NE] = v; NE++;
    push(u, v);
    push(v, u);
}

static void del_pair(int x, int y) {
    for (int i = 0; i < NE; i++) {
        if (EA[i] == x && EB[i] == y) {
            EA[i] = EA[NE - 1];
            EB[i] = EB[NE - 1];
            NE--;
            drop(x, y);
            drop(y, x);
            return;
        }
    }
}

static void rebuild(void) {
    for (int v = 0; v < N; v++) dg[v] = 0;
    for (int i = 0; i < NE; i++) {
        push(EA[i], EB[i]);
        push(EB[i], EA[i]);
    }
}

static long long cost_fn(void) {
    memset(R0, 0, sizeof(u64) * (size_t)N * W);
    for (int v = 0; v < N; v++) R0[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int t = 0; t < DIAM; t++) {
        for (int v = 0; v < N; v++) {
            u64 *out = R1 + (size_t)v * W;
            const u64 *in = R0 + (size_t)v * W;
            memcpy(out, in, sizeof(u64) * (size_t)W);
            const int *p = adj + (size_t)v * DEG;
            for (int i = 0; i < dg[v]; i++) {
                const u64 *s = R0 + (size_t)p[i] * W;
                for (int w = 0; w < W; w++) out[w] |= s[w];
            }
        }
        u64 *tmp = R0; R0 = R1; R1 = tmp;
    }
    long long c = 0;
    for (int v = 0; v < N; v++) {
        int cnt = 0;
        const u64 *r = R0 + (size_t)v * W;
        for (int w = 0; w < W; w++) cnt += pc64(r[w]);
        c += N - cnt;
    }
    return c;
}

static int insert_pair(void) {
    if (N + 2 > CAP) return 0;
    if (NE < DEG) return 0;
    int sel[MAXDEG];
    int k = 0, tries = 0;
    while (k < DEG && tries < 4000) {
        tries++;
        int i = rndint(NE);
        int ok = 1;
        for (int q = 0; q < k; q++) {
            if (sel[q] == i || EA[sel[q]] == EA[i] || EB[sel[q]] == EB[i]) { ok = 0; break; }
        }
        if (ok) sel[k++] = i;
    }
    if (k < DEG) return 0;
    int xs[MAXDEG], ys[MAXDEG];
    for (int q = 0; q < DEG; q++) { xs[q] = EA[sel[q]]; ys[q] = EB[sel[q]]; }
    for (int q = 0; q < DEG; q++) del_pair(xs[q], ys[q]);
    int a = N, b = N + 1;
    N += 2;
    col[a] = 0; col[b] = 1;
    dg[a] = 0; dg[b] = 0;
    for (int q = 0; q < DEG; q++) {
        add_edge(a, ys[q]);
        add_edge(xs[q], b);
    }
    return 1;
}

static void snapshot(void) {
    memcpy(SA_, EA, sizeof(int) * (size_t)NE);
    memcpy(SB_, EB, sizeof(int) * (size_t)NE);
    SNE = NE; SN = N;
}

static void restore(void) {
    NE = SNE; N = SN;
    memcpy(EA, SA_, sizeof(int) * (size_t)NE);
    memcpy(EB, SB_, sizeof(int) * (size_t)NE);
    rebuild();
}

static void saveglobal(void) {
    GN = N; GE = NE;
    memcpy(GA, EA, sizeof(int) * (size_t)NE);
    memcpy(GB, EB, sizeof(int) * (size_t)NE);
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    u64 seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    int maxgrow = argc > 5 ? atoi(argv[5]) : 300;
    rs = seed * 0x9E3779B97F4A7C15ULL ^ 0xABCDEF12345ULL;
    if (rs == 0) rs = 1;

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 <= 0 || m0 < 0 || DEG < 1 || DEG > MAXDEG ||
        DIAM < 1 || maxgrow < 0) {
        printf("0 0\n");
        return 0;
    }
    CAP = n0 + 2 * maxgrow + 4;
    W = (CAP + 63) / 64;
    size_t capE = (size_t)CAP * DEG + 8;
    col = malloc(sizeof(int) * CAP);
    dg = calloc(CAP, sizeof(int));
    adj = malloc(sizeof(int) * capE);
    EA = malloc(sizeof(int) * capE);
    EB = malloc(sizeof(int) * capE);
    SA_ = malloc(sizeof(int) * capE);
    SB_ = malloc(sizeof(int) * capE);
    GA = malloc(sizeof(int) * capE);
    GB = malloc(sizeof(int) * capE);
    R0 = malloc(sizeof(u64) * (size_t)CAP * W);
    R1 = malloc(sizeof(u64) * (size_t)CAP * W);
    if (!col || !dg || !adj || !EA || !EB || !SA_ || !SB_ || !GA || !GB || !R0 || !R1) {
        printf("0 0\n");
        return 0;
    }

    NE = 0;
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { printf("0 0\n"); return 0; }
        if (u < 0 || v < 0 || u >= n0 || v >= n0 || u == v || dg[u] >= DEG || dg[v] >= DEG ||
            has_edge(u, v)) {
            printf("0 0\n");
            return 0;
        }
        EA[NE] = u; EB[NE] = v; NE++;
        push(u, v);
        push(v, u);
    }
    N = n0;

    /* Bipartition by BFS. */
    for (int v = 0; v < N; v++) col[v] = -1;
    int *stk = malloc(sizeof(int) * CAP);
    if (!stk) { printf("0 0\n"); return 0; }
    for (int s = 0; s < N; s++) {
        if (col[s] != -1) continue;
        col[s] = 0;
        int sp = 0;
        stk[sp++] = s;
        while (sp > 0) {
            int u = stk[--sp];
            const int *p = adj + (size_t)u * DEG;
            for (int i = 0; i < dg[u]; i++) {
                int v = p[i];
                if (col[v] == -1) { col[v] = 1 - col[u]; stk[sp++] = v; }
                else if (col[v] == col[u]) { printf("0 0\n"); return 0; }
            }
        }
    }
    free(stk);
    for (int i = 0; i < NE; i++) {
        if (col[EA[i]] == 1) { int t = EA[i]; EA[i] = EB[i]; EB[i] = t; }
    }

    GN = 0; GE = 0;
    clock_t t0 = clock();
    long long cur = cost_fn();
    if (cur == 0) saveglobal();
    snapshot();
    long long pbest = cur;
    int since = 0;
    long long it = 0;

    while (1) {
        if ((it++ & 15) == 0 && (double)(clock() - t0) / CLOCKS_PER_SEC >= tl) break;
        if (cur == 0) {
            if (N > GN) saveglobal();
            if (!insert_pair()) break;
            cur = cost_fn();
            pbest = cur;
            since = 0;
            snapshot();
            continue;
        }
        if (since > STAG) {
            restore();
            cur = pbest;
            since = 0;
        }
        if (NE < 2) break;
        double T = 1.5 * (1.0 - (double)since / STAG) + 0.05;
        int i = rndint(NE), j = rndint(NE);
        if (i == j) { since++; continue; }
        int a1 = EA[i], b1 = EB[i], a2 = EA[j], b2 = EB[j];
        if (a1 == a2 || b1 == b2 || has_edge(a1, b2) || has_edge(a2, b1)) { since++; continue; }
        exch(i, j);
        long long nc = cost_fn();
        if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
            cur = nc;
            if (cur < pbest) { pbest = cur; since = 0; snapshot(); }
            else since++;
        } else {
            exch(i, j);
            since++;
        }
    }
    if (cur == 0 && N > GN) saveglobal();

    if (GN > 0) {
        printf("%d %d\n", GN, GE);
        for (int i = 0; i < GE; i++) printf("%d %d\n", GA[i], GB[i]);
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
# Group sampling for the structured lift search.
# ----------------------------------------------------------------------------

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


# ----------------------------------------------------------------------------
# Driver: structured lift start (first ~45% of the budget), then the
# grow-and-repair engine on the best valid graph for the rest.
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

    if D >= 4 and time.monotonic() < lift_deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Phase 1: structured bi-Cayley lifts with adaptive growth.
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

    # Cheap spare-degree extension of the structured start.
    try:
        n2, e2 = _extend_spare(best[0], best[1], d, D, lift_deadline + 0.02 * budget)
        if n2 > best[0] and lib.is_valid(n2, e2, d, D):
            best = (n2, e2)
    except Exception:
        pass

    # Phase 2: grow-and-repair with edge-exchange annealing on the bitset cost.
    remaining = deadline - time.monotonic() - 1.0
    if remaining > 2.0 and best[0] >= 2:
        try:
            out = lib.run_c(
                C_GROW,
                [d, D, rng.randrange(1, 10 ** 9), f"{remaining:.2f}", 400],
                stdin_graph=best,
                timeout=remaining + 15.0,
            )
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
