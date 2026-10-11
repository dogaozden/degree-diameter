import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bold change for this island: a second, different search stage.
#
# Stage 1 (lift search): the parent's bi-Cayley voltage annealer, now given
#   about 40% of the budget. It produces a regular d-valent graph.
#
# Stage 2 (vertex insertion + repair, new): starting from the best regular
#   graph, repeatedly insert a fresh pair (x, y) by removing d-1 disjoint
#   edges (a_i, b_i) and wiring a_i - y, b_i - x, x - y. Every vertex keeps
#   degree d, so the graph stays regular and bipartite. Then 2-switch moves
#   (a1-b1, a2-b2 -> a1-b2, a2-b1) anneal the number of ordered pairs at
#   distance > D to zero. The cost is computed with bitset ball expansion,
#   which is much faster than BFS from every vertex. A failed repair rolls back
#   to the last valid graph, so the output is always valid.
#
# Every candidate is re-checked with lib.is_valid. If a stage fails, the best
# valid graph so far is returned, so the score never falls below the parent's
# lift-only result except through the reduced lift time.
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


INS_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define EXTRA 4000
#define MOVES 4000
#define MAXFAIL 6

static int DEG, DIAM, N, CAP, WCAP, WN;
static int *adj, *side, *bak, *vadj, *vside;
static uint64_t *bs0, *bs1;
static uint64_t rs = 88172645463325252ULL;

static inline uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static inline int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static inline double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static double elapsed(clock_t t0) {
    return (double)(clock() - t0) / (double)CLOCKS_PER_SEC;
}

static void set_wn(void) { WN = (N + 63) >> 6; }

/* Number of ordered pairs (v, w) at distance > DIAM. Zero iff valid. */
static long long cost_fn(void) {
    uint64_t *from = bs0, *to = bs1;
    for (int v = 0; v < N; v++) {
        uint64_t *c = from + (size_t)v * WCAP;
        for (int w = 0; w < WN; w++) c[w] = 0;
        c[v >> 6] |= 1ULL << (v & 63);
    }
    for (int it = 0; it < DIAM; it++) {
        for (int v = 0; v < N; v++) {
            uint64_t *o = to + (size_t)v * WCAP;
            const uint64_t *c = from + (size_t)v * WCAP;
            for (int w = 0; w < WN; w++) o[w] = c[w];
            const int *av = adj + (size_t)v * DEG;
            for (int k = 0; k < DEG; k++) {
                const uint64_t *cu = from + (size_t)av[k] * WCAP;
                for (int w = 0; w < WN; w++) o[w] |= cu[w];
            }
        }
        uint64_t *t = from; from = to; to = t;
    }
    long long bad = 0;
    for (int v = 0; v < N; v++) {
        const uint64_t *c = from + (size_t)v * WCAP;
        int s = 0;
        for (int w = 0; w < WN; w++) s += popc64(c[w]);
        bad += N - s;
    }
    return bad;
}

static int has_edge(int a, int b) {
    const int *av = adj + (size_t)a * DEG;
    for (int k = 0; k < DEG; k++) if (av[k] == b) return 1;
    return 0;
}

static void replace_nb(int v, int old, int nw) {
    int *av = adj + (size_t)v * DEG;
    for (int k = 0; k < DEG; k++) {
        if (av[k] == old) { av[k] = nw; return; }
    }
}

/* 2-switch on a random pair of A-side edges. Returns 0 if the move is not applicable. */
static int move_switch(void) {
    int a1, a2;
    do { a1 = rndint(N); } while (side[a1] != 0);
    do { a2 = rndint(N); } while (side[a2] != 0);
    if (a1 == a2) return 0;
    int b1 = adj[(size_t)a1 * DEG + rndint(DEG)];
    int b2 = adj[(size_t)a2 * DEG + rndint(DEG)];
    if (b1 == b2) return 0;
    if (has_edge(a1, b2) || has_edge(a2, b1)) return 0;
    replace_nb(a1, b1, b2);
    replace_nb(a2, b2, b1);
    replace_nb(b1, a1, a2);
    replace_nb(b2, a2, a1);
    return 1;
}

/* Insert a new A-vertex x and B-vertex y into a d-regular bipartite graph:
   remove DEG-1 disjoint edges (a_i, b_i), add a_i-y, b_i-x, and x-y. */
static int insert_pair(void) {
    int m = DEG - 1;
    int ca[256], cb[256];
    int got = 0;
    if (m < 1 || m > 256) return 0;
    for (long tries = 0; got < m && tries < 200000; tries++) {
        int a = rndint(N);
        if (side[a] != 0) continue;
        int b = adj[(size_t)a * DEG + rndint(DEG)];
        int ok = 1;
        for (int i = 0; i < got; i++) {
            if (ca[i] == a || cb[i] == b) { ok = 0; break; }
        }
        if (ok) { ca[got] = a; cb[got] = b; got++; }
    }
    if (got < m) return 0;
    int x = N, y = N + 1;
    for (int i = 0; i < m; i++) {
        replace_nb(ca[i], cb[i], y);
        replace_nb(cb[i], ca[i], x);
    }
    int *ax = adj + (size_t)x * DEG;
    int *ay = adj + (size_t)y * DEG;
    for (int i = 0; i < m; i++) { ax[i] = cb[i]; ay[i] = ca[i]; }
    ax[m] = y;
    ay[m] = x;
    side[x] = 0;
    side[y] = 1;
    N += 2;
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t seed = strtoull(argv[3], NULL, 10);
    double slice = atof(argv[4]);
    rs = seed * 0x9E3779B97F4A7C15ULL ^ 0x51ED27ULL;
    if (rs == 0) rs = 1;

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { printf("0 0\n"); return 0; }
    if (DEG < 2 || DIAM < 2 || n0 < 2 || n0 > 200000 || m0 < 1) { printf("0 0\n"); return 0; }
    if ((long long)m0 * 2 != (long long)n0 * DEG) { printf("0 0\n"); return 0; }

    int *eu = malloc(sizeof(int) * (size_t)m0);
    int *ev = malloc(sizeof(int) * (size_t)m0);
    int *dg = calloc((size_t)n0, sizeof(int));
    if (!eu || !ev || !dg) { printf("0 0\n"); return 0; }
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= n0 || v >= n0 || u == v) {
            printf("0 0\n");
            return 0;
        }
        eu[i] = u;
        ev[i] = v;
        dg[u]++;
        dg[v]++;
    }
    for (int v = 0; v < n0; v++) {
        if (dg[v] != DEG) { printf("0 0\n"); return 0; }
    }

    CAP = n0 + EXTRA;
    WCAP = (CAP + 63) >> 6;
    adj = malloc(sizeof(int) * (size_t)CAP * DEG);
    bak = malloc(sizeof(int) * (size_t)CAP * DEG);
    vadj = malloc(sizeof(int) * (size_t)CAP * DEG);
    side = malloc(sizeof(int) * (size_t)CAP);
    vside = malloc(sizeof(int) * (size_t)CAP);
    bs0 = calloc((size_t)CAP * WCAP, sizeof(uint64_t));
    bs1 = calloc((size_t)CAP * WCAP, sizeof(uint64_t));
    int *queue = malloc(sizeof(int) * (size_t)CAP);
    int *fc = calloc((size_t)n0, sizeof(int));
    if (!adj || !bak || !vadj || !side || !vside || !bs0 || !bs1 || !queue || !fc) {
        printf("0 0\n");
        return 0;
    }

    for (int i = 0; i < m0; i++) {
        int u = eu[i], v = ev[i];
        adj[(size_t)u * DEG + fc[u]++] = v;
        adj[(size_t)v * DEG + fc[v]++] = u;
    }
    for (int v = 0; v < n0; v++)
        for (int k = 0; k < DEG; k++)
            for (int l = 0; l < k; l++)
                if (adj[(size_t)v * DEG + k] == adj[(size_t)v * DEG + l]) {
                    printf("0 0\n");
                    return 0;
                }

    /* Bipartition by BFS; reject non-bipartite input. */
    N = n0;
    set_wn();
    for (int v = 0; v < N; v++) side[v] = -1;
    for (int s = 0; s < N; s++) {
        if (side[s] != -1) continue;
        side[s] = 0;
        int qh = 0, qt = 0;
        queue[qt++] = s;
        while (qh < qt) {
            int u = queue[qh++];
            for (int k = 0; k < DEG; k++) {
                int w = adj[(size_t)u * DEG + k];
                if (side[w] == -1) {
                    side[w] = 1 - side[u];
                    queue[qt++] = w;
                } else if (side[w] == side[u]) {
                    printf("0 0\n");
                    return 0;
                }
            }
        }
    }
    if (cost_fn() != 0) { printf("0 0\n"); return 0; }

    int vN = N;
    memcpy(vadj, adj, sizeof(int) * (size_t)N * DEG);
    memcpy(vside, side, sizeof(int) * (size_t)N);

    clock_t t0 = clock();
    int fails = 0;
    while (fails < MAXFAIL && elapsed(t0) < slice) {
        if (vN + 2 > CAP) break;
        N = vN;
        set_wn();
        memcpy(adj, vadj, sizeof(int) * (size_t)N * DEG);
        memcpy(side, vside, sizeof(int) * (size_t)N);
        if (!insert_pair()) { fails++; continue; }
        set_wn();
        long long c = cost_fn();
        for (int it = 0; it < MOVES && c > 0; it++) {
            if ((it & 63) == 0 && elapsed(t0) >= slice) break;
            double T = 1.5 * (1.0 - (double)it / MOVES) + 0.02;
            memcpy(bak, adj, sizeof(int) * (size_t)N * DEG);
            if (!move_switch()) continue;
            long long nc = cost_fn();
            if (nc <= c || rnd01() < exp(-(double)(nc - c) / T)) {
                c = nc;
            } else {
                memcpy(adj, bak, sizeof(int) * (size_t)N * DEG);
            }
        }
        if (c == 0) {
            vN = N;
            memcpy(vadj, adj, sizeof(int) * (size_t)N * DEG);
            memcpy(vside, side, sizeof(int) * (size_t)N);
            fails = 0;
        } else {
            fails++;
        }
    }

    printf("%d %d\n", vN, vN * DEG / 2);
    for (int v = 0; v < vN; v++) {
        if (vside[v] != 0) continue;
        for (int k = 0; k < DEG; k++)
            printf("%d %d\n", v, vadj[(size_t)v * DEG + k]);
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
# Group sampling for the lift search.
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
# Stage 2 driver: vertex insertion + repair in C.
# ----------------------------------------------------------------------------

def _grow_insert(n, edges, d, D, slice_s, seed):
    """Run the insertion engine on a d-regular graph. Returns (n, edges) or None."""
    try:
        out = lib.run_c(INS_SOURCE, [d, D, seed, f"{slice_s:.2f}"],
                        stdin_graph=(n, edges), timeout=slice_s + 3.0)
        n2, e2 = lib.parse_graph_text(out)
    except (RuntimeError, ValueError):
        return None
    return n2, e2


# ----------------------------------------------------------------------------
# Build.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.9 * time_limit, time_limit - 4.0))
    deadline = t0 + budget
    lift_deadline = t0 + 0.4 * budget
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

    # Stage 1: lift search, with adaptive growth of the target size.
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

    # Spare-degree extension (returns at once for regular graphs).
    try:
        n2, e2 = _extend_spare(best[0], best[1], d, D, lift_deadline)
        if n2 > best[0] and lib.is_valid(n2, e2, d, D):
            best = (n2, e2)
    except Exception:
        pass

    # Stage 2: vertex insertion + repair, starting from the best regular graph.
    if d >= 3 and D >= 2:
        slice_s = deadline - time.monotonic() - 3.0
        if slice_s >= 2.0:
            res = _grow_insert(best[0], best[1], d, D, slice_s,
                               rng.randrange(1, 10 ** 9))
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
