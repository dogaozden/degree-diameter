import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Engine A (lift search): simulated annealing over the voltages of a bi-Cayley
# lift over Z_m x|_r Z_k2 (element (a, b) coded as a*k2 + b).
#
# Base graph: K vertices per side, DEG layers, each layer a permutation of
# 0..K-1. Dart e = l*K + i joins A_i to B_{dJ[e]} with voltage dS[e].
# Cost = unreached (rep, vertex) pairs + duplicate penalty.
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
# Engine B (growth): a substantially different search. It takes a valid,
# (nearly) regular bipartite graph, adds T fresh vertex pairs by edge
# "splitting" (remove edge x-y, add a-y and x-b, with a-b joined), then
# anneals with degree-preserving double-edge swaps. Cost = number of unordered
# vertex pairs at distance > DIAM, computed with bitsets over all vertices.
# Accepts only cost 0. Prints a graph or "0 0".
#
# Usage: prog d D T seed slice_seconds      (stdin: graph in "n m" format)
# ----------------------------------------------------------------------------

GROW_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 2600
#define MAXDEG 12
#define MAXE (MAXN * MAXDEG / 2 + 64)
#define MAXW ((MAXN + 63) / 64)

static int DEG, DIAM, N, NE, W;
static int adj[MAXN][MAXDEG];
static int dg[MAXN];
static int side[MAXN];
static int stk[MAXN];
static int ea[MAXE], eb[MAXE];
static int bestEb[MAXE];
static int EU[MAXE], EV[MAXE];
static uint64_t bufA[MAXN * MAXW], bufB[MAXN * MAXW];
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

static inline int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int u, int v) {
    for (int i = 0; i < dg[u]; i++) if (adj[u][i] == v) return 1;
    return 0;
}

static void repl(int v, int old, int nw) {
    for (int i = 0; i < dg[v]; i++) if (adj[v][i] == old) { adj[v][i] = nw; return; }
}

static void add_adj(int u, int v) {
    adj[u][dg[u]++] = v;
    adj[v][dg[v]++] = u;
}

static void rebuild(void) {
    for (int v = 0; v < N; v++) dg[v] = 0;
    for (int e = 0; e < NE; e++) add_adj(ea[e], eb[e]);
}

/* Swap the B-endpoints of edges e1=(x1,y1) and e2=(x2,y2) -> (x1,y2),(x2,y1).
   Applying it twice restores the original. */
static void applySwap(int e1, int e2) {
    int x1 = ea[e1], y1 = eb[e1], x2 = ea[e2], y2 = eb[e2];
    eb[e1] = y2; eb[e2] = y1;
    repl(x1, y1, y2);
    repl(x2, y2, y1);
    repl(y1, x1, x2);
    repl(y2, x2, x1);
}

static long cost_fn(void) {
    int Wd = W;
    for (int v = 0; v < N; v++) {
        uint64_t *c = bufA + (size_t)v * Wd;
        memset(c, 0, sizeof(uint64_t) * (size_t)Wd);
        c[v >> 6] |= 1ULL << (v & 63);
    }
    uint64_t *cur = bufA, *nxt = bufB;
    for (int r = 0; r < DIAM; r++) {
        for (int v = 0; v < N; v++) {
            uint64_t *o = nxt + (size_t)v * Wd;
            const uint64_t *c = cur + (size_t)v * Wd;
            memcpy(o, c, sizeof(uint64_t) * (size_t)Wd);
            for (int i = 0; i < dg[v]; i++) {
                const uint64_t *cu = cur + (size_t)adj[v][i] * Wd;
                for (int w = 0; w < Wd; w++) o[w] |= cu[w];
            }
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
    }
    long total = 0;
    for (int v = 0; v < N; v++) {
        const uint64_t *c = cur + (size_t)v * Wd;
        int cnt = 0;
        for (int w = 0; w < Wd; w++) cnt += pc64(c[w]);
        total += N - cnt;
    }
    return total / 2;
}

static int read_graph(void) {
    int n, m;
    if (scanf("%d %d", &n, &m) != 2) return 0;
    if (n < 1 || n > MAXN - 2 || m < 0 || m > MAXE) return 0;
    N = n;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return 0;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) return 0;
        EU[i] = u; EV[i] = v;
    }
    NE = m;
    for (int v = 0; v < N; v++) dg[v] = 0;
    for (int i = 0; i < m; i++) {
        int u = EU[i], v = EV[i];
        if (dg[u] >= DEG || dg[v] >= DEG) return 0;
        if (has_edge(u, v)) return 0;
        add_adj(u, v);
    }
    for (int v = 0; v < N; v++) side[v] = -1;
    for (int s = 0; s < N; s++) {
        if (side[s] != -1) continue;
        side[s] = 0;
        int sp = 0;
        stk[sp++] = s;
        while (sp > 0) {
            int u = stk[--sp];
            for (int i = 0; i < dg[u]; i++) {
                int v = adj[u][i];
                if (side[v] == -1) {
                    side[v] = 1 - side[u];
                    stk[sp++] = v;
                } else if (side[v] == side[u]) {
                    return 0;
                }
            }
        }
    }
    for (int i = 0; i < m; i++) {
        if (side[EU[i]] == 0) { ea[i] = EU[i]; eb[i] = EV[i]; }
        else { ea[i] = EV[i]; eb[i] = EU[i]; }
    }
    rebuild();
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 6) { printf("0 0\n"); return 0; }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    int T = atoi(argv[3]);
    uint64_t seed = strtoull(argv[4], NULL, 10);
    double slice = atof(argv[5]);
    if (DEG < 1 || DEG > MAXDEG || DIAM < 1 || T < 1 || T > 64) { printf("0 0\n"); return 0; }

    rs = seed * 0x9E3779B97F4A7C15ULL ^ 0x5DEECE66DULL;
    if (rs == 0) rs = 1;

    if (!read_graph()) { printf("0 0\n"); return 0; }
    if (N + 2 * T > MAXN) { printf("0 0\n"); return 0; }

    /* Growth: add T pairs (a,b) with edge a-b; fill a and b by splitting edges. */
    for (int p = 0; p < T; p++) {
        int a = N, b = N + 1;
        N += 2;
        dg[a] = 0; dg[b] = 0;
        ea[NE] = a; eb[NE] = b; NE++;
        add_adj(a, b);
        long tries = 0;
        while (dg[a] < DEG) {
            if (++tries > 5000000L) { printf("0 0\n"); return 0; }
            int e = rndint(NE);
            int x = ea[e], y = eb[e];
            if (x == a || y == b) continue;
            if (has_edge(b, x) || has_edge(a, y)) continue;
            /* Edge (x,y) becomes (a,y); new edge (x,b). Degrees of x,y unchanged. */
            repl(x, y, b);
            repl(y, x, a);
            adj[a][dg[a]++] = y;
            adj[b][dg[b]++] = x;
            ea[e] = a; eb[e] = y;
            ea[NE] = x; eb[NE] = b; NE++;
        }
    }

    W = (N + 63) / 64;
    int cur = (int)cost_fn();
    int bestC = cur;
    memcpy(bestEb, eb, sizeof(int) * (size_t)NE);
    int found = (cur == 0);

    clock_t t0 = clock();
    const int RL = 3000;
    const double T0 = 2.0, T1 = 0.02;
    while (!found && elapsed(t0) < slice) {
        for (int it = 0; it < RL; it++) {
            if (elapsed(t0) >= slice) break;
            double Tt = T0 * (1.0 - (double)it / RL) + T1;
            int e1 = rndint(NE), e2 = rndint(NE);
            if (e1 == e2) continue;
            int x1 = ea[e1], y1 = eb[e1], x2 = ea[e2], y2 = eb[e2];
            if (x1 == x2 || y1 == y2) continue;
            if (has_edge(x1, y2) || has_edge(x2, y1)) continue;
            applySwap(e1, e2);
            int nc = (int)cost_fn();
            if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / Tt)) {
                cur = nc;
                if (cur < bestC) {
                    bestC = cur;
                    memcpy(bestEb, eb, sizeof(int) * (size_t)NE);
                    if (cur == 0) { found = 1; break; }
                }
            } else {
                applySwap(e1, e2);
            }
        }
        if (found) break;
        /* Restart the next cycle from the best state seen so far. */
        memcpy(eb, bestEb, sizeof(int) * (size_t)NE);
        rebuild();
        cur = bestC;
    }

    if (!found) { printf("0 0\n"); return 0; }
    printf("%d %d\n", N, NE);
    for (int e = 0; e < NE; e++) printf("%d %d\n", ea[e], eb[e]);
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


# ----------------------------------------------------------------------------
# Spare-degree extension (cheap; no-op for regular graphs).
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
# Driver stages.
# ----------------------------------------------------------------------------

def _lift_stage(best, d, D, lift_deadline, rng, consider):
    """Phase A: bi-Cayley lift voltage annealing (produces the strong base graph)."""
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


def _grow_stage(best, d, D, deadline, rng):
    """Phase B: add vertex pairs to the current best with the annealing growth engine.

    The number of pairs per step adapts: doubles on success, halves on failure.
    Every accepted graph is checked with lib.is_valid, so a bad run never lowers the result.
    """
    n, e = best
    t = 1
    while True:
        remaining = deadline - time.monotonic()
        if remaining < 3.0:
            break
        slice_s = min(remaining - 2.0, 8.0)
        try:
            out = lib.run_c(
                GROW_SOURCE,
                [d, D, t, rng.randrange(1, 10 ** 9), f"{slice_s:.2f}"],
                stdin_graph=(n, e),
                timeout=slice_s + 5.0,
            )
        except RuntimeError:
            break
        try:
            n2, e2 = lib.parse_graph_text(out)
        except ValueError:
            break
        if n2 > n and lib.is_valid(n2, e2, d, D):
            n, e = n2, e2
            t = min(2 * t, 8)
        else:
            t = max(1, t // 2)
    return n, e


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 5.0))
    deadline = start + budget
    lift_deadline = start + 0.4 * budget
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

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Phase A: lift search for a strong base.
    _lift_stage(best, d, D, lift_deadline, rng, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))

    # Phase B: growth by degree-preserving annealing (new construction path).
    try:
        n3, e3 = _grow_stage(best, d, D, deadline, rng)
        if n3 > best[0] and lib.is_valid(n3, e3, d, D):
            best = (n3, e3)
    except Exception:
        pass

    # Spare-degree extension with whatever time is left.
    try:
        n2, e2 = _extend_spare(best[0], best[1], d, D, deadline)
        if n2 > best[0] and lib.is_valid(n2, e2, d, D):
            best = (n2, e2)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
