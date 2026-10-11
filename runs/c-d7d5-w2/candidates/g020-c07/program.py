import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine 1: simulated annealing over voltages of a bi-Cayley lift over
# Z_m x|_r Z_k2. Dart e = l*K + i joins A_i to B_{dJ[e]} with voltage dS[e].
# Cost = excess-distance sum; zero iff the lift has diameter <= DIAM.
# Usage: prog d D K m k2 r seed slice_seconds  -> "n m" + edges, or "0 0".
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
static double elapsed(clock_t t0) { return (double)(clock() - t0) / (double)CLOCKS_PER_SEC; }
static int gcd_int(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }

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
        if (stamp == 0xFFFFFFFFu) { memset(vis, 0, sizeof(uint32_t) * (size_t)N); stamp = 0; }
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
                    if (vis[v] != stamp) { vis[v] = stamp; nxt[nn++] = v; }
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
    if (argc < 9) { fprintf(stderr, "usage: prog d D K m k2 r seed slice\n"); return 1; }
    DEG = atoi(argv[1]); DIAM = atoi(argv[2]); K = atoi(argv[3]); MM = atoi(argv[4]);
    K2 = atoi(argv[5]);
    int r = atoi(argv[6]);
    uint64_t seed = strtoull(argv[7], NULL, 10);
    double slice = atof(argv[8]);
    if (DEG < 1 || DIAM < 1 || K < 1 || MM < 1 || K2 < 1 || K2 > 4096) { printf("0 0\n"); return 0; }
    if (gcd_int(r, MM) != 1) { printf("0 0\n"); return 0; }
    POWR = malloc(sizeof(int) * (size_t)K2);
    if (!POWR) { printf("0 0\n"); return 0; }
    POWR[0] = 1 % MM;
    for (int b = 1; b < K2; b++) POWR[b] = (int)((long long)POWR[b - 1] * r % MM);
    if (((long long)POWR[K2 - 1] * r) % MM != 1 % MM) { printf("0 0\n"); return 0; }
    G = MM * K2; N = 2 * K * G; NE = DEG * K;
    rs = seed * 0x9E3779B97F4A7C15ULL ^ 0x1234567ULL;
    if (rs == 0) rs = 1;
    dI = malloc(sizeof(int) * NE); dJ = malloc(sizeof(int) * NE); dS = malloc(sizeof(int) * NE);
    bestS = malloc(sizeof(int) * NE); bestJ = malloc(sizeof(int) * NE);
    perm = malloc(sizeof(int) * (size_t)NE * G);
    adj = malloc(sizeof(int) * (size_t)N * DEG);
    cnt = malloc(sizeof(int) * N); fr = malloc(sizeof(int) * N); nx = malloc(sizeof(int) * N);
    vis = calloc(N, sizeof(uint32_t));
    int *p = malloc(sizeof(int) * K);
    if (!dI || !dJ || !dS || !bestS || !bestJ || !perm || !adj || !cnt || !fr || !nx || !vis || !p) {
        printf("0 0\n"); return 0;
    }
    clock_t t0 = clock();
    int found = 0, bestCost = BIGCOST;
    const int RL = 60000;
    while (!found && elapsed(t0) < slice) {
        double T0;
        if (bestCost >= BIGCOST || rnd01() < 0.25) {
            for (int l = 0; l < DEG; l++) {
                for (int i = 0; i < K; i++) p[i] = i;
                for (int i = K - 1; i > 0; i--) { int j = rndint(i + 1); int t = p[i]; p[i] = p[j]; p[j] = t; }
                for (int i = 0; i < K; i++) { dI[l * K + i] = i; dJ[l * K + i] = p[i]; }
            }
            for (int e = 0; e < NE; e++) { dS[e] = rndint(G); set_perm(e); }
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
        int runBest = cur, since = 0;
        for (int it = 0; it < RL; it++) {
            if ((it & 255) == 0 && elapsed(t0) >= slice) break;
            double T = T0 * (1.0 - (double)it / RL) + 0.05;
            if (K > 1 && rnd01() < 0.3) {
                int l = rndint(DEG), i1 = rndint(K), i2 = rndint(K - 1);
                if (i2 >= i1) i2++;
                int e1 = l * K + i1, e2 = l * K + i2;
                int t = dJ[e1]; dJ[e1] = dJ[e2]; dJ[e2] = t;
                int nc = cost_fn();
                if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) cur = nc;
                else { t = dJ[e1]; dJ[e1] = dJ[e2]; dJ[e2] = t; }
            } else {
                int e = rndint(NE), old = dS[e], ns = rndint(G);
                if (ns == old) continue;
                dS[e] = ns; set_perm(e);
                int nc = cost_fn();
                if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) cur = nc;
                else { dS[e] = old; set_perm(e); }
            }
            if (cur < bestCost) { bestCost = cur; save_best(); }
            if (cur < runBest) { runBest = cur; since = 0; }
            else if (++since > STAG) break;
            if (cur == 0) { found = 1; break; }
        }
    }
    if (found) {
        printf("%d %d\n", N, NE * G);
        for (int e = 0; e < NE; e++)
            for (int g = 0; g < G; g++)
                printf("%d %d\n", dI[e] * G + g, (K + dJ[e]) * G + perm[(size_t)e * G + g]);
    } else {
        printf("0 0\n");
    }
    fflush(stdout);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# C engine 2 (new construction): graph surgery + annealing on the explicit graph.
#  * Input: a valid bipartite graph (stdin, "n m" + edges).
#  * Repair move: double edge swap (a1,b1),(a2,b2) -> (a1,b2),(a2,b1); keeps
#    bipartiteness and all degrees.
#  * Growth move (when cost is 0): add a fresh pair (a,b) with edge a-b; remove
#    up to DEG-1 disjoint edges (x_i,y_i) and attach a to every y_i and b to every
#    x_i. Degrees stay <= DEG.
#  * Cost = number of ordered vertex pairs at distance > DIAM, computed by
#    bit-parallel BFS over all sources.
#  * Output: the largest valid graph found (always at least the input).
# Usage: prog d D seed slice_seconds
# ----------------------------------------------------------------------------

C_SURGERY = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 4096
#define MAXM 80000
#define WMAX 64
#define MAXDEG 32

static int DEG, DIAM, n, M;
static int col[MAXN];
static int eu[MAXM], ev[MAXM];
static int snu[MAXM], snv[MAXM], snM;
static int beu[MAXM], bev[MAXM], bestN, bestM;
static int lastI, lastJ, lastB1, lastB2;
static unsigned char adjm[MAXN][MAXN];
static int nb[MAXN][MAXDEG];
static int dg[MAXN];
static uint64_t RB[2][MAXN][WMAX];
static uint64_t rs = 88172645463325252ULL;

static inline uint64_t rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }
static inline double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double elapsed(clock_t t0) { return (double)(clock() - t0) / (double)CLOCKS_PER_SEC; }

static int pop64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static long cost_fn(void) {
    int Wn = (n + 63) >> 6;
    for (int v = 0; v < n; v++) dg[v] = 0;
    for (int e = 0; e < M; e++) {
        int a = eu[e], b = ev[e];
        nb[a][dg[a]++] = b;
        nb[b][dg[b]++] = a;
    }
    int cur = 0;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < Wn; w++) RB[0][v][w] = 0;
        RB[0][v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int t = 0; t < DIAM; t++) {
        int nxt = cur ^ 1;
        for (int v = 0; v < n; v++) {
            uint64_t *o = RB[nxt][v];
            const uint64_t *s = RB[cur][v];
            for (int w = 0; w < Wn; w++) o[w] = s[w];
            for (int k = 0; k < dg[v]; k++) {
                const uint64_t *u = RB[cur][nb[v][k]];
                for (int w = 0; w < Wn; w++) o[w] |= u[w];
            }
        }
        cur = nxt;
    }
    long total = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < Wn; w++) c += pop64(RB[cur][v][w]);
        total += n - c;
    }
    return total;
}

static void set_adj(void) { for (int e = 0; e < M; e++) adjm[eu[e]][ev[e]] = 1; }
static void clear_adj(void) { for (int e = 0; e < M; e++) adjm[eu[e]][ev[e]] = 0; }

static void snapshot(void) {
    memcpy(snu, eu, sizeof(int) * (size_t)M);
    memcpy(snv, ev, sizeof(int) * (size_t)M);
    snM = M;
}

static void restore(void) {
    clear_adj();
    memcpy(eu, snu, sizeof(int) * (size_t)snM);
    memcpy(ev, snv, sizeof(int) * (size_t)snM);
    M = snM;
    set_adj();
}

static int swap_move(void) {
    int i = rndint(M), j = rndint(M);
    if (i == j) return 0;
    int a1 = eu[i], b1 = ev[i], a2 = eu[j], b2 = ev[j];
    if (a1 == a2 || b1 == b2) return 0;
    if (adjm[a1][b2] || adjm[a2][b1]) return 0;
    adjm[a1][b1] = 0; adjm[a2][b2] = 0;
    adjm[a1][b2] = 1; adjm[a2][b1] = 1;
    ev[i] = b2; ev[j] = b1;
    lastI = i; lastJ = j; lastB1 = b1; lastB2 = b2;
    return 1;
}

static void undo_swap(void) {
    int a1 = eu[lastI], a2 = eu[lastJ];
    adjm[a1][lastB2] = 0; adjm[a2][lastB1] = 0;
    adjm[a1][lastB1] = 1; adjm[a2][lastB2] = 1;
    ev[lastI] = lastB1; ev[lastJ] = lastB2;
}

static void add_edge(int x, int y) {
    eu[M] = x; ev[M] = y; adjm[x][y] = 1; M++;
}

static int grow(void) {
    if (n + 2 > MAXN) return 0;
    int k = DEG - 1;
    if (k < 0) k = 0;
    if (k > MAXDEG - 2) k = MAXDEG - 2;
    int xs[MAXDEG], ys[MAXDEG], idx[MAXDEG], c = 0;
    int tries = 0;
    while (c < k && tries < 4000 && M > 0) {
        tries++;
        int e = rndint(M), x = eu[e], y = ev[e], ok = 1;
        for (int q = 0; q < c; q++) if (xs[q] == x || ys[q] == y) { ok = 0; break; }
        if (!ok) continue;
        xs[c] = x; ys[c] = y; idx[c] = e; c++;
    }
    /* sort removal indices descending */
    for (int p = 1; p < c; p++) {
        int t = idx[p], q = p - 1;
        while (q >= 0 && idx[q] < t) { idx[q + 1] = idx[q]; q--; }
        idx[q + 1] = t;
    }
    for (int p = 0; p < c; p++) {
        int e = idx[p];
        adjm[eu[e]][ev[e]] = 0;
        eu[e] = eu[M - 1]; ev[e] = ev[M - 1];
        M--;
    }
    int a = n, b = n + 1;
    col[a] = 0; col[b] = 1;
    add_edge(a, b);
    for (int q = 0; q < c; q++) {
        add_edge(a, ys[q]);
        add_edge(xs[q], b);
    }
    n += 2;
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: prog d D seed slice\n"); return 1; }
    DEG = atoi(argv[1]); DIAM = atoi(argv[2]);
    uint64_t seed = strtoull(argv[3], NULL, 10);
    double slice = atof(argv[4]);
    rs = seed * 0x9E3779B97F4A7C15ULL ^ 0x7654321ULL;
    if (rs == 0) rs = 1;
    if (DEG < 1 || DEG > MAXDEG || DIAM < 1) { printf("0 0\n"); return 0; }

    int nn, mm;
    if (scanf("%d %d", &nn, &mm) != 2 || nn <= 0 || nn > MAXN - 2 || mm < 0 || mm > MAXM - 2 * MAXDEG) {
        printf("0 0\n"); return 0;
    }
    n = nn; M = mm;
    for (int e = 0; e < M; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= n || v >= n || u == v) { printf("0 0\n"); return 0; }
        eu[e] = u; ev[e] = v;
    }
    /* 2-colour the input via a symmetric temporary adjacency matrix. */
    for (int e = 0; e < M; e++) { adjm[eu[e]][ev[e]] = 1; adjm[ev[e]][eu[e]] = 1; }
    for (int v = 0; v < n; v++) col[v] = -1;
    int *qu = malloc(sizeof(int) * (size_t)n);
    for (int s = 0; s < n; s++) {
        if (col[s] != -1) continue;
        col[s] = 0;
        int h = 0, tl = 0;
        qu[tl++] = s;
        while (h < tl) {
            int u = qu[h++];
            for (int w = 0; w < n; w++) {
                if (!adjm[u][w]) continue;
                if (col[w] == -1) { col[w] = 1 - col[u]; qu[tl++] = w; }
                else if (col[w] == col[u]) { printf("0 0\n"); return 0; }
            }
        }
    }
    free(qu);
    memset(adjm, 0, sizeof(adjm));
    for (int e = 0; e < M; e++) if (col[eu[e]] != 0) { int t = eu[e]; eu[e] = ev[e]; ev[e] = t; }
    /* degree check */
    for (int v = 0; v < n; v++) dg[v] = 0;
    for (int e = 0; e < M; e++) { dg[eu[e]]++; dg[ev[e]]++; }
    for (int v = 0; v < n; v++) if (dg[v] > DEG) { printf("0 0\n"); return 0; }
    set_adj();

    bestN = n; bestM = M;
    memcpy(beu, eu, sizeof(int) * (size_t)M);
    memcpy(bev, ev, sizeof(int) * (size_t)M);
    if (M == 0 || n < 3) {
        printf("%d %d\n", bestN, bestM);
        for (int e = 0; e < bestM; e++) printf("%d %d\n", beu[e], bev[e]);
        return 0;
    }

    clock_t t0 = clock();
    long cur = cost_fn();
    snapshot();
    long snCost = cur;
    int stall = 0;
    const int STALL = 4000;
    double T = 1.0;
    while (elapsed(t0) < slice) {
        if (cur == 0) {
            if (n > bestN) {
                bestN = n; bestM = M;
                memcpy(beu, eu, sizeof(int) * (size_t)M);
                memcpy(bev, ev, sizeof(int) * (size_t)M);
            }
            if (!grow()) break;
            cur = cost_fn();
            snapshot();
            snCost = cur;
            stall = 0;
            T = 1.0;
            continue;
        }
        if (!swap_move()) continue;
        long nc = cost_fn();
        if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) cur = nc;
        else undo_swap();
        if (cur < snCost) { snCost = cur; snapshot(); stall = 0; }
        else if (++stall > STALL) { restore(); cur = snCost; stall = 0; }
        T = 0.6 * (1.0 - (double)stall / STALL) + 0.05;
    }
    if (cur == 0 && n > bestN) {
        bestN = n; bestM = M;
        memcpy(beu, eu, sizeof(int) * (size_t)M);
        memcpy(bev, ev, sizeof(int) * (size_t)M);
    }
    printf("%d %d\n", bestN, bestM);
    for (int e = 0; e < bestM; e++) printf("%d %d\n", beu[e], bev[e]);
    fflush(stdout);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact constructions (kept for the cases where they apply).
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
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Spare-degree extension (no-op for regular graphs).
# ----------------------------------------------------------------------------

def _two_colour(n, edges):
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
            cand = edges + [(a, b)] + [(a, x) for x in B_sp[:k]] + [(b, y) for y in A_sp[:k]]
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
# Group sampling for the lift phase.
# ----------------------------------------------------------------------------

K2_CHOICES = [1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 21, 24,
              27, 28, 30, 36, 40, 42, 49, 54, 56, 63, 72, 81, 84, 96, 108, 121,
              128, 162, 243]


def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x|_r Z_k2 with order m*k2 >= target, or None."""
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
            return m, k2, 1
    return None


def _lift_phase(best, d, D, rng, end):
    """Voltage-lift search (phase 1). Returns the best valid (n, edges) found."""
    step = 0.08
    while True:
        remaining = end - time.monotonic()
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
            out = lib.run_c(C_LIFT, [d, D, k, m, k2, r, rng.randrange(1, 10 ** 9), f"{slice_s:.2f}"],
                            timeout=slice_s + 10.0)
            n, e = lib.parse_graph_text(out)
        except (RuntimeError, ValueError):
            step = max(0.005, step * 0.7)
            continue
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
            step = min(0.4, step * 1.25)
        else:
            step = max(0.005, step * 0.7)
    return best


def _surgery_phase(best, d, D, rng, end):
    """Graph surgery and annealing (phase 2): grow the explicit graph by edge swaps."""
    slice_s = end - time.monotonic() - 0.5
    if slice_s < 1.0 or best[0] < 4:
        return best
    try:
        out = lib.run_c(C_SURGERY, [d, D, rng.randrange(1, 10 ** 9), f"{slice_s:.2f}"],
                        stdin_graph=best, timeout=slice_s + 10.0)
        n, e = lib.parse_graph_text(out)
    except (RuntimeError, ValueError):
        return best
    if n > best[0] and lib.is_valid(n, e, d, D):
        best = (n, e)
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.9 * time_limit, time_limit - 4.0))
    deadline = start + budget
    lift_end = start + 0.40 * budget
    search_end = start + 0.92 * budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    def adopt(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            adopt(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            adopt(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Phase 1: voltage lifts (known-good baseline).
    if d >= 2:
        best = _lift_phase(best, d, D, rng, lift_end) if D >= 2 else best
        if not lib.is_valid(best[0], best[1], d, D):
            best = lib.haar_graph(d, range(d))

    # Phase 2: surgery on the explicit graph, starting from the phase-1 best.
    if d >= 2:
        try:
            best = _surgery_phase(best, d, D, rng, search_end)
        except Exception:
            pass

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
