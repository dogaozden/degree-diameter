import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Engine B: voltage annealing of bi-Cayley-type lifts with K base vertices per
# side over Z_m x|_r Z_k2 (baseline engine that produces the starting graph).
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
# Engine C (new): bipartite edge-swap annealing on a GENERAL graph, not an
# algebraic lift. It starts from a valid graph (stdin), adds vertex pairs up
# to the target order, fills spare degree, then anneals over degree-preserving
# swaps and degree-transfer moves. Cost = number of vertex pairs at distance
# > DIAM, computed by bitset ball expansion. Output is a valid graph (cost 0)
# or "0 0".
#
# Usage: prog d D target_n seed slice_seconds   (graph on stdin, "n m" + edges)
# ----------------------------------------------------------------------------

REPAIR_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define FAIL() do { printf("0 0\n"); return 0; } while (0)

static int DD, DIAM, N, W;
static int *adjl, *deg, *col, *listA, *listB, nA, nB;
static uint8_t *M;
static uint64_t *R1, *R2;
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

static int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void remove_nb(int v, int u) {
    int *L = adjl + (size_t)v * DD;
    for (int k = 0; k < deg[v]; k++) {
        if (L[k] == u) { L[k] = L[deg[v] - 1]; deg[v]--; return; }
    }
}

static void add_edge(int a, int b) {
    adjl[(size_t)a * DD + deg[a]++] = b;
    adjl[(size_t)b * DD + deg[b]++] = a;
    M[(size_t)a * N + b] = 1;
    M[(size_t)b * N + a] = 1;
}

static void del_edge(int a, int b) {
    remove_nb(a, b);
    remove_nb(b, a);
    M[(size_t)a * N + b] = 0;
    M[(size_t)b * N + a] = 0;
}

/* Number of unordered vertex pairs at distance > DIAM. */
static long long cost_fn(void) {
    memset(R1, 0, sizeof(uint64_t) * (size_t)N * W);
    for (int v = 0; v < N; v++) R1[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int lv = 0; lv < DIAM; lv++) {
        for (int v = 0; v < N; v++) {
            uint64_t *dst = R2 + (size_t)v * W;
            memcpy(dst, R1 + (size_t)v * W, sizeof(uint64_t) * W);
            for (int k = 0; k < deg[v]; k++) {
                const uint64_t *s2 = R1 + (size_t)adjl[(size_t)v * DD + k] * W;
                for (int w = 0; w < W; w++) dst[w] |= s2[w];
            }
        }
        uint64_t *t = R1; R1 = R2; R2 = t;
    }
    long long total = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc64(R1[(size_t)v * W + w]);
        total += N - c;
    }
    return total / 2;
}

static void shuffle_list(int *a, int n) {
    for (int i = n - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = a[i]; a[i] = a[j]; a[j] = t;
    }
}

int main(int argc, char **argv) {
    if (argc < 6) FAIL();
    DD = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    int NT = atoi(argv[3]);
    uint64_t seed = strtoull(argv[4], NULL, 10);
    double slice = atof(argv[5]);
    if (DD < 1 || DIAM < 1 || NT < 2 || NT > 4000) FAIL();

    rs = seed * 0x9E3779B97F4A7C15ULL ^ 0x5DEECE66DULL;
    if (rs == 0) rs = 1;

    int n0, m0;
    if (scanf("%d %d", &n0, &m0) != 2) FAIL();
    if (n0 < 1 || n0 > NT || m0 < 0) FAIL();
    N = NT;
    W = (N + 63) / 64;

    int *eu = malloc(sizeof(int) * (size_t)(m0 + 1));
    int *ev = malloc(sizeof(int) * (size_t)(m0 + 1));
    if (!eu || !ev) FAIL();
    for (int i = 0; i < m0; i++) {
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) FAIL();
    }

    adjl = malloc(sizeof(int) * (size_t)N * DD);
    deg = calloc(N, sizeof(int));
    col = malloc(sizeof(int) * N);
    M = calloc((size_t)N * N, 1);
    R1 = malloc(sizeof(uint64_t) * (size_t)N * W);
    R2 = malloc(sizeof(uint64_t) * (size_t)N * W);
    listA = malloc(sizeof(int) * N);
    listB = malloc(sizeof(int) * N);
    int *qbuf = malloc(sizeof(int) * N);
    if (!adjl || !deg || !col || !M || !R1 || !R2 || !listA || !listB || !qbuf) FAIL();

    for (int i = 0; i < m0; i++) {
        int u = eu[i], v = ev[i];
        if (u < 0 || v < 0 || u >= n0 || v >= n0 || u == v) FAIL();
        if (M[(size_t)u * N + v]) FAIL();
        if (deg[u] >= DD || deg[v] >= DD) FAIL();
        add_edge(u, v);
    }

    /* Bipartition: BFS on the input part, alternate colours on new vertices. */
    for (int v = 0; v < N; v++) col[v] = -1;
    for (int s = 0; s < n0; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int qh = 0, qt = 0;
        qbuf[qt++] = s;
        while (qh < qt) {
            int v = qbuf[qh++];
            for (int k = 0; k < deg[v]; k++) {
                int u = adjl[(size_t)v * DD + k];
                if (col[u] < 0) { col[u] = 1 - col[v]; qbuf[qt++] = u; }
                else if (col[u] == col[v]) FAIL();
            }
        }
    }
    for (int j = n0; j < N; j++) col[j] = (j - n0) & 1;
    nA = nB = 0;
    for (int v = 0; v < N; v++) {
        if (col[v] == 0) listA[nA++] = v;
        else listB[nB++] = v;
    }
    if (nA == 0 || nB == 0) FAIL();

    /* Greedy fill of spare degree between deficient A and B vertices. */
    shuffle_list(listA, nA);
    shuffle_list(listB, nB);
    for (int i = 0; i < nA; i++) {
        int a = listA[i];
        if (deg[a] >= DD) continue;
        for (int j = 0; j < nB && deg[a] < DD; j++) {
            int b = listB[j];
            if (deg[b] >= DD || M[(size_t)a * N + b]) continue;
            add_edge(a, b);
        }
    }

    long long cur = cost_fn();
    clock_t t0 = clock();
    double T0 = 2.0, T1 = 0.1, T = T0;

    for (long long it = 0; cur > 0; it++) {
        if ((it & 31) == 0) {
            double el = elapsed(t0);
            if (el >= slice) break;
            double frac = el / slice;
            T = T0 * pow(T1 / T0, frac);
        }
        int mv = rndint(100);

        if (mv < 10) {
            /* Fill move: add an edge between two deficient vertices. */
            int a = listA[rndint(nA)];
            int b = listB[rndint(nB)];
            if (deg[a] < DD && deg[b] < DD && !M[(size_t)a * N + b]) {
                add_edge(a, b);
                cur = cost_fn();
            }
        } else if (mv < 45) {
            /* Transfer move: a deficient A vertex x takes edge (a, b) from a full B vertex b. */
            int x = listA[rndint(nA)];
            if (deg[x] >= DD) continue;
            int b = listB[rndint(nB)];
            if (deg[b] != DD || M[(size_t)x * N + b]) continue;
            int a = adjl[(size_t)b * DD + rndint(DD)];
            del_edge(a, b);
            add_edge(x, b);
            long long nc = cost_fn();
            long long dlt = nc - cur;
            if (dlt <= 0 || rnd01() < exp(-(double)dlt / T)) {
                cur = nc;
            } else {
                del_edge(x, b);
                add_edge(a, b);
            }
        } else {
            /* Degree-preserving swap: (a1,b1),(a2,b2) -> (a1,b2),(a2,b1). */
            int a1 = listA[rndint(nA)];
            int a2 = listA[rndint(nA)];
            if (deg[a1] == 0 || deg[a2] == 0) continue;
            int b1 = adjl[(size_t)a1 * DD + rndint(deg[a1])];
            int b2 = adjl[(size_t)a2 * DD + rndint(deg[a2])];
            if (a1 == a2 || b1 == b2) continue;
            if (M[(size_t)a1 * N + b2] || M[(size_t)a2 * N + b1]) continue;
            del_edge(a1, b1);
            del_edge(a2, b2);
            add_edge(a1, b2);
            add_edge(a2, b1);
            long long nc = cost_fn();
            long long dlt = nc - cur;
            if (dlt <= 0 || rnd01() < exp(-(double)dlt / T)) {
                cur = nc;
            } else {
                del_edge(a1, b2);
                del_edge(a2, b1);
                add_edge(a1, b1);
                add_edge(a2, b2);
            }
        }
    }

    if (cur != 0) FAIL();
    long long cnt = 0;
    for (int i = 0; i < nA; i++) cnt += deg[listA[i]];
    printf("%d %lld\n", N, cnt);
    for (int i = 0; i < nA; i++) {
        int v = listA[i];
        for (int k = 0; k < deg[v]; k++) printf("%d %d\n", v, adjl[(size_t)v * DD + k]);
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
# Spare-degree extension (greedy, keeps validity).
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
# Group sampling for engine B.
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
    deadline = start + budget
    search_deadline = start + 0.9 * budget
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

    # Phase B: voltage-lift annealing produces a strong starting graph.
    phaseB_end = start + 0.35 * (search_deadline - start)
    while True:
        remaining = phaseB_end - time.monotonic()
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

    # Phase C (bold): general-graph edge-swap annealing. Grow the current best
    # graph by one vertex pair at a time and repair it toward diameter D.
    while True:
        remaining = search_deadline - time.monotonic()
        if remaining < 1.5:
            break
        slice_s = min(remaining - 0.5, 12.0)
        target = best[0] + 2
        try:
            out = lib.run_c(
                REPAIR_SOURCE,
                [d, D, target, rng.randrange(1, 10 ** 9), f"{slice_s:.2f}"],
                stdin_graph=best,
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
