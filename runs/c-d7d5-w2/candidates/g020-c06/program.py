import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Stage 1 C engine: simulated annealing over voltages of a bi-Cayley lift over
# Z_m x|_r Z_k2 (element (a, b) coded as a*k2 + b). Unchanged from the parent.
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
# Stage 2 C engine (new): grow a regular bipartite graph by annealing.
#
# Input (stdin): "n m" then m edges u v, with side A = 0..n/2-1 and
# side B = n/2..n-1. The graph must be d-regular and have diameter <= D
# or be close to it.
#
# Loop: anneal with degree-preserving double edge swaps; cost = number of
# unordered vertex pairs at distance > D (bitset BFS from all vertices).
# When cost hits 0, snapshot the graph and add one A-B pair of vertices,
# wired in by d "stealing" operations that keep old degrees fixed. Repeat
# until the slice ends or a stage stalls. Output the largest snapshot.
#
# Usage: prog d D maxA seed slice_seconds
# ----------------------------------------------------------------------------

GROW_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define STAGE_MAX 15000

static int d, D, NA, MAXA, W, bestNA;
static int *adjA, *adjB, *bestA, *act;
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

static inline int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Unordered pairs at distance > D. Vertex ids: A a -> a, B b -> MAXA + b. */
static long long cost(void) {
    int nv = 0;
    for (int a = 0; a < NA; a++) act[nv++] = a;
    for (int b = 0; b < NA; b++) act[nv++] = MAXA + b;
    memset(R1, 0, sizeof(uint64_t) * (size_t)(2 * MAXA) * W);
    for (int i = 0; i < nv; i++) {
        int v = act[i];
        R1[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < D; r++) {
        for (int i = 0; i < nv; i++) {
            int v = act[i];
            uint64_t *dst = R2 + (size_t)v * W;
            memcpy(dst, R1 + (size_t)v * W, sizeof(uint64_t) * W);
            if (v < MAXA) {
                const int *nb = adjA + (size_t)v * d;
                for (int t = 0; t < d; t++) {
                    const uint64_t *s = R1 + (size_t)(MAXA + nb[t]) * W;
                    for (int w = 0; w < W; w++) dst[w] |= s[w];
                }
            } else {
                const int *nb = adjB + (size_t)(v - MAXA) * d;
                for (int t = 0; t < d; t++) {
                    const uint64_t *s = R1 + (size_t)nb[t] * W;
                    for (int w = 0; w < W; w++) dst[w] |= s[w];
                }
            }
        }
        uint64_t *tmp = R1; R1 = R2; R2 = tmp;
    }
    long long bad = 0;
    for (int i = 0; i < nv; i++) {
        const uint64_t *row = R1 + (size_t)act[i] * W;
        int pop = 0;
        for (int w = 0; w < W; w++) pop += pc64(row[w]);
        bad += nv - pop;
    }
    return bad / 2;
}

static void rep_b(int b, int old, int nw) {
    int *p = adjB + (size_t)b * d;
    for (int t = 0; t < d; t++) if (p[t] == old) { p[t] = nw; return; }
}

/* Swap B-endpoints of A-slots (a1,t1) and (a2,t2). Self-inverse on the same slots. */
static void apply_swap(int a1, int t1, int a2, int t2) {
    int b1 = adjA[a1 * d + t1], b2 = adjA[a2 * d + t2];
    adjA[a1 * d + t1] = b2;
    adjA[a2 * d + t2] = b1;
    rep_b(b1, a1, a2);
    rep_b(b2, a2, a1);
    M[a1 * MAXA + b1] = 0;
    M[a2 * MAXA + b2] = 0;
    M[a1 * MAXA + b2] = 1;
    M[a2 * MAXA + b1] = 1;
}

static int propose(int *a1, int *t1, int *a2, int *t2) {
    for (int tries = 0; tries < 50; tries++) {
        int A1 = rndint(NA), A2 = rndint(NA);
        if (A1 == A2) continue;
        int T1 = rndint(d), T2 = rndint(d);
        int b1 = adjA[A1 * d + T1], b2 = adjA[A2 * d + T2];
        if (b1 == b2) continue;
        if (M[A1 * MAXA + b2] || M[A2 * MAXA + b1]) continue;
        *a1 = A1; *t1 = T1; *a2 = A2; *t2 = T2;
        return 1;
    }
    return 0;
}

/* Add one A-B pair (index an = bn = old NA), giving each of them d neighbours
   by stealing edges (a,b) -> (a,bn), (an,b). Old degrees are unchanged. */
static int add_pair(void) {
    if (NA >= MAXA) return 0;
    int an = NA, bn = NA;
    NA++;
    for (int k = 0; k < d; k++) {
        int ok = 0;
        for (int tries = 0; tries < 100000 && !ok; tries++) {
            int a = rndint(an);
            int t = rndint(d);
            int b = adjA[a * d + t];
            if (M[a * MAXA + bn] || M[an * MAXA + b]) continue;
            adjA[a * d + t] = bn;
            rep_b(b, a, an);
            M[a * MAXA + b] = 0;
            M[a * MAXA + bn] = 1;
            M[an * MAXA + b] = 1;
            adjA[an * d + k] = b;
            adjB[bn * d + k] = a;
            ok = 1;
        }
        if (!ok) return 0;
    }
    return 1;
}

static void save_best(void) {
    memcpy(bestA, adjA, sizeof(int) * (size_t)NA * d);
    bestNA = NA;
}

int main(int argc, char **argv) {
    if (argc < 6) { printf("0 0\n"); return 0; }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    MAXA = atoi(argv[3]);
    uint64_t seed = strtoull(argv[4], NULL, 10);
    double slice = atof(argv[5]);
    rs = seed * 0x9E3779B97F4A7C15ULL ^ 0xABCDEFULL;
    if (rs == 0) rs = 1;

    int n, m;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || (n & 1)) { printf("0 0\n"); return 0; }
    int NA0 = n / 2;
    if (d < 1 || D < 1 || MAXA < NA0 || NA0 < d) { printf("0 0\n"); return 0; }

    W = (2 * MAXA + 63) / 64;
    adjA = malloc(sizeof(int) * (size_t)MAXA * d);
    adjB = malloc(sizeof(int) * (size_t)MAXA * d);
    bestA = malloc(sizeof(int) * (size_t)MAXA * d);
    act = malloc(sizeof(int) * (size_t)2 * MAXA);
    M = calloc((size_t)MAXA * MAXA, 1);
    R1 = malloc(sizeof(uint64_t) * (size_t)(2 * MAXA) * W);
    R2 = malloc(sizeof(uint64_t) * (size_t)(2 * MAXA) * W);
    int *degA = calloc(MAXA, sizeof(int));
    int *degB = calloc(MAXA, sizeof(int));
    if (!adjA || !adjB || !bestA || !act || !M || !R1 || !R2 || !degA || !degB) {
        printf("0 0\n");
        return 0;
    }

    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { printf("0 0\n"); return 0; }
        if (u >= NA0 && v < NA0) { int t = u; u = v; v = t; }
        if (!(u >= 0 && u < NA0 && v >= NA0 && v < n)) { printf("0 0\n"); return 0; }
        int a = u, b = v - NA0;
        if (M[a * MAXA + b] || degA[a] >= d || degB[b] >= d) { printf("0 0\n"); return 0; }
        M[a * MAXA + b] = 1;
        adjA[a * d + degA[a]++] = b;
        adjB[b * d + degB[b]++] = a;
    }
    for (int i = 0; i < NA0; i++) if (degA[i] != d) { printf("0 0\n"); return 0; }
    for (int i = 0; i < NA0; i++) if (degB[i] != d) { printf("0 0\n"); return 0; }

    NA = NA0;
    bestNA = 0;
    clock_t t0 = clock();
    long long cur = cost();
    int iter = 0;

    while (elapsed(t0) < slice) {
        if (cur == 0) {
            save_best();
            if (!add_pair()) break;
            cur = cost();
            iter = 0;
            continue;
        }
        if (++iter > STAGE_MAX) break;
        double T = 0.25 + 1.0 * exp(-(double)iter / 2000.0);
        int a1, t1, a2, t2;
        if (!propose(&a1, &t1, &a2, &t2)) continue;
        apply_swap(a1, t1, a2, t2);
        long long nc = cost();
        if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
            cur = nc;
        } else {
            apply_swap(a1, t1, a2, t2);
        }
    }

    if (bestNA == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", 2 * bestNA, bestNA * d);
    for (int a = 0; a < bestNA; a++)
        for (int t = 0; t < d; t++)
            printf("%d %d\n", a, bestNA + bestA[a * d + t]);
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


# ----------------------------------------------------------------------------
# Stage 2 driver: grow a d-regular graph by annealing (new construction).
# ----------------------------------------------------------------------------

def _grow_regular(graph, d, D, seconds, seed):
    """Run GROW_SOURCE on a d-regular bipartite graph. Returns a larger (n, edges) or None."""
    n, edges = graph
    if seconds < 2.0 or not edges:
        return None
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
    if any(x != d for x in deg):
        return None
    col = _two_colour(n, edges)
    if col is None:
        return None
    A = [v for v in range(n) if col[v] == 0]
    B = [v for v in range(n) if col[v] == 1]
    if not A or len(A) != len(B):
        return None
    NA0 = len(A)
    ia = {v: i for i, v in enumerate(A)}
    ib = {v: NA0 + i for i, v in enumerate(B)}
    rel = []
    for u, v in edges:
        if col[u] == 1:
            u, v = v, u
        rel.append((ia[u], ib[v]))
    max_a = NA0 + 60
    try:
        out = lib.run_c(GROW_SOURCE, [d, D, max_a, seed, f"{seconds:.2f}"],
                        stdin_graph=(2 * NA0, rel), timeout=seconds + 10.0)
        n2, e2 = lib.parse_graph_text(out)
    except (RuntimeError, ValueError):
        return None
    if n2 <= n:
        return None
    return n2, e2


# ----------------------------------------------------------------------------
# Greedy spare-degree extension (for irregular valid graphs).
# ----------------------------------------------------------------------------

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
# Stage 1 driver: lift search over semidirect groups.
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


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.9 * time_limit, time_limit - 4.0))
    deadline = start + budget
    lift_deadline = start + 0.5 * budget  # stage 1 gets half, stage 2 the rest
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
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

    # Stage 1: lift search, adaptive growth of the target size.
    step = 0.08
    retry = None
    while True:
        remaining = lift_deadline - time.monotonic()
        if remaining < 1.0:
            break
        slice_s = min(remaining, 10.0)
        if retry is not None:
            k, m, k2, r = retry
            retry = None
            is_retry = True
        else:
            is_retry = False
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
            ok = consider(n, e)
        except ValueError:
            ok = False
        if ok:
            step = min(0.4, step * 1.25)
        elif not is_retry:
            retry = (k, m, k2, r)
        else:
            step = max(0.005, step * 0.7)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))

    # Stage 2 (new): anneal-and-grow from the best regular graph found.
    grow_left = deadline - time.monotonic() - 1.5
    if grow_left >= 2.0:
        try:
            g = _grow_regular(best, d, D, grow_left, rng.randrange(1, 10 ** 9))
        except Exception:
            g = None
        if g is not None:
            consider(g[0], g[1])

    # Spare-degree extension for irregular graphs, with any time left.
    try:
        n2, e2 = _extend_spare(best[0], best[1], d, D, deadline)
        if n2 > best[0] and lib.is_valid(n2, e2, d, D):
            best = (n2, e2)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
