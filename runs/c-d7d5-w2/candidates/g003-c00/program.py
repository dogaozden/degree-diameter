import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C search engine 1: simulated annealing over the voltages of a bi-Cayley lift
# over the group Z_m x|_r Z_k2 (element (a, b) coded as a*k2 + b).
#
# Base graph: K vertices per side, DEG layers, each layer a permutation of
# 0..K-1 (so every vertex has degree DEG). Dart e = l*K + i joins A_i to
# B_{dJ[e]} with voltage dS[e]: A_{i,g} ~ B_{j,g*s} for all g.
# Left multiplication is an automorphism, so the BFS from the 2K
# representatives decides the diameter exactly.
#
# Moves: change a voltage, or swap the targets of two darts in one layer
# (keeps degrees). Cost = unreached (rep, vertex) pairs + duplicate penalty.
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
# C search engine 2 (new): grow a regular bipartite graph by PAIR INSERTION.
#
# Insertion: pick DEG edges (a_i, b_i) with all a_i distinct and all b_i
# distinct. Replace each by (a', b_i) and add (a_i, b'), where a', b' are two
# new vertices (a' on side A, b' on side B). Every degree is preserved, the
# graph stays bipartite, and the order grows by 2.
#
# The new graph usually has diameter > D. Repair: simulated annealing with
# double-edge swaps (a1,b1),(a2,b2) -> (a1,b2),(a2,b1), which keep all degrees
# and bipartiteness. Cost = ordered vertex pairs at distance > D. The distance
# test uses bitsets: after D rounds of OR-ing neighbour reach-sets, every
# vertex must reach all N vertices. Success means cost 0, so the output is
# always valid. On failure the state is restored from the last valid graph.
#
# Usage: prog d D seed slice_seconds [iters_per_pair] [max_added_pairs]
# stdin: a valid d-regular bipartite graph ("n m" + edges). Prints the largest
# valid graph found (or the input graph if nothing was added), or "0 0".
# ----------------------------------------------------------------------------

GROW_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

static int DEG, DIAM, N, NE, CAPN, CAPE, W, mstamp = 0;
static int *eu, *ev, *adj, *cnt, *mkA, *mkB, *col, *qb;
static int *saveU, *saveV, saveN, saveNE;
static uint64_t *bufA, *bufB;
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

static void build_adj(void) {
    memset(cnt, 0, sizeof(int) * (size_t)N);
    for (int e = 0; e < NE; e++) {
        int a = eu[e], b = ev[e];
        adj[(size_t)a * DEG + cnt[a]++] = b;
        adj[(size_t)b * DEG + cnt[b]++] = a;
    }
}

/* Ordered pairs at distance > DIAM (0 iff valid). Uses the current edges. */
static long long cost_fn(void) {
    build_adj();
    size_t words = (size_t)N * W;
    memset(bufA, 0, sizeof(uint64_t) * words);
    for (int v = 0; v < N; v++) bufA[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    uint64_t *cur = bufA, *nxt = bufB;
    for (int lv = 0; lv < DIAM; lv++) {
        for (int v = 0; v < N; v++) {
            uint64_t *o = nxt + (size_t)v * W;
            memcpy(o, cur + (size_t)v * W, sizeof(uint64_t) * W);
            for (int t = 0; t < DEG; t++) {
                const uint64_t *s = cur + (size_t)adj[(size_t)v * DEG + t] * W;
                for (int w = 0; w < W; w++) o[w] |= s[w];
            }
        }
        uint64_t *tmp = cur; cur = nxt; nxt = tmp;
    }
    long long reached = 0;
    for (size_t i = 0; i < words; i++) reached += popc64(cur[i]);
    return (long long)N * N - reached;
}

static int has_edge(int a, int b) {
    for (int t = 0; t < DEG; t++)
        if (adj[(size_t)a * DEG + t] == b) return 1;
    return 0;
}

static void save_state(void) {
    memcpy(saveU, eu, sizeof(int) * (size_t)NE);
    memcpy(saveV, ev, sizeof(int) * (size_t)NE);
    saveN = N;
    saveNE = NE;
}

static void restore_state(void) {
    NE = saveNE;
    N = saveN;
    memcpy(eu, saveU, sizeof(int) * (size_t)NE);
    memcpy(ev, saveV, sizeof(int) * (size_t)NE);
}

/* Insert a pair of new vertices (see the header comment). Returns 1 on success. */
static int add_pair(void) {
    if (N + 2 > CAPN || NE + DEG > CAPE) return 0;
    int ch[64];
    int nch = 0;
    mstamp++;
    long long tries = 0;
    while (nch < DEG && tries < 200000) {
        tries++;
        int e = rndint(NE);
        int a = eu[e], b = ev[e];
        if (mkA[a] == mstamp || mkB[b] == mstamp) continue;
        mkA[a] = mstamp;
        mkB[b] = mstamp;
        ch[nch++] = e;
    }
    if (nch < DEG) return 0;
    int ap = N, bp = N + 1;
    for (int i = 0; i < DEG; i++) {
        int e = ch[i];
        int a = eu[e];
        eu[e] = ap;          /* edge (a', b_i), ev[e] stays b_i */
        eu[NE + i] = a;      /* edge (a_i, b') */
        ev[NE + i] = bp;
    }
    N += 2;
    NE += DEG;
    return 1;
}

/* Double-edge-swap annealing. Returns 0 when valid, else the final cost. */
static long long anneal(int iters, clock_t t0, double slice) {
    long long cur = cost_fn();
    if (cur == 0) return 0;
    for (int it = 0; it < iters; it++) {
        if ((it & 7) == 0 && elapsed(t0) >= slice) break;
        double T = 20.0 * (1.0 - (double)it / iters) + 1.0;
        build_adj();
        int e1 = rndint(NE), e2 = rndint(NE);
        if (e1 == e2) continue;
        int a1 = eu[e1], b1 = ev[e1], a2 = eu[e2], b2 = ev[e2];
        if (a1 == a2 || b1 == b2) continue;
        if (has_edge(a1, b2) || has_edge(a2, b1)) continue;
        ev[e1] = b2;
        ev[e2] = b1;
        long long nc = cost_fn();
        long long delta = nc - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cur = nc;
            if (cur == 0) return 0;
        } else {
            ev[e1] = b1;
            ev[e2] = b2;
        }
    }
    return cur;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed slice [iters] [maxadd]\n");
        return 1;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t seed = strtoull(argv[3], NULL, 10);
    double slice = atof(argv[4]);
    int iters = argc > 5 ? atoi(argv[5]) : 2500;
    int maxAdd = argc > 6 ? atoi(argv[6]) : 60;
    if (DEG < 1 || DEG > 60 || DIAM < 1 || iters < 1 || maxAdd < 0) {
        printf("0 0\n");
        return 0;
    }
    rs = seed * 0x9E3779B97F4A7C15ULL ^ 0x7654321ULL;
    if (rs == 0) rs = 1;

    int n0, m0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 <= 0 || m0 <= 0) {
        printf("0 0\n");
        return 0;
    }
    CAPN = n0 + 2 * maxAdd;
    CAPE = m0 + DEG * maxAdd;
    W = (CAPN + 63) / 64;

    eu = malloc(sizeof(int) * CAPE);
    ev = malloc(sizeof(int) * CAPE);
    saveU = malloc(sizeof(int) * CAPE);
    saveV = malloc(sizeof(int) * CAPE);
    adj = malloc(sizeof(int) * (size_t)CAPN * DEG);
    cnt = malloc(sizeof(int) * CAPN);
    mkA = calloc(CAPN, sizeof(int));
    mkB = calloc(CAPN, sizeof(int));
    col = malloc(sizeof(int) * CAPN);
    qb = malloc(sizeof(int) * CAPN);
    bufA = malloc(sizeof(uint64_t) * (size_t)CAPN * W);
    bufB = malloc(sizeof(uint64_t) * (size_t)CAPN * W);
    if (!eu || !ev || !saveU || !saveV || !adj || !cnt || !mkA || !mkB || !col || !qb || !bufA || !bufB) {
        printf("0 0\n");
        return 0;
    }

    /* Read and validate: simple, d-regular, bipartite. */
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { printf("0 0\n"); return 0; }
        if (u < 0 || v < 0 || u >= n0 || v >= n0 || u == v) { printf("0 0\n"); return 0; }
        eu[i] = u;
        ev[i] = v;
    }
    memset(cnt, 0, sizeof(int) * (size_t)n0);
    for (int i = 0; i < m0; i++) { cnt[eu[i]]++; cnt[ev[i]]++; }
    for (int v = 0; v < n0; v++) if (cnt[v] != DEG) { printf("0 0\n"); return 0; }
    for (int i = 0; i < m0; i++) {
        int u = eu[i], v = ev[i];
        adj[(size_t)u * DEG + 0] = adj[(size_t)u * DEG + 0];
    }
    /* BFS colouring with a temporary adjacency. */
    memset(cnt, 0, sizeof(int) * (size_t)n0);
    for (int i = 0; i < m0; i++) {
        int u = eu[i], v = ev[i];
        adj[(size_t)u * DEG + cnt[u]++] = v;
        adj[(size_t)v * DEG + cnt[v]++] = u;
    }
    for (int v = 0; v < n0; v++) col[v] = -1;
    for (int s = 0; s < n0; s++) {
        if (col[s] != -1) continue;
        int qh = 0, qt = 0;
        col[s] = 0;
        qb[qt++] = s;
        while (qh < qt) {
            int u = qb[qh++];
            for (int t = 0; t < DEG; t++) {
                int v = adj[(size_t)u * DEG + t];
                if (col[v] == -1) {
                    col[v] = 1 - col[u];
                    qb[qt++] = v;
                } else if (col[v] == col[u]) {
                    printf("0 0\n");
                    return 0;
                }
            }
        }
    }
    /* Orient each edge so eu is on side 0. */
    for (int i = 0; i < m0; i++) {
        if (col[eu[i]] != 0) {
            int t = eu[i]; eu[i] = ev[i]; ev[i] = t;
        }
    }
    N = n0;
    NE = m0;

    if (cost_fn() != 0) {
        printf("0 0\n");
        return 0;
    }
    save_state();

    clock_t t0 = clock();
    while (elapsed(t0) < slice && N + 2 <= CAPN) {
        restore_state();
        if (!add_pair()) continue;
        long long r = anneal(iters, t0, slice);
        if (r == 0) save_state();
    }
    restore_state();

    printf("%d %d\n", N, NE);
    for (int e = 0; e < NE; e++) printf("%d %d\n", eu[e], ev[e]);
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
# Group sampling and helpers.
# ----------------------------------------------------------------------------

def _sample_group(target, rng):
    """Return (m, k2, r) describing Z_m x|_r Z_k2 with order m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, -(-target // k2))
        r = 1  # r = 1 is the direct product, always valid
        if k2 > 1 and m > 2:
            cands = [c for c in range(2, m) if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m]
            if cands:
                r = rng.choice(cands)
        return m, k2, r
    return None


def _is_regular(n, edges, d):
    """True if every vertex of the graph has degree exactly d."""
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
    return all(x == d for x in deg)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    # Keep a margin for compiling (cached after the first call), process
    # start-up and parsing.
    budget = max(1.0, min(0.9 * time_limit, time_limit - 4.0))
    deadline = start + budget
    # Lift search gets 60% of the budget; the rest grows the best graph.
    lift_deadline = start + 0.6 * budget
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

        # Araujo-Pardo & Lopez record for D = 3, d = q + 2 with q a prime power.
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

    # Phase 1: anneal voltages of bi-Cayley lifts (as before), up to lift_deadline.
    while True:
        remaining = lift_deadline - time.monotonic()
        if remaining < 1.0:
            break
        slice_s = min(remaining, 15.0)
        k = rng.choice([1, 1, 1, 2, 2, 3])
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

    # Phase 2 (new): pair insertion plus annealing repair, starting from the
    # best d-regular graph. Each success adds two vertices; the C engine keeps
    # its last valid state, so the output is always valid.
    if D >= 2 and best[0] > 2 and _is_regular(best[0], best[1], d):
        remaining = deadline - time.monotonic() - 1.0
        if remaining > 3.0:
            try:
                out = lib.run_c(
                    GROW_SOURCE,
                    [d, D, rng.randrange(1, 10 ** 9), f"{remaining:.2f}", 2500, 60],
                    stdin_graph=best,
                    timeout=remaining + 10.0,
                )
                n2, e2 = lib.parse_graph_text(out)
                consider(n2, e2)
            except (RuntimeError, ValueError):
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
