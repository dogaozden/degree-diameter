import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# New construction: bi-Cayley (group-based) bipartite graphs.
#
# Let G be a finite group, S a set of d elements. Vertices are A_g and B_h for
# g, h in G, with A_g ~ B_{g s} for s in S. Left multiplication by x maps A_g to
# A_{xg} and B_h to B_{xh} and is an automorphism. So every pair of vertices is
# equivalent to a pair involving A_e or B_e, and the diameter is <= D iff A_e and
# B_e both reach every vertex within D steps. The cost is the number of unreached
# vertices from A_e plus from B_e, so one search step costs two small BFS runs.
#
# Groups: Z_m x|_r Z_k (cyclic when k = 1). The C engine searches S by simulated
# annealing with swap moves. Orders G are tried in ascending order from about
# 0.7 * (Moore bound / 2) up to the Moore bound / 2, so the largest valid
# 2G-vertex graph is kept. Fallbacks: W(q) quadrangle incidence graph (D = 4),
# and K_{d,d}. Every candidate is checked with lib.is_valid before it is kept.
# ----------------------------------------------------------------------------

BICAY_C = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXG 1200
#define MAXD 32

static int G, M, K, R, D, DEG;
static int *mt;
static int *ginv;
static int S[MAXD];
static int inS[MAXG];
static int adj[2 * MAXG][MAXD];
static int distv[2 * MAXG];
static int qv[2 * MAXG];
static uint64_t rs = 88172645463325252ULL;

static uint64_t nxt(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rnd(int k) { return (int)(nxt() % (uint64_t)k); }

static double rnd01(void) {
    return (double)(nxt() >> 11) * (1.0 / 9007199254740992.0);
}

static void build_adj(void) {
    for (int g = 0; g < G; g++)
        for (int j = 0; j < DEG; j++)
            adj[g][j] = G + mt[g * G + S[j]];
    for (int h = 0; h < G; h++)
        for (int j = 0; j < DEG; j++)
            adj[G + h][j] = mt[h * G + ginv[S[j]]];
}

static int reach_count(int src) {
    int N = 2 * G;
    for (int v = 0; v < N; v++) distv[v] = -1;
    int qh = 0, qt = 0;
    distv[src] = 0;
    qv[qt++] = src;
    while (qh < qt) {
        int u = qv[qh++];
        if (distv[u] >= D) continue;
        for (int j = 0; j < DEG; j++) {
            int v = adj[u][j];
            if (distv[v] < 0) {
                distv[v] = distv[u] + 1;
                qv[qt++] = v;
            }
        }
    }
    return qt;
}

static int cost(void) {
    build_adj();
    return (2 * G - reach_count(0)) + (2 * G - reach_count(G));
}

int main(int argc, char **argv) {
    if (argc < 8) {
        printf("FAIL 0\n");
        return 0;
    }
    M = atoi(argv[1]);
    K = atoi(argv[2]);
    R = atoi(argv[3]);
    DEG = atoi(argv[4]);
    D = atoi(argv[5]);
    unsigned long long seed = strtoull(argv[6], NULL, 10);
    double tl = atof(argv[7]);
    G = M * K;
    if (M < 2 || K < 1 || G < 2 || G > MAXG || DEG < 1 || DEG > MAXD || DEG > G || D < 1 || tl <= 0) {
        printf("FAIL 0\n");
        return 0;
    }
    rs ^= (uint64_t)seed * 0xD1B54A32D192ED03ULL + 7ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 10; i++) nxt();

    int *pw = malloc(sizeof(int) * K);
    pw[0] = 1 % M;
    for (int b = 1; b < K; b++) pw[b] = (int)((long long)pw[b - 1] * R % M);

    mt = malloc(sizeof(int) * G * G);
    for (int x = 0; x < G; x++) {
        int a = x / K, b = x % K;
        for (int y = 0; y < G; y++) {
            int c = y / K, d = y % K;
            int aa = (int)(((long long)a + (long long)pw[b] * c) % M);
            mt[x * G + y] = aa * K + (b + d) % K;
        }
    }
    ginv = malloc(sizeof(int) * G);
    for (int x = 0; x < G; x++) {
        ginv[x] = -1;
        for (int y = 0; y < G; y++)
            if (mt[x * G + y] == 0) {
                ginv[x] = y;
                break;
            }
        if (ginv[x] < 0) {
            printf("FAIL 0\n");
            return 0;
        }
    }

    clock_t t0 = clock();
    int bestc = 1 << 30;
    int cur = 0;
    int timeup = 0;
    while (!timeup) {
        memset(inS, 0, sizeof inS);
        for (int j = 0; j < DEG; j++) {
            int x;
            do {
                x = rnd(G);
            } while (inS[x]);
            inS[x] = 1;
            S[j] = x;
        }
        cur = cost();
        if (cur < bestc) bestc = cur;
        long noimp = 0;
        while (cur > 0 && noimp < 20000) {
            double frac = (double)(clock() - t0) / CLOCKS_PER_SEC / tl;
            if (frac >= 1.0) {
                timeup = 1;
                break;
            }
            int j = rnd(DEG);
            int old = S[j];
            int x;
            do {
                x = rnd(G);
            } while (inS[x]);
            S[j] = x;
            inS[old] = 0;
            inS[x] = 1;
            int c2 = cost();
            double T = 0.4 + 1.2 * (1.0 - frac);
            if (c2 <= cur || rnd01() < exp(-(double)(c2 - cur) / T)) {
                cur = c2;
            } else {
                S[j] = old;
                inS[x] = 0;
                inS[old] = 1;
            }
            if (cur < bestc) {
                bestc = cur;
                noimp = 0;
            } else {
                noimp++;
            }
        }
        if (cur == 0) {
            printf("OK");
            for (int j = 0; j < DEG; j++) printf(" %d", S[j]);
            printf("\n");
            return 0;
        }
    }
    printf("FAIL %d\n", bestc);
    return 0;
}
"""


def _groups(G):
    """All (m, k, r) with m * k = G giving Z_m x|_r Z_k (cyclic when k = 1)."""
    out = []
    for k in range(1, 17):
        if k > G or G % k:
            continue
        m = G // k
        if m < 2:
            continue
        if k == 1:
            out.append((m, 1, 1))
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _graph_from(m, k, r, S):
    """Bi-Cayley graph on A_g, B_g (g in the group), with A_g ~ B_{g s} for s in S."""
    G, mul, _ = lib.semidirect_group(m, k, r)
    edges = [(g, G + mul(g, s)) for g in range(G) for s in S]
    return 2 * G, edges


def _level(G, d, D, budget, rng, deadline):
    """Try to find a valid bi-Cayley graph on 2G vertices within the budget."""
    groups = _groups(G)
    if not groups:
        return None
    cyc = [g for g in groups if g[1] == 1]
    rest = [g for g in groups if g[1] != 1]
    rng.shuffle(rest)
    tries = cyc[:1] + rest[:3]
    per = budget / len(tries)
    for m, k, r in tries:
        b = min(per, deadline - time.monotonic())
        if b < 0.2:
            break
        try:
            out = lib.run_c(BICAY_C, [m, k, r, d, D, rng.randrange(1 << 30), f"{b:.2f}"],
                            timeout=b + 5.0)
        except RuntimeError:
            continue
        toks = out.split()
        if len(toks) == d + 1 and toks[0] == "OK":
            S = [int(x) for x in toks[1:]]
            n, e = _graph_from(m, k, r, S)
            if lib.is_valid(n, e, d, D):
                return n, e
    return None


# ----------------------------------------------------------------------------
# Fallback: incidence graph of the generalized quadrangle W(q).
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of W(q): degree q + 1, diameter 4."""
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
    """W(q) for the largest prime power q <= 16 with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    tl = float(time_limit)
    rng = random.Random(seed)

    if d >= 1 and D == 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Calibration: D = 3 with d - 1 a prime power is the Moore-optimal incidence graph.
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1):
        n0, e0 = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(n0, e0, d, D):
            return n0, e0

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Main search: ascending bi-Cayley orders G, so 2G vertices.
    if d >= 3 and D >= 2:
        hi = lib.moore_bound(d, D) // 2
        lo = max(2, int(0.7 * hi))
        level_budget = max(1.0, 0.07 * tl)
        search_end = start + 0.72 * tl
        fails = 0
        G = lo
        while G <= hi and time.monotonic() < search_end and fails < 3:
            res = _level(G, d, D, level_budget, rng, search_end)
            if res is None:
                fails += 1
            else:
                fails = 0
                consider(res[0], res[1])
            G += 1

    # Second fallback for D = 4: generalized quadrangle incidence graph, if time allows.
    if D == 4 and d >= 5 and time.monotonic() < start + 0.8 * tl - 8.0:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
