import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing over connection sets of Haar graphs H(M, S).
#
# H(M, S) is bipartite with parts a_i, b_j (i, j in Z_M), and a_i ~ b_{i+s} for
# s in S, |S| = d. The shifts and the swap a_i <-> b_{-i} are automorphisms, so
# the graph is valid iff a_0 and b_0 both reach everything within D steps.
# Cost = number of vertices not within D of a_0, plus those not within D of b_0.
# For each M we search S by annealing; M is grown by bisection between the
# largest success and the smallest failure. The output is always a valid
# Haar graph (M = d, S = all residues, is K_{d,d}, which is valid for D >= 2).
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXM 4000
#define MAXV (2 * MAXM)
#define DMAX 64

static int d, D, M, NV;
static int S[DMAX];
static int bestS[DMAX];
static int bestM;
static unsigned char inS[MAXM];
static int distv[MAXV], stampv[MAXV], qbuf[MAXV];
static int stampCur = 0;
static uint64_t rs = 1;
static clock_t t0;

static uint64_t nextr(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rnd(int k) { return (int)(nextr() % (uint64_t)k); }

static double rnd01(void) {
    return (double)(nextr() >> 11) * (1.0 / 9007199254740992.0);
}

static double elapsed(void) {
    return (double)(clock() - t0) / CLOCKS_PER_SEC;
}

/* Number of vertices NOT within distance D of src. */
static int bfs_bad(int src) {
    stampCur++;
    int qh = 0, qt = 0;
    qbuf[qt++] = src;
    stampv[src] = stampCur;
    distv[src] = 0;
    while (qh < qt) {
        int u = qbuf[qh++];
        if (distv[u] >= D) continue;
        int nd = distv[u] + 1;
        if (u < M) {
            for (int k = 0; k < d; k++) {
                int v = M + (u + S[k]) % M;
                if (stampv[v] != stampCur) {
                    stampv[v] = stampCur;
                    distv[v] = nd;
                    qbuf[qt++] = v;
                }
            }
        } else {
            int j = u - M;
            for (int k = 0; k < d; k++) {
                int v = (j - S[k] + M) % M;
                if (stampv[v] != stampCur) {
                    stampv[v] = stampCur;
                    distv[v] = nd;
                    qbuf[qt++] = v;
                }
            }
        }
    }
    return NV - qt;
}

static long long cost(void) {
    return (long long)bfs_bad(0) + (long long)bfs_bad(M);
}

static void init_state(void) {
    for (int i = 0; i < M; i++) inS[i] = 0;
    S[0] = 0;
    inS[0] = 1;
    int k = 1;
    while (k < d) {
        int x = 1 + rnd(M - 1);
        if (!inS[x]) {
            inS[x] = 1;
            S[k++] = x;
        }
    }
}

/* Returns 1 if a valid S for the current M was found before `end` (CPU seconds). */
static int attempt(double end) {
    NV = 2 * M;
    init_state();
    long long c = cost();
    double T = 0.7;
    long it = 0;
    while (c > 0) {
        if ((it & 127) == 0 && elapsed() >= end) return 0;
        it++;
        int i = 1 + rnd(d - 1);
        int x = -1;
        for (int t = 0; t < 64; t++) {
            int y = rnd(M);
            if (!inS[y]) {
                x = y;
                break;
            }
        }
        if (x < 0) continue;
        int old = S[i];
        inS[old] = 0;
        inS[x] = 1;
        S[i] = x;
        long long c2 = cost();
        long long dl = c2 - c;
        if (dl <= 0 || rnd01() < exp(-(double)dl / T)) {
            c = c2;
        } else {
            inS[x] = 0;
            inS[old] = 1;
            S[i] = old;
        }
    }
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double total = atof(argv[4]);
    if (d < 2 || d > DMAX || D < 1 || total <= 0) {
        printf("0 0\n");
        return 0;
    }
    rs = seed * 0x9E3779B97F4A7C15ULL + 1234567ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) nextr();
    t0 = clock();

    int lo = d, hi = 0;
    bestM = d;
    for (int k = 0; k < d; k++) bestS[k] = k;

    int m = lo + (lo / 50 > 1 ? lo / 50 : 1);
    while (elapsed() < total && m < MAXM) {
        M = m;
        double cap = 0.12 * total;
        if (cap < 1.0) cap = 1.0;
        double end = elapsed() + cap;
        if (end > total) end = total;
        int ok = attempt(end);
        if (ok) {
            lo = m;
            bestM = m;
            memcpy(bestS, S, sizeof(int) * d);
            if (hi <= lo) hi = 0;
            if (hi == 0) {
                m = lo + (lo / 50 > 1 ? lo / 50 : 1);
            } else {
                m = (hi - lo > 1) ? (lo + hi) / 2 : hi;
            }
        } else {
            if (hi == 0 || m < hi) hi = m;
            m = (hi - lo > 1) ? (lo + hi) / 2 : hi;
        }
    }

    int n = 2 * bestM;
    int me = bestM * d;
    printf("%d %d\n", n, me);
    for (int i = 0; i < bestM; i++)
        for (int k = 0; k < d; k++)
            printf("%d %d\n", i, bestM + (i + bestS[k]) % bestM);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions and glue.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q).

    Degree q + 1, diameter 4, order 2(q+1)(q^2+1).
    """
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
    """W(q) incidence graph for the largest prime power q <= 9 with q + 1 <= d."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _saturate_edges(n, edges, d, rng):
    """Greedily join deficient opposite-side vertices in random order (keeps diameter and bipartiteness)."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    existing = set()
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
        existing.add((min(u, v), max(u, v)))
    deg = [len(a) for a in adj]
    color = lib.adjacency(n, edges)  # placeholder to keep names aligned
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
    left = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in left for b in right
             if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return edges


def _run_haar(d, D, seed, budget):
    """Run the C Haar-graph annealer for `budget` seconds and parse its output."""
    out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                    timeout=budget + 8.0)
    return lib.parse_graph_text(out)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    tl = float(time_limit)
    end = start + 0.85 * tl - 1.0
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Calibration: D = 3 with d - 1 a prime power is the Moore-optimal incidence graph.
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1):
        n0, e0 = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(n0, e0, d, D):
            return n0, e0

    # Cheap structured candidates.
    if D == 3:
        qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)]
        if qs:
            pn, pe = lib.projective_plane_incidence(qs[0])
            consider(pn, pe)

    if D == 4 and d >= 3:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            sn, se = gq[0], _saturate_edges(gq[0], gq[1], d, rng)
            consider(sn, se)

    # Main bold search: cyclic Haar graphs with a C-side annealed connection set.
    if d >= 2:
        budget = end - time.monotonic() - 2.0
        if budget >= 2.0:
            try:
                n2, e2 = _run_haar(d, D, seed, budget)
                consider(n2, e2)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
