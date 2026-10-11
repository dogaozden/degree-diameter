import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bi-Cayley (Haar) graphs over Z_m.
#
# Vertices a_i = i and b_j = m + j. Connection set S (|S| = d, 0 in S) gives
# edges a_i -- b_{i+s}. Translations act on each side, so the diameter is at
# most D iff every vertex is within distance D of a_0 and of b_0. The cost is
# the number of vertices missed by those two radius-D BFS balls, so one
# evaluation is O(m d). Simulated annealing searches S for the current m, and
# m is raised after every success.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXM 4000
#define MAXD 32
#define RESTART_STEPS 150000

static int d, D, m;
static int S[MAXD];
static int bestS[MAXD];
static unsigned char inS[MAXM];
static int vis[2 * MAXM];
static int qbuf[2 * MAXM];
static int gen = 1;
static uint64_t rs = 1;
static double t_limit;

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

static double now(void) { return (double)clock() / CLOCKS_PER_SEC; }

static void clear_inS(void) {
    for (int k = 0; k < d; k++) inS[S[k]] = 0;
}

/* Number of vertices reached from src within distance D. */
static int bfs_reached(int src) {
    gen++;
    int qh = 0, qt = 0;
    vis[src] = gen;
    qbuf[qt++] = src;
    for (int lvl = 0; lvl < D && qh < qt; lvl++) {
        int end = qt;
        while (qh < end) {
            int x = qbuf[qh++];
            if (x < m) {
                for (int k = 0; k < d; k++) {
                    int y = m + (x + S[k]) % m;
                    if (vis[y] != gen) {
                        vis[y] = gen;
                        qbuf[qt++] = y;
                    }
                }
            } else {
                int j = x - m;
                for (int k = 0; k < d; k++) {
                    int y = (j - S[k] + m) % m;
                    if (vis[y] != gen) {
                        vis[y] = gen;
                        qbuf[qt++] = y;
                    }
                }
            }
        }
    }
    return qt;
}

static long long cost(void) {
    long long a = 2LL * m - bfs_reached(0);
    long long b = 2LL * m - bfs_reached(m);
    return a + b;
}

static void random_start(void) {
    S[0] = 0;
    inS[0] = 1;
    for (int k = 1; k < d; k++) {
        int v;
        do {
            v = 1 + rnd(m - 1);
        } while (inS[v]);
        S[k] = v;
        inS[v] = 1;
    }
}

/* Anneal S for modulus mm until cost 0 (returns 1, S valid) or time runs out (returns 0). */
static int anneal(int mm) {
    clear_inS();
    m = mm;
    if (m < d + 1) return 0;
    while (now() < t_limit) {
        clear_inS();
        random_start();
        long long cur = cost();
        if (cur == 0) return 1;
        for (long st = 0; st < RESTART_STEPS; st++) {
            if ((st & 127) == 0 && now() >= t_limit) {
                clear_inS();
                return 0;
            }
            double T = 1.5 * (1.0 - (double)st / RESTART_STEPS) + 0.08;
            int i = 1 + rnd(d - 1);
            int v;
            do {
                v = 1 + rnd(m - 1);
            } while (inS[v]);
            int old = S[i];
            inS[old] = 0;
            inS[v] = 1;
            S[i] = v;
            long long c2 = cost();
            long long dl = c2 - cur;
            if (dl <= 0 || rnd01() < exp(-(double)dl / T)) {
                cur = c2;
                if (cur == 0) return 1;
            } else {
                inS[v] = 0;
                inS[old] = 1;
                S[i] = old;
            }
        }
    }
    clear_inS();
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 6) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    int m0 = atoi(argv[5]);
    if (d < 2 || d > MAXD || D < 1 || tl <= 0) {
        printf("0 0\n");
        return 0;
    }
    rs = seed * 0x9E3779B97F4A7C15ULL + 777ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) nextr();

    t_limit = now() + tl;
    int bestm = 0;
    int mm = m0;
    if (mm < d + 1) mm = d + 1;
    while (mm < MAXM / 2 - 1 && now() < t_limit) {
        if (!anneal(mm)) break;
        bestm = mm;
        memcpy(bestS, S, sizeof S);
        mm++;
    }

    if (bestm == 0) {
        printf("0 0\n");
        return 0;
    }
    int bm = bestm;
    printf("%d %d\n", 2 * bm, bm * d);
    for (int i = 0; i < bm; i++)
        for (int k = 0; k < d; k++)
            printf("%d %d\n", i, bm + (i + bestS[k]) % bm);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions: generalized quadrangle fallback and glue.
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
    """W(q) for the largest prime power q with q + 1 <= d (q <= 16)."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _saturate_edges(n, edges, d, rng):
    """Greedily join deficient opposite-side vertices in random order."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    existing = set()
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
        existing.add((min(u, v), max(u, v)))
    deg = [len(a) for a in adj]
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


def build(d, D, seed, time_limit):
    start = time.monotonic()
    tl = float(time_limit)
    rng = random.Random(seed)

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Safe fallback: K_{d,d}, valid for D >= 2 (and for D = 1 handled above).
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

    # Quadrangle fallback for D >= 4, plus a saturated variant.
    if D >= 4 and d >= 3:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            consider(gq[0], _saturate_edges(gq[0], gq[1], d, rng))

    # Main search: bi-Cayley (Haar) annealing in C, climbing m while it succeeds.
    c_end = start + 0.85 * tl - 1.5
    budget = c_end - time.monotonic()
    if budget >= 2.0 and d >= 2 and D >= 2:
        moore = lib.moore_bound(d, D)
        mstart = max(d + 1, int(0.72 * moore / 2))
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", mstart],
                            stdin_graph=None, timeout=budget + 5.0)
            n2, e2 = lib.parse_graph_text(out)
            consider(n2, e2)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
