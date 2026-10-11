"""Bi-Cayley (Haar-type) annealing over semidirect groups, with a new search core.

Python keeps a valid fallback (K_{d,d}, or a known construction for D = 3 or 4) and
calls the C engine with a lower bound on the group order. The C engine works on a
different family from the previous voltage-lift search: a bipartite graph on A = G and
B = G, with A_g adjacent to B_{g s} for s in a set S of d distinct elements of a group G.
Left multiplication is an automorphism, so the diameter is <= D iff a BFS of depth D from
A_identity and from B_identity reaches everything. S is annealed to minimise the number of
unreached pairs. Groups are semidirect products Z_m x|_r Z_k (r^k = 1 mod m, gcd(r, m) = 1),
sampled freshly for each attempt. The group order G climbs by one each time a valid set S
is found. Python re-checks every output with lib.is_valid and keeps the larger of the two graphs.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Bi-Cayley bipartite search.
 *
 * Usage:   prog d D seed time_limit [G_hint]
 * stdin is drained and ignored.
 * stdout:  "n m" then m lines "u v" for the largest valid bi-Cayley graph found,
 *          or K_{d,d} if none is found.
 *
 * Graph: group G = Z_m x|_r Z_k (element a*k+b), vertices A_g = g and B_h = G + h,
 * with A_g ~ B_{g*s} for s in S (|S| = d, distinct). Degree d on both sides, bipartite.
 * Diameter <= D iff BFS of depth D from A_0 and from B_0 reaches everything.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXG 512
#define MAXD 16
#define MAXV (2 * MAXG)

static int d, D;
static double t_end;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rng_state = 88172645463325252ULL;
static uint64_t rnd(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return rng_state;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static long powmod(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static long moore_bound(void) {
    if (D <= 0 || d <= 0) return 1;
    if (d == 1) return 2;
    if (d == 2) return 2L * D;
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 100000000L) break;
    }
    return 2 * s;
}

/* ------------------------------------------------------------ groups */

static int GM, GK2, GORD;
static int RP[MAXG];
static int MT[MAXG][MAXG];
static int INV[MAXG];

static void build_group(int m, int k2, int r) {
    GM = m;
    GK2 = k2;
    GORD = m * k2;
    RP[0] = 1 % m;
    for (int b = 1; b < k2; b++) RP[b] = (int)((long)RP[b - 1] * r % m);
    for (int x = 0; x < GORD; x++)
        for (int y = 0; y < GORD; y++) {
            int a = x / GK2, b = x % GK2, c = y / GK2, e = y % GK2;
            MT[x][y] = (int)(((long)a + (long)RP[b] * c) % GM) * GK2 + (b + e) % GK2;
        }
    for (int x = 0; x < GORD; x++)
        for (int y = 0; y < GORD; y++)
            if (MT[x][y] == 0) INV[x] = y;
}

/* Random semidirect group of order G. r = 1 (direct product) is always valid. */
static void sample_group(int G, int *om, int *ok2, int *orr) {
    int divs[64], nd = 0;
    for (int m = 1; m <= G && nd < 64; m++)
        if (G % m == 0) divs[nd++] = m;
    int m = divs[rndint(nd)];
    int k2 = G / m;
    int r = 1 % m;
    if (m > 2 && k2 > 1 && rnd01() < 0.7) {
        for (int t = 0; t < 200; t++) {
            int c = 1 + rndint(m - 1);
            if (gcd_i(c, m) == 1 && powmod(c, k2, m) == 1 % m) { r = c; break; }
        }
    }
    if (m == 1) r = 0;
    *om = m;
    *ok2 = k2;
    *orr = r;
}

/* ------------------------------------------------------------ bi-Cayley core */

static int SS[MAXD];

static int inS(int t, int n) {
    for (int i = 0; i < n; i++)
        if (SS[i] == t) return 1;
    return 0;
}

static inline int nb(int v, int i) {
    if (v < GORD) return GORD + MT[v][SS[i]];
    return MT[v - GORD][INV[SS[i]]];
}

static int VIS[MAXV], VST = 0, QU[MAXV];

/* Number of vertices within distance D of src (including src). */
static int reach(int src) {
    VST++;
    int head = 0, tail = 0;
    VIS[src] = VST;
    QU[tail++] = src;
    for (int depth = 0; depth < D && head < tail; depth++) {
        int end = tail;
        while (head < end) {
            int u = QU[head++];
            for (int i = 0; i < d; i++) {
                int v = nb(u, i);
                if (VIS[v] != VST) { VIS[v] = VST; QU[tail++] = v; }
            }
        }
    }
    return tail;
}

/* Unreached (source, vertex) pairs from A_0 and B_0. Zero means diameter <= D. */
static long cost_fn(void) {
    int N = 2 * GORD;
    return (long)(N - reach(0)) + (long)(N - reach(GORD));
}

/* Anneal the connection set S (d distinct elements of the current group). */
static int anneal(long steps) {
    int G = GORD;
    for (int i = 0; i < d; i++) {
        int t;
        do { t = rndint(G); } while (inS(t, i));
        SS[i] = t;
    }
    long c = cost_fn();
    for (long s = 0; s < steps && c > 0; s++) {
        if ((s & 63) == 0 && now() > t_end) return 0;
        double T = 1.5 * (1.0 - (double)s / (double)steps) + 0.05;
        int i = rndint(d);
        int t = rndint(G);
        if (inS(t, d)) continue;
        int old = SS[i];
        SS[i] = t;
        long c2 = cost_fn();
        if (c2 <= c || rnd01() < exp(-(double)(c2 - c) / T)) c = c2;
        else SS[i] = old;
    }
    return c == 0;
}

/* ------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [G_hint]\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long hint = argc > 5 ? atol(argv[5]) : 1;

    int ch;
    while ((ch = getchar()) != EOF) { }

    double t0 = now();
    t_end = t0 + limit * 0.9;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 1 || d > MAXD) { printf("1 0\n"); return 0; }
    if (d == 1 || D < 2) { printf("2 1\n0 1\n"); return 0; }

    long moore = moore_bound();
    int bestG = 0, bm = 0, bk2 = 0, br = 0;
    int bestS[MAXD];

    long G = hint;
    if (G < d) G = d;
    int fails = 0;
    while (now() < t_end) {
        if (2L * G > moore || G > MAXG) break;
        int m, k2, r;
        sample_group((int)G, &m, &k2, &r);
        build_group(m, k2, r);
        long steps = 20000 + rndint(20000) + (long)fails * 500;
        if (steps > 300000) steps = 300000;
        if (anneal(steps)) {
            bestG = (int)G;
            bm = m;
            bk2 = k2;
            br = r;
            memcpy(bestS, SS, sizeof(int) * d);
            G++;
            fails = 0;
        } else {
            fails++;
        }
    }

    if (bestG == 0) {
        int n = 2 * d;
        printf("%d %d\n", n, d * d);
        for (int a = 0; a < d; a++)
            for (int b = 0; b < d; b++) printf("%d %d\n", a, d + b);
        return 0;
    }

    build_group(bm, bk2, br);
    memcpy(SS, bestS, sizeof(int) * d);
    long m_edges = (long)bestG * d;
    printf("%d %ld\n", 2 * bestG, m_edges);
    for (int g = 0; g < bestG; g++)
        for (int i = 0; i < d; i++)
            printf("%d %d\n", g, bestG + MT[g][SS[i]]);
    return 0;
}
'''


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4, degree q+1."""
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


def known_start(d, D):
    """Best known construction Python can build directly for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)
    if D == 4:
        for q in range(min(d - 1, 7), 1, -1):
            if lib.is_prime_power(q) and q + 1 <= d:
                return _gq_w(q)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))          # K_{d,d}: valid for D >= 2
    try:
        start = known_start(d, D)
    except (ValueError, RuntimeError):
        start = None
    if start is not None and start[0] > best[0] and lib.is_valid(start[0], start[1], d, D):
        best = start

    if best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if budget < 0.5:
        return best
    hint = max(d, best[0] // 2)
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), hint],
                         stdin_graph=None, timeout=budget + 5)
        n, edges = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)
    except (RuntimeError, ValueError, OSError):
        pass
    return best
