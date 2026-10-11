"""Cyclic Haar-graph search: a different family from the voltage-lift parent.

A Haar graph H(Z_m, S) has parts A = {a_i} and B = {b_j}, with a_i ~ b_{i+s} for s in S.
It is d-regular and bipartite when |S| = d, with order 2m. Translations act transitively on
each side, so the diameter is <= D iff BFS of depth D from a_0 and from b_0 reaches everything.
C searches for S by hill-climbing the number of unreached vertices, and it raises m while
it succeeds. Python keeps the best known construction as a fallback, compares against the
result, and validates before returning.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Haar-graph search over Z_m.
 * Usage: prog d D seed time_limit
 * Output: "n m" then edges of the largest valid Haar graph found (K_{d,d} if nothing better).
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXM 2048
#define MAXD 32

static int d, D;
static double t_end;
static uint64_t rs = 88172645463325252ULL;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

/* Moore bound for bipartite graphs with max degree d and diameter D. */
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

static int M;               /* current group order */
static int S[MAXD];         /* connection set, d distinct residues mod M */
static int seen[2 * MAXM];
static int stamp_ = 0;
static int Q[2 * MAXM];

/* Number of vertices within distance D of src in the Haar graph (vertices 0..M-1 are A, M..2M-1 are B). */
static int reach(int src) {
    int st = ++stamp_;
    int head = 0, tail = 0;
    seen[src] = st;
    Q[tail++] = src;
    for (int depth = 0; depth < D; depth++) {
        int end = tail;
        if (head == end) break;
        while (head < end) {
            int u = Q[head++];
            if (u < M) {
                for (int k = 0; k < d; k++) {
                    int v = M + (u + S[k]) % M;
                    if (seen[v] != st) { seen[v] = st; Q[tail++] = v; }
                }
            } else {
                int j = u - M;
                for (int k = 0; k < d; k++) {
                    int v = (j - S[k] + M) % M;
                    if (seen[v] != st) { seen[v] = st; Q[tail++] = v; }
                }
            }
        }
    }
    return tail;
}

/* Unreached pairs (a_0 and b_0 against all vertices). Zero means diameter <= D. */
static long cost(void) {
    long a = 2L * M - reach(0);
    long b = 2L * M - reach(M);
    return a + b;
}

static int in_S(int x) {
    for (int k = 0; k < d; k++)
        if (S[k] == x) return 1;
    return 0;
}

static void random_S(void) {
    for (int k = 0; k < d; k++) {
        int x;
        int clash;
        do {
            x = rndint(M);
            clash = 0;
            for (int j = 0; j < k; j++)
                if (S[j] == x) { clash = 1; break; }
        } while (clash);
        S[k] = x;
    }
}

/* One hill-climb run for the current M. On success S holds a valid connection set. */
static int climb(long steps) {
    random_S();
    long cur = cost();
    for (long s = 0; s < steps; s++) {
        if (cur == 0) return 1;
        if ((s & 63) == 0 && now() > t_end) return 0;
        double T = 1.5 * (1.0 - (double)s / (double)steps) + 0.05;
        int k = rndint(d);
        int old = S[k];
        int nv;
        do nv = rndint(M); while (in_S(nv));
        S[k] = nv;
        long c2 = cost();
        if (c2 <= cur || rnd01() < exp(-(double)(c2 - cur) / T)) cur = c2;
        else S[k] = old;
    }
    return cur == 0;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit * 0.93;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || D < 2 || d > MAXD) {
        printf("1 0\n");
        return 0;
    }

    long moore = moore_bound();
    int bestM = d;
    int bestS[MAXD];
    for (int k = 0; k < d; k++) bestS[k] = k;   /* K_{d,d} */

    int gap = 0;
    while (now() < t_end) {
        int m = bestM + 1 + gap;
        if (m >= MAXM || 2L * m > moore) break;
        M = m;
        int ok = 0;
        for (int r = 0; r < 12 && now() < t_end && !ok; r++) {
            if (climb(40000)) ok = 1;
        }
        if (ok) {
            bestM = m;
            memcpy(bestS, S, sizeof(int) * (size_t)d);
            gap = 0;
        } else if (++gap >= 3) {
            break;
        }
    }

    printf("%d %d\n", 2 * bestM, bestM * d);
    for (int i = 0; i < bestM; i++)
        for (int k = 0; k < d; k++)
            printf("%d %d\n", i, bestM + (i + bestS[k]) % bestM);
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

    # Safe fallback: K_{d,d} (valid for D >= 2), or a known construction if larger.
    best = lib.haar_graph(d, range(d))
    try:
        start = known_start(d, D)
    except (ValueError, RuntimeError):
        start = None
    if start is not None and start[0] > best[0] and lib.is_valid(start[0], start[1], d, D):
        best = start

    if best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.92 * time_limit - (time.monotonic() - t0) - 1.5
    if budget < 0.5:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)], timeout=budget + 3)
        n, edges = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)
    except (RuntimeError, ValueError, OSError):
        pass
    return best
