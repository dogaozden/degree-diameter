"""Haar-graph search for bipartite degree-diameter graphs.

Main engine (C): a Haar graph H(Z_m, S) has vertices A_i and B_j (i, j in Z_m) with A_i ~ B_{i+s}
for s in S, |S| = d, and 0 in S by translation. It is d-regular and bipartite. Translation by a
acts on both sides, so the diameter is at most D iff the BFS balls of A_0 and B_0 cover everything
within D steps. The search holds |S| fixed and anneals one shift at a time, minimising the number
of unreached vertices. Whenever a zero-cost S is found for m = best + 1, the order grows.

Python provides the start graph (K_{d,d}, or an algebraic graph when one is better), calls the
engine, and keeps the largest graph that lib.is_valid accepts. The fallback is always valid.
"""
import itertools
import time

import lib

C_SOURCE = r'''
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXM 20000
#define MAXS 40

static int d, D, m;
static int S[MAXS];
static int bestS[MAXS];
static int best_m;
static double t_end;
static int stampv[2 * MAXM];
static int stk = 0;
static int qb[2 * MAXM];

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

/* Largest order of a bipartite graph with max degree d and diameter D, divided by nothing. */
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

/* Number of vertices reached within D steps from src (A_i = i, B_j = m + j). */
static int reach(int src) {
    stk++;
    int head = 0, tail = 0;
    qb[tail++] = src;
    stampv[src] = stk;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        for (; head < end; head++) {
            int v = qb[head];
            if (v < m) {
                for (int k = 0; k < d; k++) {
                    int u = m + (v + S[k]) % m;
                    if (stampv[u] != stk) { stampv[u] = stk; qb[tail++] = u; }
                }
            } else {
                int j = v - m;
                for (int k = 0; k < d; k++) {
                    int u = (j - S[k] + m) % m;
                    if (stampv[u] != stk) { stampv[u] = stk; qb[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Zero iff the Haar graph H(Z_m, S) has diameter <= D. */
static long cost(void) {
    return (long)(2 * m - reach(0)) + (long)(2 * m - reach(m));
}

static int in_S(int t, int k) {
    for (int i = 0; i < k; i++)
        if (S[i] == t) return 1;
    return 0;
}

static void rand_S(void) {
    S[0] = 0;
    for (int k = 1; k < d; k++) {
        int t;
        do t = 1 + rndint(m - 1); while (in_S(t, k));
        S[k] = t;
    }
}

/* Simulated annealing on the shifts S[1..d-1]. Returns 1 when a valid S is found. */
static int anneal(long steps) {
    double T0 = 0.5 + 2.0 * rnd01();
    long cur = cost();
    if (cur == 0) return 1;
    for (long s = 0; s < steps; s++) {
        if ((s & 127) == 0 && now() > t_end) return 0;
        double T = T0 * (1.0 - (double)s / (double)steps) + 0.05;
        int k = 1 + rndint(d - 1);
        int t;
        do t = 1 + rndint(m - 1); while (in_S(t, d));
        int old = S[k];
        S[k] = t;
        long c = cost();
        if (c <= cur || rnd01() < exp(-(double)(c - cur) / T)) {
            cur = c;
            if (cur == 0) return 1;
        } else {
            S[k] = old;
        }
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 5) return 2;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.3;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 2 || d > MAXS) {
        printf("0 0\n");
        return 0;
    }

    /* K_{d,d} is the Haar graph with m = d and S = all residues: diameter 2, valid. */
    best_m = d;
    for (int k = 0; k < d; k++) bestS[k] = k;

    long mb = moore_bound();
    int mcap = (int)(mb / 2);
    if (mcap > MAXM) mcap = MAXM;
    int cur_m = -1;

    while (now() < t_end) {
        int mt = best_m + 1;
        if (mt > mcap) break;
        if (mt != cur_m) {
            m = mt;
            rand_S();
            cur_m = mt;
        }
        if (anneal(20000)) {
            best_m = m;
            memcpy(bestS, S, sizeof(int) * d);
        }
    }

    int n = 2 * best_m;
    long E = (long)best_m * d;
    printf("%d %ld\n", n, E);
    for (int i = 0; i < best_m; i++)
        for (int k = 0; k < d; k++)
            printf("%d %d\n", i, best_m + (i + bestS[k]) % best_m);
    return 0;
}
'''


def _gq_w(q):
    """Incidence graph of points and lines of W(q): degree q+1, diameter 4."""
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


def _largest_prime_power_le(x):
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def _try(fn, *args):
    try:
        return fn(*args)
    except Exception:
        return None


def known_starts(d, D):
    """Algebraic candidate graphs (filtered by lib.is_valid by the caller)."""
    out = []
    if D >= 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        out.append(_try(lib.projective_plane_incidence, d - 1))
    if D >= 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        out.append(_try(lib.araujo_lopez_graph, d - 2))
    if D >= 4:
        q = _largest_prime_power_le(min(d - 1, 9))
        if q is not None and q >= 2:
            out.append(_try(_gq_w, q))
    return [c for c in out if c is not None]


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D
        return L, [(i, (i + 1) % L) for i in range(L)]

    # Safe fallback: K_{d,d} (diameter 2), then any valid algebraic start that is larger.
    best = lib.haar_graph(d, range(d))
    for cand in known_starts(d, D):
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 39 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.9 * time_limit - (time.monotonic() - t0) - 3.0
    if budget < 2.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=None, timeout=budget + 15)
        n, e = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
    except Exception:
        pass
    return best
