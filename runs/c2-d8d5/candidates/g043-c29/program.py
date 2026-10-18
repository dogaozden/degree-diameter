"""Bipartite Haar-graph search: H(Z_m, S) with |S| = d, searched in C by annealing on S.

Haar graphs are vertex-transitive on each side under translation, so the diameter
check reduces to two BFS runs, from a_0 and from b_0. This replaces the earlier
lift-and-grow pipeline with a different family, to test whether abelian Haar graphs
can beat the cyclic and semidirect lifts for d=8, D=5.
"""
import itertools
import math
import random
import time

import lib


C_SOURCE = r'''
/* Haar-graph annealing: find S (|S| = d, residues mod M) so that H(Z_M, S) has diameter <= D.
 * Vertices: A_i = i, B_j = M + j. Edge A_i ~ B_{(i+s) mod M} for s in S.
 * Usage: prog d D seed time_limit m_start
 * Output: "n m" plus edges of the largest valid Haar graph found (or K_{d,d}).
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
#define ITERS 100000L

static int d, D;
static double t_end;
static int distq[2 * MAXM];
static int queue_[2 * MAXM];
static int S[MAXD];

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

/* Number of vertices (of the 2M total) not within distance D of src. */
static int unreached_from(int M, const int *Sv, int src) {
    int N = 2 * M;
    for (int v = 0; v < N; v++) distq[v] = -1;
    int head = 0, tail = 0, reached = 1;
    distq[src] = 0;
    queue_[tail++] = src;
    while (head < tail) {
        int v = queue_[head++];
        int dv = distq[v];
        if (dv >= D) continue;
        for (int t = 0; t < d; t++) {
            int u;
            if (v < M) {
                u = M + (v + Sv[t]) % M;
            } else {
                int j = v - M;
                u = (j - Sv[t] + M) % M;
            }
            if (distq[u] < 0) {
                distq[u] = dv + 1;
                queue_[tail++] = u;
                reached++;
            }
        }
    }
    return N - reached;
}

/* Vertex-transitivity per side means only a_0 and b_0 need checking. */
static int cost(int M, const int *Sv) {
    return unreached_from(M, Sv, 0) + unreached_from(M, Sv, M);
}

static int in_prefix(int cnt, int x) {
    for (int t = 0; t < cnt; t++)
        if (S[t] == x) return 1;
    return 0;
}

static int in_set(int x) { return in_prefix(d, x); }

static int anneal(int M) {
    for (int t = 0; t < d; t++) {
        int x;
        do { x = rndint(M); } while (in_prefix(t, x));
        S[t] = x;
    }
    int cur = cost(M, S);
    for (long it = 0; it < ITERS && cur > 0; it++) {
        if ((it & 255) == 0 && now() > t_end) return 0;
        double T = 1.5 * (1.0 - (double)it / (double)ITERS) + 0.05;
        int idx = rndint(d);
        int old = S[idx];
        int nw;
        if (rnd01() < 0.6) {
            int step = 1 + rndint(4);
            nw = (rnd() & 1) ? (old + step) % M : (old + M - step % M) % M;
        } else {
            nw = rndint(M);
        }
        if (nw == old || in_set(nw)) continue;
        S[idx] = nw;
        int c = cost(M, S);
        if (c <= cur || rnd01() < exp(-(double)(c - cur) / T)) cur = c;
        else S[idx] = old;
    }
    return cur == 0;
}

static void print_haar(int M, const int *Sv) {
    printf("%d %ld\n", 2 * M, (long)M * d);
    for (int i = 0; i < M; i++)
        for (int t = 0; t < d; t++)
            printf("%d %d\n", i, M + (i + Sv[t]) % M);
}

static void print_kdd(void) {
    printf("%d %d\n", 2 * d, d * d);
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++)
            printf("%d %d\n", a, d + b);
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: %s d D seed time_limit m_start\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long m_start = atol(argv[5]);
    double t0 = now();
    t_end = t0 + limit * 0.92;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 1 || d > MAXD) {
        print_kdd();
        return 0;
    }

    long moore = moore_bound();
    long target = m_start;
    if (target < d) target = d;
    int best_m = 0;
    int best_S[MAXD];

    while (now() < t_end) {
        if (2 * target > moore || target > MAXM) break;
        if (anneal((int)target)) {
            best_m = (int)target;
            memcpy(best_S, S, sizeof(int) * d);
            target++;
        }
    }

    if (best_m > 0) print_haar(best_m, best_S);
    else print_kdd();
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Exact and small constructions (calibration cases return immediately).
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
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    usable = max(1.0, 0.85 * time_limit - 2.0)
    end = t0 + usable

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        """Keep the graph if it is larger and valid."""
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
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            ar = lib.araujo_lopez_graph(d - 2)
            consider(ar[0], ar[1])
        except (ValueError, RuntimeError):
            pass
    if D == 4 and time.monotonic() < end:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Haar-graph annealing in C. Each Haar graph H(Z_m, S) with |S| = d has 2m vertices,
    # so the search starts just above the current best half-order.
    if D >= 2 and 2 <= d <= 32:
        m_start = max(d, best[0] // 2 + 1)
        budget = end - time.monotonic() - 0.5
        if budget > 1.0:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), m_start],
                                 stdin_graph=None, timeout=budget + 8)
                out = lib.parse_graph_text(text)
                consider(out[0], out[1])
            except (RuntimeError, ValueError):
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
