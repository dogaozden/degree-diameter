import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing over cyclic Haar graphs H(m, S).
#
# Vertices a_i = i and b_j = m + j. Edges a_i -- b_{i+s} for s in S, where S is a
# set of d distinct residues mod m. This is a bipartite d-regular graph. The map
# x -> x + t is an automorphism, so distances from a_i and b_j are translates of
# distances from a_0 and b_0. Two BFS runs of depth D therefore decide the whole
# diameter. Cost = number of vertices unreached from a_0 plus from b_0.
# Usage: prog d D m seed time_limit. Prints "OK s_1 ... s_d" or "FAIL".
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXM 8192
#define MAXD 64
#define MAXN (2 * MAXM)

static int d, D, m;
static int S[MAXD];
static int dist[MAXN], q[MAXN];
static uint64_t rs = 88172645463325252ULL;

static uint64_t nx(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rnd(int k) { return (int)(nx() % (uint64_t)k); }

static double r01(void) {
    return (double)(nx() >> 11) * (1.0 / 9007199254740992.0);
}

static int cost(void) {
    int N = 2 * m, total = 0;
    for (int src = 0; src < 2; src++) {
        int s0 = src ? m : 0;
        for (int i = 0; i < N; i++) dist[i] = -1;
        int qh = 0, qt = 0;
        q[qt++] = s0;
        dist[s0] = 0;
        while (qh < qt) {
            int u = q[qh++];
            if (dist[u] >= D) continue;
            for (int i = 0; i < d; i++) {
                int w;
                if (u < m) w = m + (u + S[i]) % m;
                else w = ((u - m) - S[i] + m) % m;
                if (dist[w] < 0) {
                    dist[w] = dist[u] + 1;
                    q[qt++] = w;
                }
            }
        }
        total += N - qt;
    }
    return total;
}

static void randomize(void) {
    S[0] = 0;
    for (int i = 1; i < d; i++) {
        while (1) {
            int x = 1 + rnd(m - 1);
            int dup = 0;
            for (int j = 0; j < i; j++)
                if (S[j] == x) dup = 1;
            if (!dup) {
                S[i] = x;
                break;
            }
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 6) {
        printf("FAIL\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    m = atoi(argv[3]);
    unsigned long long seed = strtoull(argv[4], NULL, 10);
    double tl = atof(argv[5]);
    if (d < 2 || d > MAXD || D < 1 || m <= d || m > MAXM || tl <= 0) {
        printf("FAIL\n");
        return 0;
    }
    rs = seed * 0x9E3779B97F4A7C15ULL + 1ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) nx();

    clock_t start = clock();
    randomize();
    int c = cost();
    int best_c = c;
    long stall = 0;
    while (c > 0) {
        double frac = ((double)(clock() - start) / CLOCKS_PER_SEC) / tl;
        if (frac >= 1.0) break;
        double T = 0.5 + 3.0 * (1.0 - frac);
        int i = 1 + rnd(d - 1);
        int x = 1 + rnd(m - 1);
        int dup = 0;
        for (int j = 0; j < d; j++)
            if (S[j] == x) dup = 1;
        if (dup) continue;
        int old = S[i];
        S[i] = x;
        int c2 = cost();
        if (c2 <= c || r01() < exp(-(double)(c2 - c) / T)) {
            c = c2;
        } else {
            S[i] = old;
        }
        if (c < best_c) {
            best_c = c;
            stall = 0;
        } else if (++stall > 30000) {
            randomize();
            c = cost();
            best_c = c;
            stall = 0;
        }
    }
    if (c == 0) {
        printf("OK");
        for (int i = 0; i < d; i++) printf(" %d", S[i]);
        printf("\n");
    } else {
        printf("FAIL\n");
    }
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


def _largest_prime_power(k):
    """Largest prime power q with 2 <= q <= k, or None."""
    for q in range(k, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def _haar_c(d, D, m, seed, budget):
    """Ask the C annealer for a connection set S of size d in Z_m giving a diameter-D Haar graph.

    Returns the list S, or None if the search failed within budget.
    """
    out = lib.run_c(C_SOURCE, [d, D, m, seed, f"{budget:.2f}"],
                    stdin_graph=None, timeout=budget + 3.0)
    tok = out.split()
    if not tok or tok[0] != "OK":
        return None
    S = [int(x) for x in tok[1:1 + d]]
    if len(S) != d or len(set(S)) != d or any(not (0 <= x < m) for x in S):
        return None
    return S


def build(d, D, seed, time_limit):
    start = time.monotonic()
    tl = float(time_limit)
    rng = random.Random(seed)

    # Trivial cases.
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

    # Quick algebraic baselines (cheap, always valid when they pass the check).
    if D == 3:
        q = _largest_prime_power(d - 1)
        if q is not None and q >= 2:
            try:
                consider(*lib.projective_plane_incidence(q))
            except Exception:
                pass
    if D == 4 and tl >= 15:
        for q in range(d - 1, 1, -1):
            if q <= 16 and lib.is_prime_power(q):
                try:
                    consider(*_gq_w(q))
                except Exception:
                    pass
                break

    # Bold change: cyclic Haar graphs H(m, S) searched by C annealing.
    # Each success gives order 2m, so we always aim for m just above the current best half-order.
    hard_end = start + 0.9 * tl - 1.0
    while True:
        now = time.monotonic()
        remaining = hard_end - now
        slice_t = min(remaining - 1.0, max(3.0, 0.3 * tl))
        if slice_t < 1.0:
            break
        m = max(best_n // 2 + 1, d + 1)
        try:
            S = _haar_c(d, D, m, rng.randrange(1 << 30), slice_t)
        except Exception:
            break
        if S is not None:
            n, e = lib.haar_graph(m, S)
            consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
