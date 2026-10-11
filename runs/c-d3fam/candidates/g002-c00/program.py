"""Bold change for the D = 3 targets: a cyclic Haar-graph construction.

For S a d-subset of Z_m, the Haar graph H(m, S) (a_i ~ b_{i+s}, s in S) is bipartite and
d-regular on 2m vertices. It has diameter <= 3 exactly when S - S covers all of Z_m, because
A-A and B-B distances come from differences, and A-B distance 3 follows from S - S = Z_m.
So the task becomes: find a d-set in Z_m with S - S = Z_m for m as large as possible.
The count bound is m <= d^2 - d + 1, which is the Moore bound 2(d^2 - d + 1) on the order.
The C engine anneals over such sets (one element moves at a time, cost = uncovered residues)
and outputs the largest m it covers. Python keeps the Araujo-Lopez / projective-plane start
whenever the search does not beat it, so every case still returns a valid graph.

Untested: whether annealing reaches m above record/2 for d = 11, 13, 15 within the time budget.
If it does not, the known construction is returned unchanged.
"""
import time

import lib

C_SOURCE = r'''
/* Cyclic Haar-graph covering search for diameter 3.
 *
 * Usage:  prog d D seed time_limit m_start
 * Finds a d-subset S of Z_m with S - S = Z_m (all nonzero residues are differences),
 * then prints the Haar graph on 2m vertices: a_i = i, b_j = m + j, a_i ~ b_{i+s} for s in S.
 * Prints "0 0" if nothing was found or D != 3.
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

static int d, D, m;
static int S[MAXD], bestS[MAXD];
static int inS[MAXM], cnt[MAXM];
static int uncovered;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static inline int md(int x) {
    x %= m;
    if (x < 0) x += m;
    return x;
}

/* cnt[x] = number of ordered pairs (s, t), s != t in S, with s - t = x (mod m). */
static inline void incr(int x) {
    if (cnt[x]++ == 0) uncovered--;
}
static inline void decr(int x) {
    if (--cnt[x] == 0) uncovered++;
}

/* Remove S[i] from the difference counts. */
static void drop(int i) {
    int s = S[i];
    for (int j = 0; j < d; j++)
        if (j != i) {
            decr(md(s - S[j]));
            decr(md(S[j] - s));
        }
    inS[s] = 0;
}

/* Put v into slot i and add its differences. */
static void put(int i, int v) {
    S[i] = v;
    inS[v] = 1;
    for (int j = 0; j < d; j++)
        if (j != i) {
            incr(md(v - S[j]));
            incr(md(S[j] - v));
        }
}

/* Random start with S[0] = 0 (translation is free). Only slots 0..i-1 are counted. */
static void init_random(void) {
    memset(cnt, 0, sizeof(int) * (size_t)m);
    memset(inS, 0, sizeof(int) * (size_t)m);
    uncovered = m - 1;
    S[0] = 0;
    inS[0] = 1;
    for (int i = 1; i < d; i++) {
        int v;
        do v = rndint(m); while (inS[v]);
        S[i] = v;
        inS[v] = 1;
        for (int j = 0; j < i; j++) {
            incr(md(v - S[j]));
            incr(md(S[j] - v));
        }
    }
}

/* Simulated annealing on the uncovered count. Returns 1 with S covering Z_m, 0 on timeout. */
static int anneal(double until) {
    init_random();
    long it = 0;
    double T = 1.0;
    while (uncovered > 0) {
        if ((++it & 1023) == 0 && now() > until) return 0;
        if ((it & 255) == 0) {
            double phase = (double)(it & ((1L << 22) - 1)) / (double)(1L << 22);
            T = pow(0.03, phase); /* reheat every 2^22 steps */
        }
        int i = 1 + rndint(d - 1); /* S[0] stays 0 */
        int v = rndint(m);
        if (inS[v]) continue;
        int old = S[i], before = uncovered;
        drop(i);
        put(i, v);
        int delta = uncovered - before;
        if (delta <= 0 || rnd01() < exp(-delta / T)) continue;
        drop(i);
        put(i, old);
    }
    return 1;
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
    int mstart = atoi(argv[5]);
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    double deadline = now() + limit * 0.9;
    if (D != 3 || d < 3 || d > MAXD) {
        printf("0 0\n");
        return 0;
    }

    int best_m = 0;
    m = mstart > d + 1 ? mstart : d + 1;
    while (m < MAXM / 2 && now() < deadline) {
        double slice = (deadline - now()) * (best_m ? 0.5 : 0.35);
        if (anneal(now() + slice)) {
            best_m = m;
            memcpy(bestS, S, sizeof(int) * (size_t)d);
            m++;
        } else {
            if (best_m) break;   /* the next size is harder: keep the best found */
            m--;                 /* nothing found yet: try a smaller cyclic group */
            if (m < d + 1) break;
        }
    }

    if (!best_m) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", 2 * best_m, best_m * d);
    for (int i = 0; i < best_m; i++)
        for (int k = 0; k < d; k++)
            printf("%d %d\n", i, best_m + (i + bestS[k]) % best_m);
    return 0;
}
'''


def known_start(d, D):
    """Best graph Python can build directly for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)           # record graphs of order 2(q^2+q+5)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    start = known_start(d, D)
    best = start if start is not None else lib.haar_graph(d, range(d))   # K_{d,d}: always valid

    # Only the D = 3 covering search is implemented here; other D keep the known start.
    if D != 3 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.8 * time_limit - (time.monotonic() - t0) - 2.0
    if budget < 1.0:
        return best

    # Start a little below the record half-order, which should be reachable quickly.
    m_start = max(d + 1, best[0] // 2 - 2)
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), m_start],
                         timeout=budget + 5)
        n, edges = lib.parse_graph_text(text)
    except (RuntimeError, ValueError):
        return best

    if n > best[0] and lib.is_valid(n, edges, d, D):
        best = (n, edges)
    return best
