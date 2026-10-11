"""Difference-cover Haar graphs for D = 3.

For D = 3, the bipartite Haar graph H(Z_m, S) with |S| = d has diameter <= 3 exactly when
the difference set S - S covers all of Z_m. Then it is d-regular, bipartite, and has 2m
vertices. The C engine searches for covers with the largest m it can reach, using simulated
annealing on the number of uncovered differences. Python keeps the best of the known
construction, K_{d,d}, and any validated cover graph.
"""
import time

import lib

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

/* Searches S subset of Z_m with |S| = d, 0 in S, S - S = Z_m, for the largest m it can reach.
 * Usage: prog d D seed time_limit   (stdin ignored)
 * stdout: "m k" then the k elements of S. Prints "0 0" if nothing was found. */

#define MAXM 2048
#define MAXK 64

static int d, D, m;
static int S[MAXK];
static unsigned char inS[MAXM];
static int cnt[MAXM];   /* cnt[t] = number of ordered pairs (a, b) in S, a != b, with a - b = t */
static int zeros;       /* number of t in 1..m-1 with cnt[t] == 0 */
static double t_end;

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

static inline int dif(int a, int b) {
    int t = a - b;
    return t < 0 ? t + m : t;
}

/* Add or remove the ordered differences of the unordered pair {a, b}. */
static void padd(int a, int b) {
    int t = dif(a, b);
    if (cnt[t]++ == 0) zeros--;
    t = dif(b, a);
    if (cnt[t]++ == 0) zeros--;
}

static void prem(int a, int b) {
    int t = dif(a, b);
    if (--cnt[t] == 0) zeros++;
    t = dif(b, a);
    if (--cnt[t] == 0) zeros++;
}

static void init_random(void) {
    memset(inS, 0, sizeof inS);
    memset(cnt, 0, sizeof cnt);
    S[0] = 0;
    inS[0] = 1;
    for (int i = 1; i < d; i++) {
        int y;
        do { y = 1 + rndint(m - 1); } while (inS[y]);
        S[i] = y;
        inS[y] = 1;
    }
    zeros = m - 1;
    for (int i = 0; i < d; i++)
        for (int j = 0; j < i; j++) padd(S[i], S[j]);
}

/* Simulated annealing for a difference cover of Z_m. Returns 1 with S set on success,
 * 0 when time runs out. */
static int anneal(double until) {
    const double T0 = 1.0, T1 = 0.03;
    const long L = 2000000;
    init_random();
    if (zeros == 0) return 1;
    long it = 0, pos = 0;
    double T = T0;
    for (;;) {
        if ((++it & 4095) == 0 && now() > until) return 0;
        if (++pos >= L) {
            pos = 0;
            init_random();
            if (zeros == 0) return 1;
        }
        if ((it & 63) == 0) T = T0 * pow(T1 / T0, (double)pos / (double)L);

        int i = 1 + rndint(d - 1);
        int x = S[i];
        int y;
        do { y = 1 + rndint(m - 1); } while (inS[y]);

        int old = zeros;
        for (int j = 0; j < d; j++)
            if (j != i) prem(x, S[j]);
        S[i] = y;
        for (int j = 0; j < d; j++)
            if (j != i) padd(y, S[j]);
        int delta = zeros - old;

        if (delta <= 0 || rnd01() < exp(-delta / T)) {
            inS[x] = 0;
            inS[y] = 1;
            if (zeros == 0) return 1;
        } else {
            for (int j = 0; j < d; j++)
                if (j != i) prem(y, S[j]);
            S[i] = x;
            for (int j = 0; j < d; j++)
                if (j != i) padd(x, S[j]);
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 5) return 2;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit * 0.92;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (D != 3 || d < 2 || d > MAXK) {
        printf("0 0\n");
        return 0;
    }
    long mmax = (long)d * (d - 1) + 1;   /* covering bound: |S - S| <= d(d-1) + 1 */
    if (mmax > MAXM - 1) mmax = MAXM - 1;
    m = (int)(0.6 * (double)mmax);
    if (m < d) m = d;

    int bestm = 0;
    int bestS[MAXK];
    while (m <= mmax && now() < t_end) {
        if (!anneal(t_end)) break;
        bestm = m;
        memcpy(bestS, S, sizeof(int) * d);
        m++;
    }
    if (bestm == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", bestm, d);
    for (int i = 0; i < d; i++) printf("%d ", bestS[i]);
    printf("\n");
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


def fallback(d, D):
    """A graph that is always valid: K_{d,d} when D >= 2, otherwise a single edge."""
    if D >= 2:
        g = lib.haar_graph(d, range(d))
        if lib.is_valid(*g, d, D):
            return g
    g = (2, [(0, 1)])
    if lib.is_valid(*g, d, D):
        return g
    return (1, [])


def parse_cover(text):
    """Parse 'm k' then k elements. Returns (m, S) or None."""
    nums = text.split()
    if len(nums) < 2:
        return None
    m, k = int(nums[0]), int(nums[1])
    if m <= 0 or k <= 0 or len(nums) < 2 + k:
        return None
    return m, [int(x) for x in nums[2:2 + k]]


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    best = known_start(d, D)
    if best is not None and not lib.is_valid(*best, d, D):
        best = None
    if best is None:
        best = fallback(d, D)

    if D == 3 and d >= 3 and best[0] < lib.moore_bound(d, D):
        budget = 0.88 * time_limit - (time.monotonic() - t0) - 1.5
        if budget > 2.0:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                                 stdin_graph=None, timeout=budget + 8)
                got = parse_cover(text)
                if got is not None:
                    m, S = got
                    cand = lib.haar_graph(m, S)
                    if cand[0] > best[0] and lib.is_valid(*cand, d, D):
                        best = cand
            except (RuntimeError, ValueError):
                pass   # keep the valid fallback
    return best
