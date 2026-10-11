"""Diameter-3 bipartite search via cyclic Haar graphs (difference covers).

Construction: for a set S of k residues mod m, the Haar graph H(m, S) has parts a_i, b_i (i in Z_m),
with a_i ~ b_j iff j - i is in S. It is bipartite and k-regular on 2m vertices. If the difference set
S - S covers every residue of Z_m, then H(m, S) has diameter 3:
  - same-side pairs a_x, a_y are at distance 2 when y - x = s1 - s2,
  - cross pairs a_x, b_y are at distance <= 3 when y - x = s1 - s2 + s3 (choose s3 in S, then cover y - x - s3).
So the task is to find a k-element difference cover of Z_m with m as large as possible.
Upper bound: m <= k^2 - k + 1, so the order is at most 2(k^2 - k + 1). The C engine runs simulated
annealing on the number of uncovered differences, increasing m while it succeeds.

Fallbacks: K_{d,d} (diameter 2) and the projective plane incidence graph PG(2, d-1) when d-1 is a prime
power. Every candidate is checked with lib.is_valid, and the largest valid one is returned.
"""
import time

import lib

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXK 64
#define MAXM 4096

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int K, M;
static int S[MAXK];
static int inS[MAXM];
static int cnt[MAXM];
static int cost;

static int md(int x) {
    x %= M;
    if (x < 0) x += M;
    return x;
}

static void bump(int r, int sign) {
    if (sign > 0) {
        if (cnt[r]++ == 0) cost--;
    } else {
        if (--cnt[r] == 0) cost++;
    }
}

/* Add (sign=+1) or remove (sign=-1) the differences between x and every S[j], j != skip. */
static void apply(int x, int sign, int skip) {
    for (int j = 0; j < K; j++) {
        if (j == skip) continue;
        int t = S[j];
        bump(md(x - t), sign);
        bump(md(t - x), sign);
    }
}

static void rebuild(void) {
    for (int r = 0; r < M; r++) cnt[r] = 0;
    for (int i = 0; i < K; i++)
        for (int j = 0; j < K; j++)
            if (i != j) cnt[md(S[i] - S[j])]++;
    cost = 0;
    for (int r = 1; r < M; r++)
        if (cnt[r] == 0) cost++;
}

/* Simulated annealing for a K-subset of Z_m whose differences cover Z_m \ {0}. */
static int try_m(int m, double deadline) {
    M = m;
    while (now() < deadline) {
        memset(inS, 0, sizeof(inS));
        for (int i = 0; i < K; i++) {
            int x;
            do {
                x = (int)(rnd() % (uint64_t)M);
            } while (inS[x]);
            S[i] = x;
            inS[x] = 1;
        }
        rebuild();
        const long limit = 300000;
        for (long it = 0; cost > 0 && it < limit; it++) {
            double T = 0.1 + 0.9 * exp(-2.5 * (double)it / (double)limit);
            int i = (int)(rnd() % (uint64_t)K);
            int old = S[i];
            int x;
            do {
                x = (int)(rnd() % (uint64_t)M);
            } while (inS[x]);
            int before = cost;
            apply(old, -1, i);
            apply(x, +1, i);
            int delta = cost - before;
            if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
                inS[old] = 0;
                inS[x] = 1;
                S[i] = x;
            } else {
                apply(x, -1, i);
                apply(old, +1, i);
            }
        }
        if (cost == 0) return 1;
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 4) return 1;
    K = atoi(argv[1]);
    double budget = atof(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    if (K < 2 || K > MAXK) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;

    double t_end = now() + budget;
    int kmax = K * K - K + 1;
    if (kmax >= MAXM) kmax = MAXM - 1;

    int best_m = 0, found_any = 0;
    int bestS[MAXK];
    int m = (kmax * 7) / 10;
    if (m < K + 1) m = K + 1;

    while (m <= kmax) {
        double rem = t_end - now();
        if (rem < 0.05) break;
        double slice;
        if (found_any) slice = rem;
        else slice = (0.2 * budget < rem) ? 0.2 * budget : rem;

        if (try_m(m, now() + slice)) {
            found_any = 1;
            best_m = m;
            memcpy(bestS, S, sizeof(int) * (size_t)K);
            m++;
        } else {
            if (found_any) break;
            int step = m / 40;
            if (step < 1) step = 1;
            m -= step;
            if (m < K + 1) break;
        }
    }

    if (!found_any) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", best_m, K);
    for (int i = 0; i < K; i++) printf("%d%c", bestS[i], i + 1 < K ? ' ' : '\n');
    return 0;
}
"""


def _parse_search(text, d):
    """Parse the C output 'm k' then k residues. Return (m, S) or None."""
    nums = text.split()
    if len(nums) < 2:
        return None
    m, k = int(nums[0]), int(nums[1])
    if m <= 0 or k != d or len(nums) < 2 + k:
        return None
    S = [int(x) for x in nums[2:2 + k]]
    if len(set(S)) != k or any(not 0 <= s < m for s in S):
        return None
    return m, S


def _pg_candidate(d):
    """PG(2, d-1) incidence graph (degree d, diameter 3) when d-1 is a prime power."""
    q = d - 1
    if q < 2 or not lib.is_prime_power(q):
        return None
    return lib.projective_plane_incidence(q)


def build(d, D, seed, time_limit):
    """Return the largest valid (n, edges) found; the difference-cover search is used for D >= 3."""
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    cands = []
    # Safe fallback: K_{d,d} has diameter 2, so it is valid for every D >= 2.
    kk = lib.haar_graph(d, range(d))
    if lib.is_valid(kk[0], kk[1], d, D):
        cands.append(kk)

    if D >= 3:
        pg = _pg_candidate(d)
        if pg is not None and lib.is_valid(pg[0], pg[1], d, D):
            cands.append(pg)

        if 2 <= d <= 60:
            budget = max(0.5, 0.78 * time_limit - (time.monotonic() - t0) - 1.0)
            try:
                text = lib.run_c(C_SOURCE, [d, f"{budget:.2f}", seed],
                                 timeout=budget + 5.0)
                parsed = _parse_search(text, d)
                if parsed is not None:
                    m, S = parsed
                    n, e = lib.haar_graph(m, S)
                    if lib.is_valid(n, e, d, D):
                        cands.append((n, e))
            except Exception:
                pass

    if not cands:
        return 1, []
    best = max(cands, key=lambda g: g[0])
    if not lib.is_valid(best[0], best[1], d, D):
        best = kk
    return best
