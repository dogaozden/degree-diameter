"""Diameter-3 bipartite search: cyclic Haar graphs from difference covers, found by C simulated annealing."""
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
#define LIMIT 400000L

/*
 * Search for S = {s_1..s_K} in Z_M with S - S = Z_M (every residue is a difference).
 * Then the bipartite graph a_i ~ b_{i+s} (s in S) has degree K, 2M vertices and diameter 3.
 * Cost = number of nonzero residues not covered as a difference. Largest M wins.
 */

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int n) {
    return (int)(rnd64() % (uint64_t)n);
}

static double rnd01(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}

static double cpu_now(void) {
    return (double)clock() / (double)CLOCKS_PER_SEC;
}

static int K, M;
static int S[MAXK];
static int inS[MAXM];
static int cnt[MAXM];
static int zeros;

static int md(int x) {
    x %= M;
    if (x < 0) x += M;
    return x;
}

static void full_count(void) {
    memset(cnt, 0, sizeof(int) * (size_t)M);
    for (int i = 0; i < K; i++)
        for (int j = 0; j < K; j++)
            if (i != j) cnt[md(S[i] - S[j])]++;
    zeros = 0;
    for (int x = 1; x < M; x++)
        if (cnt[x] == 0) zeros++;
}

/* Replace S[i] by y (y not in S). Keeps cnt and zeros exact; calling again with the old value reverts. */
static void replace_el(int i, int y) {
    int old = S[i];
    for (int j = 0; j < K; j++) {
        if (j == i) continue;
        int t = S[j];
        int a = md(old - t);
        int b = md(t - old);
        if (--cnt[a] == 0) zeros++;
        if (--cnt[b] == 0) zeros++;
    }
    inS[old] = 0;
    S[i] = y;
    inS[y] = 1;
    for (int j = 0; j < K; j++) {
        if (j == i) continue;
        int t = S[j];
        int a = md(y - t);
        int b = md(t - y);
        if (cnt[a]++ == 0) zeros--;
        if (cnt[b]++ == 0) zeros--;
    }
}

/* Simulated annealing with restarts. Returns 1 if a full cover is found before end, else 0. */
static int search(double end) {
    if (K < 2) return 0;
    for (;;) {
        if (cpu_now() > end) return 0;
        memset(inS, 0, sizeof(int) * (size_t)M);
        for (int i = 0; i < K; i++) {
            int y;
            do {
                y = rndint(M);
            } while (inS[y]);
            S[i] = y;
            inS[y] = 1;
        }
        full_count();
        double T = 0.2 + 0.5 * rnd01();
        for (long step = 0; zeros > 0 && step < LIMIT; step++) {
            if ((step & 4095L) == 0 && cpu_now() > end) return 0;
            int i, y;
            if (rnd01() < 0.7) {
                /* Focused move: pick an uncovered residue x and make it a difference. */
                int start = rndint(M - 1);
                int x = 0;
                for (int t = 0; t < M - 1; t++) {
                    int c = 1 + (start + t) % (M - 1);
                    if (cnt[c] == 0) {
                        x = c;
                        break;
                    }
                }
                if (!x) break;
                int j = rndint(K);
                y = (S[j] + x) % M;
                if (inS[y]) continue;
                do {
                    i = rndint(K);
                } while (i == j);
            } else {
                i = rndint(K);
                do {
                    y = rndint(M);
                } while (inS[y]);
            }
            int old = S[i];
            int z0 = zeros;
            replace_el(i, y);
            int delta = zeros - z0;
            if (delta > 0 && rnd01() >= exp(-(double)delta / T)) replace_el(i, old);
        }
        if (zeros == 0) return 1;
    }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    uint64_t seed = (uint64_t)strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    (void)D;

    rs ^= seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 10; i++) rnd64();

    K = d;
    int cap = K * (K - 1) + 1;
    if (K < 2 || K > MAXK || cap >= MAXM) {
        printf("0 0\n");
        return 0;
    }

    double end = cpu_now() + tl;
    int bestM = 0;
    int bestS[MAXK];

    int m = K + 1;
    int fails = 0;
    while (m <= cap) {
        double now = cpu_now();
        if (now >= end) break;
        M = m;
        double rem = end - now;
        double sl = now + 0.2 * rem;
        if (sl > end) sl = end;
        if (search(sl)) {
            bestM = m;
            for (int k = 0; k < K; k++) bestS[k] = S[k];
            m++;
            fails = 0;
        } else {
            if (++fails >= 3) break;
        }
    }

    if (bestM == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", 2 * bestM, bestM * K);
    for (int i = 0; i < bestM; i++)
        for (int k = 0; k < K; k++)
            printf("%d %d\n", i, bestM + (i + bestS[k]) % bestM);
    return 0;
}
"""


def _largest_prime_power_at_most(n):
    """Largest prime power q with 2 <= q <= n, or None."""
    for q in range(n, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        # Algebraic candidates: PG(2,q) with q + 1 <= d, and Araujo-Pardo-Lopez for d - 2 a prime power.
        q = _largest_prime_power_at_most(d - 1)
        if q is not None:
            try:
                consider(*lib.projective_plane_incidence(q))
            except Exception:
                pass
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(*lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass

        # Main construction: cyclic Haar graph H(M, S) with S - S = Z_M, found by C annealing.
        # Diameter is 3 for any such cover, so it is valid for every D >= 3.
        if d >= 2:
            elapsed = time.monotonic() - start
            c_budget = max(0.5, min(0.7 * time_limit - 3.0, time_limit - elapsed - 6.0))
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(c_budget, 2)],
                                 stdin_graph=None, timeout=c_budget + 8.0)
                consider(*lib.parse_graph_text(text))
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
