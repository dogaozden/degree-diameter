import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Engine: simulated annealing over bi-Cayley graphs.
#
# G = Z_m x|_r Z_k (element (a, b) coded as a*k + b). The graph has vertices
# A_g = g and B_h = N + h (N = |G|), with A_g ~ B_{g*s} for s in S, |S| = d.
# Left multiplication by G is an automorphism that is transitive on A and on B,
# so the graph has diameter <= D iff every pair (A_0, x) and (B_0, x) is within D.
# Cost = total excess distance from these two roots (0 iff valid).
#
# Usage: prog d D m k r seed slice_seconds
# Prints the graph ("n m" + edges) or "0 0".
# ----------------------------------------------------------------------------

BICAY_C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

static int DEG, DIAM, MM, K2, R, N;
static int *MT, *INV, *POWR, *dist, *qu, *S, *inS;
static uint64_t rs = 88172645463325252ULL;

static inline uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static inline int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static inline double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double elapsed(clock_t t0) { return (double)(clock() - t0) / (double)CLOCKS_PER_SEC; }

static int gcd_int(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static int gmul(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, dd = y % K2;
    long long t = (a + (long long)POWR[b] * c) % MM;
    return (int)(t * K2 + (b + dd) % K2);
}

static int cost_of(void) {
    int total = 0;
    int NN2 = 2 * N;
    for (int root = 0; root < 2; root++) {
        int src = root ? N : 0;
        for (int v = 0; v < NN2; v++) dist[v] = -1;
        int qh = 0, qt = 0;
        qu[qt++] = src;
        dist[src] = 0;
        while (qh < qt) {
            int u = qu[qh++];
            int du = dist[u] + 1;
            if (u < N) {
                const int *row = MT + (size_t)u * N;
                for (int i = 0; i < DEG; i++) {
                    int v = N + row[S[i]];
                    if (dist[v] < 0) { dist[v] = du; qu[qt++] = v; }
                }
            } else {
                const int *row = MT + (size_t)(u - N) * N;
                for (int i = 0; i < DEG; i++) {
                    int v = row[INV[S[i]]];
                    if (dist[v] < 0) { dist[v] = du; qu[qt++] = v; }
                }
            }
        }
        for (int v = 0; v < NN2; v++) {
            if (dist[v] < 0) total += DIAM + 2;
            else if (dist[v] > DIAM) total += dist[v] - DIAM;
        }
    }
    return total;
}

int main(int argc, char **argv) {
    if (argc < 8) { printf("0 0\n"); return 0; }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    MM = atoi(argv[3]);
    K2 = atoi(argv[4]);
    R = atoi(argv[5]);
    uint64_t seed = strtoull(argv[6], NULL, 10);
    double slice = atof(argv[7]);

    if (DEG < 1 || DIAM < 1 || MM < 1 || K2 < 1 || R < 1) { printf("0 0\n"); return 0; }
    if (gcd_int(R, MM) != 1) { printf("0 0\n"); return 0; }
    N = MM * K2;
    if (N <= DEG || N > 1500) { printf("0 0\n"); return 0; }

    POWR = malloc(sizeof(int) * (size_t)K2);
    if (!POWR) { printf("0 0\n"); return 0; }
    POWR[0] = 1 % MM;
    for (int b = 1; b < K2; b++) POWR[b] = (int)((long long)POWR[b - 1] * R % MM);
    if (((long long)POWR[K2 - 1] * R) % MM != 1 % MM) { printf("0 0\n"); return 0; }

    MT = malloc(sizeof(int) * (size_t)N * N);
    INV = malloc(sizeof(int) * N);
    dist = malloc(sizeof(int) * 2 * N);
    qu = malloc(sizeof(int) * 2 * N);
    S = malloc(sizeof(int) * DEG);
    inS = calloc(N, sizeof(int));
    if (!MT || !INV || !dist || !qu || !S || !inS) { printf("0 0\n"); return 0; }

    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            MT[(size_t)x * N + y] = gmul(x, y);
    for (int x = 0; x < N; x++) {
        if (MT[x] != x) { printf("0 0\n"); return 0; }  /* identity must be 0 */
        INV[x] = -1;
        for (int y = 0; y < N; y++)
            if (MT[(size_t)x * N + y] == 0) { INV[x] = y; break; }
        if (INV[x] < 0) { printf("0 0\n"); return 0; }
    }

    rs = seed * 0x9E3779B97F4A7C15ULL ^ 0x5DEECE66DULL;
    if (rs == 0) rs = 1;

    clock_t t0 = clock();
    int found = 0;
    const int LEN = 40000;
    while (!found && elapsed(t0) < slice) {
        memset(inS, 0, sizeof(int) * N);
        for (int i = 0; i < DEG; i++) {
            int x;
            do { x = rndint(N); } while (inS[x]);
            S[i] = x;
            inS[x] = 1;
        }
        int cur = cost_of();
        if (cur == 0) { found = 1; break; }
        const double T0 = 4.0;
        for (int it = 0; it < LEN; it++) {
            if ((it & 63) == 0 && elapsed(t0) >= slice) break;
            double T = T0 * (1.0 - (double)it / LEN) + 0.05;
            int i = rndint(DEG);
            int old = S[i];
            int x;
            do { x = rndint(N); } while (inS[x]);
            S[i] = x;
            inS[old] = 0;
            inS[x] = 1;
            int nc = cost_of();
            if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
                cur = nc;
                if (cur == 0) { found = 1; break; }
            } else {
                S[i] = old;
                inS[x] = 0;
                inS[old] = 1;
            }
        }
    }

    if (!found) { printf("0 0\n"); return 0; }
    printf("%d %d\n", 2 * N, N * DEG);
    for (int g = 0; g < N; g++)
        for (int i = 0; i < DEG; i++)
            printf("%d %d\n", g, N + MT[(size_t)g * N + S[i]]);
    fflush(stdout);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact fallbacks.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Group enumeration and bi-Cayley search.
# ----------------------------------------------------------------------------

def _groups_of_order(n):
    """All (m, k, r) describing Z_m x|_r Z_k with m * k = n (r = 1 gives the direct product)."""
    out = []
    for k in range(1, n + 1):
        if n % k:
            continue
        m = n // k
        if k == 1:
            out.append((m, 1, 1))
            continue
        out.append((m, k, 1))
        for r in range(2, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _bicayley_try(d, D, n, rng, slice_s):
    """Try up to three groups of order n with the bi-Cayley annealer. Returns (2n, edges) or None."""
    groups = _groups_of_order(n)
    if not groups:
        return None
    rng.shuffle(groups)
    tries = min(3, len(groups))
    per = slice_s / tries
    for m, k, r in groups[:tries]:
        out = lib.run_c(
            BICAY_C_SOURCE,
            [d, D, m, k, r, rng.randrange(1, 10 ** 9), f"{per:.2f}"],
            timeout=per + 5.0,
        )
        try:
            nn, e = lib.parse_graph_text(out)
        except ValueError:
            continue
        if nn > 0 and lib.is_valid(nn, e, d, D):
            return nn, e
    return None


def _bicayley_phase(d, D, rng, state, deadline):
    """Bisect the half-size n of a balanced bi-Cayley graph, keeping the largest valid one."""
    lo = state[0][0] // 2
    hi = None
    n = max(lo + 1, int(0.36 * lib.moore_bound(d, D) / 2))
    while True:
        rem = deadline - time.monotonic()
        if rem < 2.0 or n > 1400 or n <= lo:
            break
        slice_s = min(rem - 1.0, max(2.0, min(8.0, rem / 4)))
        res = _bicayley_try(d, D, n, rng, slice_s)
        if res is not None:
            if res[0] > state[0][0]:
                state[0] = res
            lo = max(lo, n)
            if hi is None:
                n = int(n * 1.02) + 1
            else:
                n = (lo + hi) // 2
        else:
            hi = n if hi is None else min(hi, n)
            n = (lo + hi) // 2
        if hi is not None and hi - lo <= 1:
            break


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.9 * time_limit, time_limit - 4.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    state = [lib.haar_graph(d, range(d))]

    def consider(cand):
        n, e = cand
        if n > state[0][0] and lib.is_valid(n, e, d, D):
            state[0] = (n, e)

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg)
            if D == 3 and lib.is_prime_power(d - 1):
                return state[0]

    try:
        _bicayley_phase(d, D, rng, state, deadline)
    except Exception:
        pass

    best = state[0]
    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
