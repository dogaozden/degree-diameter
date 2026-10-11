import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# New search space: K = 1 bi-Cayley graphs over a metacyclic group
# G = Z_m x|_r Z_k (element (a, b) coded as a*k + b, r^k = 1 mod m).
#
# Vertices: A_g (0..G-1) and B_x (G..2G-1). Dart i joins A_g to B_{g*s_i}.
# Left multiplication is an automorphism, so distances from A_e and from B_e
# decide the diameter exactly. Voltage s_0 = identity is WLOG (relabel B).
#
# Cost = number of vertices not reached within DIAM steps, summed over the
# two sources. Zero iff the graph is valid. The engine simulated-anneals the
# DEG-1 free voltages, then the Python driver climbs the group order G one
# step at a time, so each success raises the order.
#
# Usage: prog d D m k r seed slice_seconds
# Prints a valid graph ("n m" + edges) or "0 0".
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define PEN 1000
#define RL 30000

static int DEG, DIAM, MM, K2, G, N;
static int *POWR, *MUL, *INV, *S, *dist, *qu;
static uint64_t rs = 88172645463325252ULL;

static inline uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static inline int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static inline double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int gcd_int(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static int gmul_raw(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, dd = y % K2;
    long long t = (a + (long long)POWR[b] * c) % MM;
    return (int)(t * K2 + (b + dd) % K2);
}

static int cost_fn(void) {
    int dup = 0;
    for (int i = 0; i < DEG; i++)
        for (int j = i + 1; j < DEG; j++)
            if (S[i] == S[j]) dup++;
    if (dup) return PEN * dup;

    int total = 0;
    for (int src = 0; src < 2; src++) {
        int s0 = src * G;
        memset(dist, -1, sizeof(int) * (size_t)N);
        int head = 0, tail = 0;
        dist[s0] = 0;
        qu[tail++] = s0;
        while (head < tail) {
            int u = qu[head++];
            int du = dist[u];
            if (du >= DIAM) continue;
            if (u < G) {
                const int *row = MUL + (size_t)u * G;
                for (int i = 0; i < DEG; i++) {
                    int v = G + row[S[i]];
                    if (dist[v] < 0) { dist[v] = du + 1; qu[tail++] = v; }
                }
            } else {
                const int *row = MUL + (size_t)(u - G) * G;
                for (int i = 0; i < DEG; i++) {
                    int v = row[INV[S[i]]];
                    if (dist[v] < 0) { dist[v] = du + 1; qu[tail++] = v; }
                }
            }
        }
        total += N - tail;
    }
    return total;
}

int main(int argc, char **argv) {
    if (argc < 8) { printf("0 0\n"); return 0; }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    MM = atoi(argv[3]);
    K2 = atoi(argv[4]);
    int r = atoi(argv[5]);
    uint64_t seed = strtoull(argv[6], NULL, 10);
    double slice = atof(argv[7]);

    if (DEG < 2 || DIAM < 1 || MM < 2 || K2 < 1) { printf("0 0\n"); return 0; }
    G = MM * K2;
    if (G < DEG || G > 3000) { printf("0 0\n"); return 0; }
    if (r < 1 || gcd_int(r, MM) != 1) { printf("0 0\n"); return 0; }

    POWR = malloc(sizeof(int) * (size_t)K2);
    if (!POWR) { printf("0 0\n"); return 0; }
    POWR[0] = 1 % MM;
    for (int b = 1; b < K2; b++) POWR[b] = (int)((long long)POWR[b - 1] * r % MM);
    if (((long long)POWR[K2 - 1] * r) % MM != 1 % MM) { printf("0 0\n"); return 0; }

    MUL = malloc(sizeof(int) * (size_t)G * G);
    INV = malloc(sizeof(int) * (size_t)G);
    if (!MUL || !INV) { printf("0 0\n"); return 0; }
    for (int x = 0; x < G; x++)
        for (int y = 0; y < G; y++)
            MUL[(size_t)x * G + y] = gmul_raw(x, y);
    for (int x = 0; x < G; x++) {
        int found_inv = 0;
        for (int y = 0; y < G; y++)
            if (MUL[(size_t)x * G + y] == 0) { INV[x] = y; found_inv = 1; break; }
        if (!found_inv) { printf("0 0\n"); return 0; }
    }

    N = 2 * G;
    S = malloc(sizeof(int) * DEG);
    dist = malloc(sizeof(int) * (size_t)N);
    qu = malloc(sizeof(int) * (size_t)N);
    if (!S || !dist || !qu) { printf("0 0\n"); return 0; }

    rs = seed * 0x9E3779B97F4A7C15ULL ^ 0x7654321ULL;
    if (rs == 0) rs = 1;

    clock_t t0 = clock();
    int found = 0;
    while (!found && (double)(clock() - t0) / CLOCKS_PER_SEC < slice) {
        S[0] = 0;  /* identity voltage WLOG */
        for (int i = 1; i < DEG; i++) S[i] = rndint(G);
        int cur = cost_fn();
        if (cur == 0) { found = 1; break; }

        double T0 = 1.5;
        for (int it = 0; it < RL; it++) {
            if ((it & 255) == 0 &&
                (double)(clock() - t0) / CLOCKS_PER_SEC >= slice) break;
            double T = T0 * (1.0 - (double)it / RL) + 0.03;
            int i = 1 + rndint(DEG - 1);
            int old = S[i];
            int ns = rndint(G);
            if (ns == old) continue;
            S[i] = ns;
            int nc = cost_fn();
            if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
                cur = nc;
                if (cur == 0) { found = 1; break; }
            } else {
                S[i] = old;
            }
        }
    }

    if (!found) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", N, DEG * G);
    for (int i = 0; i < DEG; i++)
        for (int g = 0; g < G; g++)
            printf("%d %d\n", g, G + MUL[(size_t)g * G + S[i]]);
    fflush(stdout);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact constructions and safe fallbacks.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Group sampling: metacyclic Z_m x|_r Z_k2 with m * k2 = G.
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    """Return (m, k2, r) with m * k2 = G, or None if no factorisation exists."""
    divs = [k for k in range(1, G + 1) if G % k == 0 and G // k >= 2]
    if not divs:
        return None
    k2 = rng.choice(divs)
    m = G // k2
    if k2 == 1:
        return (m, 1, 1)
    cands = [c for c in range(2, m)
             if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m]
    r = rng.choice(cands) if cands else 1  # r = 1 is the direct product, always valid
    return (m, k2, r)


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 5.0))
    deadline = t0 + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if d < 2:
        return best

    # Search: climb the group order G = n / 2 of the bi-Cayley lift.
    mg = lib.moore_bound(d, D) // 2
    bestG = best[0] // 2
    step = max(1, bestG // 20)

    while True:
        remaining = deadline - time.monotonic()
        if remaining < 2.0:
            break
        if bestG >= mg:
            break
        G = min(bestG + step, mg)
        if G <= bestG:
            break
        grp = _sample_group(G, rng)
        if grp is None:
            step = max(1, step // 2)
            continue
        m, k2, r = grp
        slice_s = min(remaining - 1.0, max(3.0, min(12.0, remaining / 3.0)))
        try:
            out = lib.run_c(
                C_SOURCE,
                [d, D, m, k2, r, rng.randrange(1, 10 ** 9), f"{slice_s:.2f}"],
                timeout=slice_s + 10.0,
            )
        except RuntimeError:
            break
        try:
            n, e = lib.parse_graph_text(out)
        except ValueError:
            step = max(1, step // 2)
            continue
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
            bestG = n // 2
        else:
            step = max(1, step // 2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
