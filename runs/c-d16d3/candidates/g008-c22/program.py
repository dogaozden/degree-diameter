import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing over bi-Cayley voltage lifts.
#
# Group: G = M*K2 elements, coded (a, b) -> a*K2 + b, with
#   (a, b)(c, e) = (a + R^b * c, b + e), i.e. Z_M semidirect Z_K2 (R^K2 = 1 mod M).
# Base: K vertices per side. Layer L has one dart per A-index i, mapping A_i to
# B_{P[L][i]} with voltage S[L][i]; each P[L] is a permutation, so every vertex
# has degree d. Edge: (A_i, g) -- (B_j, g * s).
#
# Left multiplication is an automorphism that is transitive on each layer, so
# distances need only be checked from one representative per layer (2K BFS runs).
# Cost = number of (representative, vertex) pairs not reached within D, plus a
# large penalty for duplicate darts. Cost 0 means a valid graph.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define BIGC 1000000000L

static int d, D, K, M, K2, R, G, N, NDART;
static int *pw, *Pm, *Sv, *adjb, *degc, *vis, *que;
static int stamp = 0;
static uint64_t rs = 88172645463325252ULL;

static uint64_t nxt(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int n) { return (int)(nxt() % (uint64_t)n); }
static double rndu(void) { return (double)(nxt() >> 11) * (1.0 / 9007199254740992.0); }
static double elapsed(void) { return (double)clock() / CLOCKS_PER_SEC; }

static int gmul(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, e = y % K2;
    return ((a + pw[b] * c) % M) * K2 + (b + e) % K2;
}

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static int has_dup(void) {
    for (int a = 0; a < NDART; a++)
        for (int b = a + 1; b < NDART; b++)
            if (a % K == b % K && Pm[a] == Pm[b] && Sv[a] == Sv[b]) return 1;
    return 0;
}

static long evalc(void) {
    if (has_dup()) return BIGC;
    for (int v = 0; v < N; v++) degc[v] = 0;
    for (int a = 0; a < NDART; a++) {
        int i = a % K, j = Pm[a], s = Sv[a];
        for (int g = 0; g < G; g++) {
            int u = i * G + g;
            int w = (K + j) * G + gmul(g, s);
            adjb[u * d + degc[u]++] = w;
            adjb[w * d + degc[w]++] = u;
        }
    }
    long total = 0;
    for (int t = 0; t < 2 * K; t++) {
        int src = t * G;
        stamp++;
        int head = 0, tail = 0;
        vis[src] = stamp;
        que[tail++] = src;
        for (int lv = 0; lv < D && head < tail; lv++) {
            int end = tail;
            for (; head < end; head++) {
                int u = que[head];
                for (int k = 0; k < d; k++) {
                    int w = adjb[u * d + k];
                    if (vis[w] != stamp) { vis[w] = stamp; que[tail++] = w; }
                }
            }
        }
        total += N - tail;
    }
    return total;
}

static void output(void) {
    printf("%d %d\n", N, NDART * G);
    for (int a = 0; a < NDART; a++) {
        int i = a % K, j = Pm[a], s = Sv[a];
        for (int g = 0; g < G; g++)
            printf("%d %d\n", i * G + g, (K + j) * G + gmul(g, s));
    }
}

int main(int argc, char **argv) {
    if (argc < 9) { printf("0 0\n"); return 0; }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double secs = atof(argv[4]);
    M = atoi(argv[5]);
    K2 = atoi(argv[6]);
    R = atoi(argv[7]);
    K = atoi(argv[8]);
    if (d < 1 || D < 1 || K < 1 || M < 1 || K2 < 1) { printf("0 0\n"); return 0; }
    G = M * K2;
    if (G < 2) { printf("0 0\n"); return 0; }
    if (K2 > 1) {
        if (gcd_i(R % M, M) != 1) { printf("0 0\n"); return 0; }
        long p = 1 % M;
        for (int b = 0; b < K2; b++) p = p * (R % M) % M;
        if (p != 1 % M) { printf("0 0\n"); return 0; }
    }
    pw = malloc(sizeof(int) * K2);
    pw[0] = 1 % M;
    for (int b = 1; b < K2; b++) pw[b] = (int)((long)pw[b - 1] * (R % M) % M);

    N = 2 * K * G;
    NDART = d * K;
    Pm = malloc(sizeof(int) * NDART);
    Sv = malloc(sizeof(int) * NDART);
    adjb = malloc(sizeof(int) * (size_t)N * d);
    degc = malloc(sizeof(int) * N);
    vis = calloc(N, sizeof(int));
    que = malloc(sizeof(int) * N);

    rs = (uint64_t)seed * 2654435761ULL + 88172645463325252ULL;
    if (rs == 0) rs = 1;

    double t0 = elapsed();
    const long ITERS = 40000;
    double logr = log(0.02 / 2.0);

    while (1) {
        for (int L = 0; L < d; L++) {
            for (int i = 0; i < K; i++) Pm[L * K + i] = i;
            for (int i = K - 1; i > 0; i--) {
                int r = rndi(i + 1);
                int t = Pm[L * K + i];
                Pm[L * K + i] = Pm[L * K + r];
                Pm[L * K + r] = t;
            }
        }
        for (int a = 0; a < NDART; a++) Sv[a] = rndi(G);
        long cost = evalc();
        for (long it = 0; it < ITERS && cost != 0; it++) {
            if ((it & 255) == 0 && elapsed() - t0 > secs) { printf("0 0\n"); return 0; }
            double T = 2.0 * exp(logr * (double)it / (double)ITERS);
            if (K > 1 && rndi(10) < 3) {
                int L = rndi(d), x = rndi(K), y = rndi(K);
                if (x == y) continue;
                int ax = L * K + x, ay = L * K + y;
                int t = Pm[ax]; Pm[ax] = Pm[ay]; Pm[ay] = t;
                long c2 = evalc();
                if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / T)) cost = c2;
                else { t = Pm[ax]; Pm[ax] = Pm[ay]; Pm[ay] = t; }
            } else {
                int a = rndi(NDART);
                int old = Sv[a];
                int nw = rndi(G);
                if (nw == old) continue;
                Sv[a] = nw;
                long c2 = evalc();
                if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / T)) cost = c2;
                else Sv[a] = old;
            }
        }
        if (cost == 0) { output(); return 0; }
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python glue
# ----------------------------------------------------------------------------

def _pg_fallback(d, D):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d (diameter 3)."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            n, e = lib.projective_plane_incidence(q)
            if lib.is_valid(n, e, d, D):
                return n, e
            return None
    return None


def _group_choices(G, rng):
    """Return (M, K2, R) triples with M * K2 = G and R^K2 = 1 mod M, gcd(R, M) = 1."""
    opts = []
    for k2 in range(1, 13):
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            opts.append((m, 1, 1))
            continue
        rs = [r for r in range(1, m)
              if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
        for r in rs:
            opts.append((m, k2, r))
    return opts


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    deadline = t0 + 0.80 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    if not lib.is_valid(best[0], best[1], d, D):
        best = (1, [])

    if D >= 3:
        pg = _pg_fallback(d, D)
        if pg is not None and pg[0] > best[0]:
            best = pg

    best_n = best[0]

    # Search for larger bi-Cayley lifts in C (only if there is room under the Moore bound).
    if d >= 3 and D >= 3 and best_n < lib.moore_bound(d, D):
        while time.monotonic() < deadline - 1.0:
            k = rng.choice([1, 1, 2])
            G = best_n // (2 * k) + 1 + rng.randrange(0, 4)
            opts = _group_choices(G, rng)
            if not opts:
                continue
            M, K2, R = rng.choice(opts)
            budget = min(6.0, deadline - time.monotonic() - 0.5)
            if budget < 0.5:
                break
            try:
                text = lib.run_c(
                    C_SOURCE,
                    [d, D, rng.randrange(1, 1 << 30), f"{budget:.2f}", M, K2, R, k],
                    timeout=budget + 15,
                )
                n, e = lib.parse_graph_text(text)
            except Exception:
                continue
            if n > best_n and e and lib.is_valid(n, e, d, D):
                best = (n, e)
                best_n = n

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
