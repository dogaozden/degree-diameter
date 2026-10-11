import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# New search: tabu search over voltages of bi-Cayley lifts on semidirect
# products Z_m x|_r Z_k2 (element (a, b) coded as a*k2 + b).
#
# Base graph: K vertices per side, DEG layers, each layer a permutation of
# 0..K-1, so every vertex has degree DEG. Dart e = l*K + i joins A_i to
# B_{dJ[e]} with voltage dS[e]: A_{i,g} ~ B_{j,g*s} for all g. Left
# multiplication is an automorphism, so one BFS per block representative
# decides the diameter exactly.
#
# Instead of annealing one random move at a time, each step samples a batch
# of candidate moves, applies the best non-tabu one (aspiration allowed when
# it beats the global best), and forbids undoing it for a short tenure.
# Stagnant runs restart either from the global best with a kick or from a
# fresh random lift. Graphs are tried at orders just above the current best.
#
# Usage: prog d D K m k2 r seed slice_seconds
# Prints a graph ("n m" + edges) when cost 0 is reached, else "0 0".
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define PEN 1000
#define BIGC 0x3fffffff
#define SAMP 240
#define STAG 400

static int DEG, DIAM, K, MM, K2, G, N, NE;
static int *POWR, *dI, *dJ, *dS, *permv, *adj, *cnt, *fr, *nx;
static int *bestS, *bestJ, *tabu, *P;
static uint32_t *vis;
static uint32_t stamp = 0;
static uint64_t rs = 88172645463325252ULL;
static int gitr = 1;

static inline uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static inline int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static inline double rnd01(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}
static double elapsed(clock_t t0) {
    return (double)(clock() - t0) / (double)CLOCKS_PER_SEC;
}
static int gcd_int(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static int gmul(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, dd = y % K2;
    long long t = (a + (long long)POWR[b] * c) % MM;
    return (int)(t * K2 + (b + dd) % K2);
}

static void set_perm(int e) {
    int s = dS[e];
    int *pm = permv + (size_t)e * G;
    for (int g = 0; g < G; g++) pm[g] = gmul(g, s);
}

static int cost_fn(void) {
    int dup = 0;
    for (int e1 = 0; e1 < NE; e1++)
        for (int e2 = e1 + 1; e2 < NE; e2++)
            if (dI[e1] == dI[e2] && dJ[e1] == dJ[e2] && dS[e1] == dS[e2]) dup++;

    memset(cnt, 0, sizeof(int) * (size_t)N);
    for (int e = 0; e < NE; e++) {
        int ba = dI[e] * G, bb = (K + dJ[e]) * G;
        const int *pm = permv + (size_t)e * G;
        for (int g = 0; g < G; g++) {
            int a = ba + g, b = bb + pm[g];
            adj[(size_t)a * DEG + cnt[a]++] = b;
            adj[(size_t)b * DEG + cnt[b]++] = a;
        }
    }

    int total = 0;
    for (int ri = 0; ri < 2 * K; ri++) {
        int src = ri * G;
        if (stamp == 0xFFFFFFFFu) {
            memset(vis, 0, sizeof(uint32_t) * (size_t)N);
            stamp = 0;
        }
        stamp++;
        vis[src] = stamp;
        int *cur = fr, *nxt = nx;
        int fn = 1, reached = 1;
        cur[0] = src;
        for (int lv = 0; lv < DIAM && fn > 0; lv++) {
            int nn = 0;
            for (int q = 0; q < fn; q++) {
                const int *au = adj + (size_t)cur[q] * DEG;
                for (int t = 0; t < DEG; t++) {
                    int v = au[t];
                    if (vis[v] != stamp) {
                        vis[v] = stamp;
                        nxt[nn++] = v;
                    }
                }
            }
            reached += nn;
            int *tmp = cur; cur = nxt; nxt = tmp;
            fn = nn;
        }
        total += N - reached;
    }
    return total + PEN * dup;
}

static void save_best(void) {
    memcpy(bestS, dS, sizeof(int) * (size_t)NE);
    memcpy(bestJ, dJ, sizeof(int) * (size_t)NE);
}

static void random_init(void) {
    for (int l = 0; l < DEG; l++) {
        for (int i = 0; i < K; i++) P[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = P[i]; P[i] = P[j]; P[j] = t;
        }
        for (int i = 0; i < K; i++) {
            dI[l * K + i] = i;
            dJ[l * K + i] = P[i];
        }
    }
    for (int e = 0; e < NE; e++) {
        dS[e] = rndint(G);
        set_perm(e);
    }
}

int main(int argc, char **argv) {
    if (argc < 9) {
        printf("0 0\n");
        return 0;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    K = atoi(argv[3]);
    MM = atoi(argv[4]);
    K2 = atoi(argv[5]);
    int r = atoi(argv[6]);
    uint64_t seed = strtoull(argv[7], NULL, 10);
    double slice = atof(argv[8]);

    if (DEG < 1 || DIAM < 1 || K < 1 || MM < 1 || K2 < 1 || K2 > 4096) {
        printf("0 0\n");
        return 0;
    }
    if (gcd_int(r, MM) != 1) { printf("0 0\n"); return 0; }

    POWR = malloc(sizeof(int) * (size_t)K2);
    if (!POWR) { printf("0 0\n"); return 0; }
    POWR[0] = 1 % MM;
    for (int b = 1; b < K2; b++) POWR[b] = (int)((long long)POWR[b - 1] * r % MM);
    if (((long long)POWR[K2 - 1] * r) % MM != 1 % MM) { printf("0 0\n"); return 0; }

    G = MM * K2;
    N = 2 * K * G;
    NE = DEG * K;
    if ((long long)N > 200000) { printf("0 0\n"); return 0; }

    rs = seed * 0x9E3779B97F4A7C15ULL ^ 0x1234567ULL;
    if (rs == 0) rs = 1;

    dI = calloc(NE, sizeof(int));
    dJ = calloc(NE, sizeof(int));
    dS = calloc(NE, sizeof(int));
    bestS = calloc(NE, sizeof(int));
    bestJ = calloc(NE, sizeof(int));
    permv = calloc((size_t)NE * G, sizeof(int));
    tabu = calloc((size_t)NE * G, sizeof(int));
    adj = calloc((size_t)N * DEG, sizeof(int));
    cnt = calloc(N, sizeof(int));
    fr = calloc(N, sizeof(int));
    nx = calloc(N, sizeof(int));
    vis = calloc(N, sizeof(uint32_t));
    P = calloc(K, sizeof(int));
    if (!dI || !dJ || !dS || !bestS || !bestJ || !permv || !tabu ||
        !adj || !cnt || !fr || !nx || !vis || !P) {
        printf("0 0\n");
        return 0;
    }

    clock_t t0 = clock();
    int gbest = BIGC, found = 0;

    while (!found && elapsed(t0) < slice) {
        if (gbest < BIGC && rnd01() < 0.5) {
            memcpy(dS, bestS, sizeof(int) * (size_t)NE);
            memcpy(dJ, bestJ, sizeof(int) * (size_t)NE);
            int kick = 1 + NE / 6;
            for (int q = 0; q < kick; q++) {
                if (K > 1 && rnd01() < 0.3) {
                    int l = rndint(DEG);
                    int i1 = rndint(K), i2 = rndint(K - 1);
                    if (i2 >= i1) i2++;
                    int t = dJ[l * K + i1];
                    dJ[l * K + i1] = dJ[l * K + i2];
                    dJ[l * K + i2] = t;
                } else {
                    dS[rndint(NE)] = rndint(G);
                }
            }
            for (int e = 0; e < NE; e++) set_perm(e);
        } else {
            random_init();
        }

        int cur = cost_fn();
        if (cur < gbest) { gbest = cur; save_best(); }
        if (cur == 0) { found = 1; break; }

        int localBest = cur, stall = 0, done = 0;
        for (int it = 0; !done; it++) {
            if ((it & 7) == 0 && elapsed(t0) >= slice) break;

            int bc = BIGC, bType = -1, b1 = 0, b2 = 0;
            for (int s = 0; s < SAMP; s++) {
                if (K > 1 && rnd01() < 0.25) {
                    int l = rndint(DEG);
                    int i1 = rndint(K), i2 = rndint(K - 1);
                    if (i2 >= i1) i2++;
                    int e1 = l * K + i1, e2 = l * K + i2;
                    int t = dJ[e1]; dJ[e1] = dJ[e2]; dJ[e2] = t;
                    int c = cost_fn();
                    t = dJ[e1]; dJ[e1] = dJ[e2]; dJ[e2] = t;
                    if (c < bc || (c == bc && rnd01() < 0.5)) {
                        bc = c; bType = 1; b1 = e1; b2 = e2;
                    }
                } else {
                    int e = rndint(NE), ns = rndint(G);
                    if (ns == dS[e]) continue;
                    int tabuHit = tabu[(size_t)e * G + ns] > gitr;
                    int old = dS[e];
                    dS[e] = ns; set_perm(e);
                    int c = cost_fn();
                    dS[e] = old; set_perm(e);
                    if (tabuHit && c >= gbest) continue;
                    if (c < bc || (c == bc && rnd01() < 0.5)) {
                        bc = c; bType = 0; b1 = e; b2 = ns;
                    }
                }
            }
            if (bType < 0) continue;

            if (bType == 1) {
                int t = dJ[b1]; dJ[b1] = dJ[b2]; dJ[b2] = t;
            } else {
                int e = b1;
                int old = dS[e];
                tabu[(size_t)e * G + old] = gitr + 4 + rndint(8);
                dS[e] = b2;
                set_perm(e);
            }
            gitr++;
            cur = bc;

            if (cur < localBest) { localBest = cur; stall = 0; }
            else stall++;
            if (cur < gbest) { gbest = cur; save_best(); }
            if (cur == 0) { found = 1; done = 1; }
            else if (stall > STAG) done = 1;
        }
    }

    if (found) {
        printf("%d %d\n", N, NE * G);
        for (int e = 0; e < NE; e++) {
            for (int g = 0; g < G; g++) {
                printf("%d %d\n", dI[e] * G + g, (K + dJ[e]) * G + permv[(size_t)e * G + g]);
            }
        }
    } else {
        printf("0 0\n");
    }
    fflush(stdout);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact construction and sampling helpers.
# ----------------------------------------------------------------------------

# Known record orders used as a target floor: the search only accepts graphs
# strictly larger than this (plus two, the vertex pair granularity).
RECORD_HINT = {(7, 5): 1134}

SLICE = 6.0                      # seconds per C run
K_CHOICES = [1, 1, 1, 2, 2, 3]   # base-graph sizes (vertices per side)


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _sample_semidirect(G, rng):
    """Return (m, k2, r) with Z_m x|_r Z_k2 of order m*k2 = G, r^k2 = 1 mod m, gcd(r, m) = 1."""
    divs = [k for k in range(1, G + 1) if G % k == 0 and G // k >= 2]
    rng.shuffle(divs)
    for k2 in divs:
        m = G // k2
        if k2 == 1:
            return m, 1, 1
        rs = [r for r in range(1, m) if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
        if rs:
            nontriv = [r for r in rs if r != 1]
            if nontriv and rng.random() < 0.7:
                return m, k2, rng.choice(nontriv)
            return m, k2, rng.choice(rs)
    return G, 1, 1


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - 8.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    if not lib.is_valid(best[0], best[1], d, D):
        best = (1, [])

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

    # Search for bi-Cayley lifts strictly larger than the current floor.
    min_n = best[0] + 2
    if (d, D) in RECORD_HINT:
        min_n = max(min_n, RECORD_HINT[(d, D)] + 2)

    search_deadline = deadline - 1.0
    failures = 0
    while True:
        remaining = search_deadline - time.monotonic()
        if remaining < 2.0:
            break
        sl = min(SLICE, remaining)
        K = rng.choice(K_CHOICES)
        G = -(-min_n // (2 * K)) + rng.randrange(0, 6)
        m, k2, r = _sample_semidirect(G, rng)
        try:
            out = lib.run_c(
                C_SOURCE,
                [d, D, K, m, k2, r, rng.randrange(1, 10 ** 9), f"{sl:.2f}"],
                timeout=sl + 8.0,
            )
        except RuntimeError:
            failures += 1
            if failures >= 3:
                break
            continue
        try:
            n, e = lib.parse_graph_text(out)
        except ValueError:
            continue
        if n >= min_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            min_n = n + 2

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
        if not lib.is_valid(best[0], best[1], d, D):
            best = (1, [])
    return best
