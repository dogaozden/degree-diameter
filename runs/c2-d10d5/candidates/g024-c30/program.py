import random
import time
import itertools

import lib


# ----------------------------------------------------------------------------
# New construction family: cyclic Haar graphs H(m, S).
#
# Vertices a_i and b_j (i, j in Z_m); a_i ~ b_{i+s} for s in S, |S| = d.
# The graph is d-regular and bipartite. Translations act transitively on each
# side, so the diameter bound only needs BFS from a_0 and b_0. One BFS costs
# O(m d), so simulated annealing over the connection set S is cheap in C.
#
# Cost of S = number of vertices not within distance D of a_0 or b_0.
# Moves replace one element of S. For a fixed m, annealing either reaches cost
# 0 (valid graph with 2m vertices) or the attempt is abandoned. Successful m
# values are kept, and later candidates are drawn slightly above the best.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define ITERS 40000

static uint64_t rs;
static uint64_t rnd64(void) {
    uint64_t x = rs;
    x ^= x >> 12;
    x ^= x << 25;
    x ^= x >> 27;
    rs = x;
    return x * 2685821657736338717ULL;
}
static double rnd01(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}
static int rndint(int n) {
    return (int)(rnd64() % (uint64_t)n);
}

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + (double)ts.tv_nsec * 1e-9;
}

static int DEG, DIAM;
static int M;
static int *S, *bestS;
static int *mark, *queue, *dist;
static int stamp;
static double TEND;

/* BFS from src in Haar graph H(M, S); returns number of vertices within DIAM. */
static int bfs_count(int src) {
    stamp++;
    int head = 0, tail = 0;
    queue[tail++] = src;
    mark[src] = stamp;
    dist[src] = 0;
    int cnt = 1;
    while (head < tail) {
        int v = queue[head++];
        int dv = dist[v];
        if (dv >= DIAM) continue;
        if (v < M) {
            for (int t = 0; t < DEG; t++) {
                int w = M + (v + S[t]) % M;
                if (mark[w] != stamp) {
                    mark[w] = stamp;
                    dist[w] = dv + 1;
                    queue[tail++] = w;
                    cnt++;
                }
            }
        } else {
            int j = v - M;
            for (int t = 0; t < DEG; t++) {
                int w = (j - S[t] + M) % M;
                if (mark[w] != stamp) {
                    mark[w] = stamp;
                    dist[w] = dv + 1;
                    queue[tail++] = w;
                    cnt++;
                }
            }
        }
    }
    return cnt;
}

static int64_t cost_now(void) {
    return (int64_t)(2 * M - bfs_count(0)) + (int64_t)(2 * M - bfs_count(M));
}

static int in_set(int x, int upto) {
    for (int t = 0; t < upto; t++)
        if (S[t] == x) return 1;
    return 0;
}

/* Returns 1 on success (cost 0), 0 on failure, -1 on timeout. */
static int anneal(int iters) {
    for (int t = 0; t < DEG; t++) {
        int x;
        do {
            x = rndint(M);
        } while (in_set(x, t));
        S[t] = x;
    }
    int64_t cur = cost_now();
    for (int it = 0; it < iters; it++) {
        if (cur == 0) return 1;
        if ((it & 127) == 0 && now_s() > TEND) return -1;
        int t = rndint(DEG);
        int old = S[t];
        int nw = rndint(M);
        if (in_set(nw, DEG)) continue;
        S[t] = nw;
        int64_t c2 = cost_now();
        double T = 2.0 * (1.0 - (double)it / iters) + 0.05;
        if (c2 <= cur || rnd01() < exp(-(double)(c2 - cur) / T)) {
            cur = c2;
        } else {
            S[t] = old;
        }
    }
    return cur == 0 ? 1 : 0;
}

int main(int argc, char **argv) {
    if (argc < 7) {
        printf("0 0\n");
        return 0;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    int mstart = atoi(argv[3]);
    int mcap = atoi(argv[4]);
    unsigned long long seed = strtoull(argv[5], NULL, 10);
    double TL = atof(argv[6]);

    if (DEG < 2 || DIAM < 1 || mcap < DEG + 1) {
        printf("0 0\n");
        return 0;
    }

    rs = (seed + 1) * 0x9E3779B97F4A7C15ULL ^ 0xD1B54A32D192ED03ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 8; i++) rnd64();

    S = malloc(sizeof(int) * (size_t)DEG);
    bestS = malloc(sizeof(int) * (size_t)DEG);
    mark = calloc((size_t)(2 * mcap), sizeof(int));
    queue = malloc(sizeof(int) * (size_t)(2 * mcap));
    dist = malloc(sizeof(int) * (size_t)(2 * mcap));
    if (!S || !bestS || !mark || !queue || !dist) {
        printf("0 0\n");
        return 0;
    }

    TEND = now_s() + TL;

    if (mstart < DEG + 1) mstart = DEG + 1;
    if (mstart > mcap) mstart = mcap;

    int lo = 0, bestM = 0;
    int mcur = mstart;
    while (now_s() < TEND) {
        int m;
        if (lo == 0) {
            m = mcur;
        } else {
            m = lo + 1 + rndint(lo / 100 + 2);
        }
        if (m > mcap) m = mcap;
        if (m <= lo) break;
        if (m < DEG + 1) m = DEG + 1;
        M = m;
        int r = anneal(ITERS);
        if (r < 0) break;
        if (r == 1) {
            lo = m;
            bestM = m;
            memcpy(bestS, S, sizeof(int) * (size_t)DEG);
        } else if (lo == 0) {
            mcur -= 1 + rndint(mcur / 100 + 2);
            if (mcur < DEG + 1) mcur = DEG + 1;
        }
    }

    if (!bestM) {
        printf("0 0\n");
        return 0;
    }
    long long nedges = (long long)bestM * DEG;
    printf("%d %lld\n", 2 * bestM, nedges);
    for (int i = 0; i < bestM; i++)
        for (int t = 0; t < DEG; t++)
            printf("%d %d\n", i, bestM + (i + bestS[t]) % bestM);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact construction: incidence graph of PG(2, q), used when it applies.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Main build: exact constructions, then the Haar-graph annealing in C.
# ----------------------------------------------------------------------------

_MAX_CAP = 2_000_000  # keeps C allocations and parsing safe


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} (Haar graph with S = all residues), diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

    if D >= 3:
        try:
            pg = _best_pg(d)
        except Exception:
            pg = None
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    # Main search: annealed cyclic Haar graphs, entirely in C.
    if d >= 3 and D >= 3:
        remaining = start + budget - time.monotonic()
        if remaining > 2.0:
            cap_vertices = min(lib.moore_bound(d, D), _MAX_CAP)
            mcap = cap_vertices // 2
            mstart = max(d + 1, best_n // 2)
            if mcap >= d + 1 and mstart <= mcap:
                try:
                    text = lib.run_c(
                        C_SOURCE,
                        [d, D, mstart, mcap, int(seed) & 0x7FFFFFFF, round(remaining, 2)],
                        timeout=remaining + 20.0,
                    )
                    n2, e2 = lib.parse_graph_text(text)
                    consider(n2, e2)
                except Exception:
                    pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
