import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bold change: single-vertex-per-side bi-Cayley lifts (K = 1).
#
# Group G = Z_m x|_r Z_k2 (element (a, b) coded as a*k2 + b, identity = 0).
# Vertices: A_g = g and B_g = G + g. Connection set S = {s_0, ..., s_{DEG-1}},
# all distinct. Edges: A_g ~ B_{g*s} for every s in S. Left multiplication is an
# automorphism, so the excess-distance BFS from A_1 and B_1 decides the diameter
# exactly, and each BFS covers only 2G vertices.
#
# Search: simulated annealing over the DEG elements of S, with a
# cost that is zero iff the lift has diameter <= DIAM. Each call handles one
# group order, so the driver scans many group orders and group structures.
#
# Usage: prog d D m k2 r seed slice_seconds
# Prints a valid graph ("n m" + edges) or "0 0".
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define BIGCOST (1 << 30)

static int DEG, DIAM, MM, K2, G, N;
static int *POWR, *invT, *S, *Sbest, *adj, *fr, *nx;
static uint32_t *vis;
static uint32_t stamp = 0;
static uint64_t rs = 88172645463325252ULL;

static inline uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static inline int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static inline double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double elapsed(clock_t t0) {
    return (double)(clock() - t0) / (double)CLOCKS_PER_SEC;
}

static int gmul(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, d = y % K2;
    long long t = (a + (long long)POWR[b] * c) % MM;
    return (int)(t * K2 + (b + d) % K2);
}

/* Rebuild the adjacency entries for column t (dart S[t]). */
static void set_col(int t) {
    int s = S[t], si = invT[s];
    for (int g = 0; g < G; g++) {
        adj[(size_t)g * DEG + t] = G + gmul(g, s);          /* A_g -> B_{g s} */
        adj[(size_t)(G + g) * DEG + t] = gmul(g, si);        /* B_x -> A_{x s^-1} */
    }
}

static int has_dup_in(int val, int t) {
    for (int u = 0; u < DEG; u++) if (u != t && S[u] == val) return 1;
    return 0;
}

/* Excess-distance cost from the two representatives A_1 (vertex 0) and B_1 (vertex G). */
static int cost_fn(void) {
    const int LMAX = DIAM + 3;
    const int UNREACH_W = LMAX - DIAM + 2;
    int total = 0;
    int srcs[2] = {0, G};
    for (int si = 0; si < 2; si++) {
        if (stamp == 0xFFFFFFFFu) {
            memset(vis, 0, sizeof(uint32_t) * (size_t)N);
            stamp = 0;
        }
        stamp++;
        int src = srcs[si];
        vis[src] = stamp;
        int *cur = fr, *nxt = nx;
        int fn = 1, reached = 1;
        cur[0] = src;
        for (int lv = 0; lv < LMAX && fn > 0; lv++) {
            int nn = 0;
            for (int q = 0; q < fn; q++) {
                int u = cur[q];
                const int *au = adj + (size_t)u * DEG;
                for (int t = 0; t < DEG; t++) {
                    int v = au[t];
                    if (vis[v] != stamp) {
                        vis[v] = stamp;
                        nxt[nn++] = v;
                    }
                }
            }
            reached += nn;
            if (lv + 1 > DIAM) total += (lv + 1 - DIAM) * nn;
            int *tmp = cur; cur = nxt; nxt = tmp;
            fn = nn;
        }
        total += (N - reached) * UNREACH_W;
    }
    return total;
}

int main(int argc, char **argv) {
    if (argc < 8) {
        printf("0 0\n");
        return 0;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    MM = atoi(argv[3]);
    K2 = atoi(argv[4]);
    int r = atoi(argv[5]);
    uint64_t seed = strtoull(argv[6], NULL, 10);
    double slice = atof(argv[7]);

    if (DEG < 1 || DIAM < 1 || MM < 1 || K2 < 1 || K2 > 4096) { printf("0 0\n"); return 0; }
    if ((long long)MM * K2 > 100000) { printf("0 0\n"); return 0; }
    G = MM * K2;
    if (G < DEG) { printf("0 0\n"); return 0; }
    r = ((r % MM) + MM) % MM;

    POWR = malloc(sizeof(int) * (size_t)K2);
    if (!POWR) { printf("0 0\n"); return 0; }
    POWR[0] = 1 % MM;
    for (int b = 1; b < K2; b++) POWR[b] = (int)((long long)POWR[b - 1] * r % MM);
    if (((long long)POWR[K2 - 1] * r) % MM != 1 % MM) { printf("0 0\n"); return 0; }

    N = 2 * G;
    rs = seed * 0x9E3779B97F4A7C15ULL ^ 0x7654321ULL;
    if (rs == 0) rs = 1;

    S = malloc(sizeof(int) * DEG);
    Sbest = malloc(sizeof(int) * DEG);
    invT = malloc(sizeof(int) * G);
    adj = malloc(sizeof(int) * (size_t)N * DEG);
    fr = malloc(sizeof(int) * N);
    nx = malloc(sizeof(int) * N);
    vis = calloc(N, sizeof(uint32_t));
    if (!S || !Sbest || !invT || !adj || !fr || !nx || !vis) { printf("0 0\n"); return 0; }

    for (int s = 0; s < G; s++) {
        int ok = 0;
        for (int t = 0; t < G; t++) {
            if (gmul(s, t) == 0) { invT[s] = t; ok = 1; break; }
        }
        if (!ok) { printf("0 0\n"); return 0; }
    }

    clock_t t0 = clock();
    int found = 0;
    int bestCost = BIGCOST;
    const int RL = 40000;
    const int STAG = 6000;

    while (!found && elapsed(t0) < slice) {
        double T0;
        if (bestCost >= BIGCOST || rnd01() < 0.4) {
            for (int t = 0; t < DEG; t++) {
                int v;
                do { v = rndint(G); } while (has_dup_in(v, t));
                S[t] = v;
            }
            for (int t = 0; t < DEG; t++) set_col(t);
            T0 = 2.0;
        } else {
            memcpy(S, Sbest, sizeof(int) * DEG);
            for (int t = 0; t < DEG; t++) set_col(t);
            int kick = 1 + rndint(2);
            for (int k = 0; k < kick; k++) {
                int t = rndint(DEG);
                int v;
                do { v = rndint(G); } while (has_dup_in(v, t));
                S[t] = v;
                set_col(t);
            }
            T0 = 0.7;
        }

        int cur = cost_fn();
        if (cur < bestCost) { bestCost = cur; memcpy(Sbest, S, sizeof(int) * DEG); }
        if (cur == 0) { found = 1; break; }

        int runBest = cur;
        int since = 0;
        for (int it = 0; it < RL; it++) {
            if ((it & 127) == 0 && elapsed(t0) >= slice) break;
            double T = T0 * (1.0 - (double)it / RL) + 0.03;
            int t = rndint(DEG);
            int old = S[t];
            int v = rndint(G);
            if (v == old || has_dup_in(v, t)) continue;
            S[t] = v;
            set_col(t);
            int nc = cost_fn();
            if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
                cur = nc;
            } else {
                S[t] = old;
                set_col(t);
            }
            if (cur < bestCost) { bestCost = cur; memcpy(Sbest, S, sizeof(int) * DEG); }
            if (cur == 0) { found = 1; break; }
            if (cur < runBest) { runBest = cur; since = 0; }
            else if (++since > STAG) break;
        }
    }

    if (found) {
        printf("%d %d\n", N, G * DEG);
        for (int g = 0; g < G; g++) {
            for (int t = 0; t < DEG; t++) {
                printf("%d %d\n", g, G + gmul(g, S[t]));
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
# Safe constructions and glue.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d (diameter 3)."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _group_for_order(G, rng):
    """Return (m, k2, r) with Z_m x|_r Z_k2 of order exactly G, or None."""
    divs = [k for k in range(1, min(G, 4096) + 1) if G % k == 0 and G // k >= 2]
    if not divs:
        return None
    k2 = rng.choice(divs)
    m = G // k2
    r = 1
    if k2 > 1:
        cands = [c for c in range(2, m) if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m]
        if cands and rng.random() < 0.7:
            r = rng.choice(cands)
    return m, k2, r


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for every D >= 2.
    best = lib.haar_graph(d, range(d))

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

    # Bi-Cayley K = 1 lift search. Vertices = 2G, so target G near (record / 2).
    moore = lib.moore_bound(d, D)
    hi = max(2, int(0.38 * moore / 2))

    while True:
        remaining = deadline - time.monotonic()
        if remaining < 3.0:
            break
        slice_s = min(remaining - 2.0, 6.0)
        lo_g = best[0] // 2
        if hi <= lo_g:
            hi = lo_g + 3
        G = rng.randint(lo_g + 1, hi)
        grp = _group_for_order(G, rng)
        if grp is None:
            hi = max(lo_g + 1, hi - 1)
            continue
        m, k2, r = grp
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
            hi = max(lo_g + 1, hi - 2)
            continue
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
            hi = max(hi, n // 2 + 3)
        else:
            hi = max(lo_g + 1, hi - 2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
