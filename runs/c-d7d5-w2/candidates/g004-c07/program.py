import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C search engine: Haar-type bi-Cayley graphs over a fixed group G = Z_m x|_r Z_k2.
#
# Vertices: A_g = g (0..G-1), B_h = G + h. Connection set S = {s_0..s_{DEG-1}},
# distinct group elements. Edge A_g ~ B_{g*s_i} for every g and i. Left
# multiplication is an automorphism, so the diameter is decided by two BFS runs,
# from A_e and from B_e. Cost = unreached (source, vertex) pairs over both BFS.
#
# Search: simulated annealing over single replacements s_i -> x (x not in S),
# with fresh random restarts when a run ends. Stops when cost is 0.
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

#define RL 20000
#define TSTART 6.0
#define TEND 0.3
#define GMAX 2500

static int DEG, DIAM, MM, K2, G;
static int *POWR, *MT, *INV, *S, *SI, *fr, *nx;
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

static int gcd_int(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static int gmul(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, dd = y % K2;
    long long t = (a + (long long)POWR[b] * c) % MM;
    return (int)(t * K2 + (b + dd) % K2);
}

static int bfs_unreached(int src) {
    if (stamp == 0xFFFFFFFFu) {
        memset(vis, 0, sizeof(uint32_t) * (size_t)(2 * G));
        stamp = 0;
    }
    stamp++;
    int *cur = fr, *nxt = nx;
    int fn = 1, reached = 1;
    vis[src] = stamp;
    cur[0] = src;
    for (int lv = 0; lv < DIAM && fn > 0; lv++) {
        int nn = 0;
        for (int q = 0; q < fn; q++) {
            int u = cur[q];
            if (u < G) {
                const int *row = MT + (size_t)u * G;
                for (int i = 0; i < DEG; i++) {
                    int v = G + row[S[i]];
                    if (vis[v] != stamp) { vis[v] = stamp; nxt[nn++] = v; }
                }
            } else {
                const int *row = MT + (size_t)(u - G) * G;
                for (int i = 0; i < DEG; i++) {
                    int v = row[SI[i]];
                    if (vis[v] != stamp) { vis[v] = stamp; nxt[nn++] = v; }
                }
            }
        }
        reached += nn;
        int *tmp = cur; cur = nxt; nxt = tmp;
        fn = nn;
    }
    return 2 * G - reached;
}

static int cost_fn(void) {
    return bfs_unreached(0) + bfs_unreached(G);
}

static int in_S(int x) {
    for (int i = 0; i < DEG; i++) if (S[i] == x) return 1;
    return 0;
}

static int in_prefix(int x, int upto) {
    for (int i = 0; i < upto; i++) if (S[i] == x) return 1;
    return 0;
}

static void print_graph(void) {
    printf("%d %d\n", 2 * G, DEG * G);
    for (int i = 0; i < DEG; i++) {
        for (int g = 0; g < G; g++) {
            printf("%d %d\n", g, G + MT[(size_t)g * G + S[i]]);
        }
    }
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

    if (DEG < 1 || DIAM < 1 || MM < 2 || K2 < 1) { printf("0 0\n"); return 0; }
    if (r < 1 || r >= MM || gcd_int(r, MM) != 1) { printf("0 0\n"); return 0; }
    G = MM * K2;
    if (G > GMAX || G < DEG + 1) { printf("0 0\n"); return 0; }

    POWR = malloc(sizeof(int) * (size_t)K2);
    if (!POWR) { printf("0 0\n"); return 0; }
    POWR[0] = 1 % MM;
    for (int b = 1; b < K2; b++) POWR[b] = (int)((long long)POWR[b - 1] * r % MM);
    if (((long long)POWR[K2 - 1] * r) % MM != 1 % MM) { printf("0 0\n"); return 0; }

    MT = malloc(sizeof(int) * (size_t)G * (size_t)G);
    INV = malloc(sizeof(int) * (size_t)G);
    S = malloc(sizeof(int) * (size_t)DEG);
    SI = malloc(sizeof(int) * (size_t)DEG);
    fr = malloc(sizeof(int) * (size_t)(2 * G));
    nx = malloc(sizeof(int) * (size_t)(2 * G));
    vis = calloc((size_t)(2 * G), sizeof(uint32_t));
    if (!MT || !INV || !S || !SI || !fr || !nx || !vis) { printf("0 0\n"); return 0; }

    for (int x = 0; x < G; x++)
        for (int y = 0; y < G; y++)
            MT[(size_t)x * G + y] = gmul(x, y);
    for (int x = 0; x < G; x++) {
        INV[x] = -1;
        for (int y = 0; y < G; y++) {
            if (MT[(size_t)x * G + y] == 0) { INV[x] = y; break; }
        }
        if (INV[x] < 0) { printf("0 0\n"); return 0; }
    }

    rs = seed * 0x9E3779B97F4A7C15ULL ^ 0x7654321ULL;
    if (rs == 0) rs = 1;
    for (int k = 0; k < 10; k++) rnd64();

    clock_t t0 = clock();
    int found = 0;
    while (!found && elapsed(t0) < slice) {
        for (int i = 0; i < DEG; i++) {
            int x;
            do { x = rndint(G); } while (in_prefix(x, i));
            S[i] = x;
        }
        for (int i = 0; i < DEG; i++) SI[i] = INV[S[i]];
        int cur = cost_fn();
        if (cur == 0) { found = 1; break; }

        for (int it = 0; it < RL; it++) {
            if ((it & 127) == 0 && elapsed(t0) >= slice) break;
            double T = TSTART * (1.0 - (double)it / RL) + TEND;
            int i = rndint(DEG);
            int old = S[i];
            int x;
            do { x = rndint(G); } while (in_S(x));
            S[i] = x;
            SI[i] = INV[x];
            int nc = cost_fn();
            if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
                cur = nc;
                if (cur == 0) { found = 1; break; }
            } else {
                S[i] = old;
                SI[i] = INV[old];
            }
        }
    }

    if (found) print_graph();
    else printf("0 0\n");
    fflush(stdout);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact construction and safe fallback.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Group enumeration. Each task is a semidirect product Z_m x|_r Z_k2 of order
# G = m * k2 (element (a, b) coded as a*k2 + b), searched for a Haar-type
# lift with connection set of size d.
# ----------------------------------------------------------------------------

def _groups_of_order(G, rng, max_r=4):
    """Return (m, k2, r) triples with m * k2 = G and r^k2 = 1 mod m, gcd(r, m) = 1."""
    out = []
    for k2 in range(1, G + 1):
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            out.append((m, 1, 1))
            continue
        cands = [c for c in range(2, m)
                 if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m]
        pick = [1]  # direct product, always valid
        if cands:
            pick += rng.sample(cands, min(max_r, len(cands)))
        for r in pick:
            out.append((m, k2, r))
    return out


def _task_list(lo, hi, rng):
    """Round-robin over orders lo..hi so that every order gets its first group before any second group."""
    per_g = []
    for G in range(lo, hi + 1):
        if G < 2 or G > 2500:
            continue
        opts = _groups_of_order(G, rng)
        rng.shuffle(opts)
        per_g.append((G, opts))
    depth = max((len(o) for _, o in per_g), default=0)
    tasks = []
    for j in range(depth):
        for G, opts in per_g:
            if j < len(opts):
                m, k2, r = opts[j]
                tasks.append((G, m, k2, r))
    return tasks


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 5.0))
    deadline = start + budget
    search_deadline = start + 0.9 * budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact construction: projective plane incidence graph (diameter 3).
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    # Bold search: Haar-type lifts over exact-order semidirect products,
    # aiming for 2G vertices with G above half the current best.
    while True:
        remaining = search_deadline - time.monotonic()
        if remaining < 1.0:
            break
        lo = max(best[0] // 2 + 1, d + 1)
        tasks = _task_list(lo, lo + 40, rng)
        if not tasks:
            break
        for G, m, k2, r in tasks:
            remaining = search_deadline - time.monotonic()
            if remaining < 1.0:
                break
            if 2 * G <= best[0]:
                continue
            slice_s = min(remaining, 2.5)
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
                continue
            if n > 0:
                consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
