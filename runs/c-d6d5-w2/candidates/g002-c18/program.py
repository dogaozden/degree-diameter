import time

import lib


# ----------------------------------------------------------------------------
# C engine: bipartite graphs with a fixed degree, found by local search on
# double-edge swaps, not by lifts.
#
# State: a DEG-regular bipartite graph on 2H vertices. Vertex ids are unified:
# A-vertex i is id 2i and B-vertex j is id 2j+1. Every edge joins an even id
# to an odd id, so the graph is bipartite by construction.
#
# Cost: the number of ordered vertex pairs at distance > DIAM. Distances are
# computed with bitsets: reach_{k+1}[v] = reach_k[v] OR (OR over neighbours),
# and cost = sum_v (2H - |reach_DIAM[v]|). Cost 0 means the graph is valid.
#
# Moves: double-edge swaps (a1,b1),(a2,b2) -> (a1,b2),(a2,b1). They keep the
# graph regular and bipartite. Annealing accepts worse states with a
# temperature that falls over each chunk.
#
# Growth: from a valid graph on 2H vertices, pick DEG edges (a_i,b_i) with
# all a_i distinct and all b_i distinct. Add A-vertex a' joined to all b_i and
# B-vertex b' joined to all a_i, removing the picked edges. Degrees stay
# DEG, and the order rises by 2. Annealing then repairs the diameter. A
# failed repair restores the last valid graph and retries with a new matching.
#
# Start: a Haar graph (circulant bipartite graph) on 2H vertices. If it cannot
# be repaired, H shrinks until a valid graph is found.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXH 1600
#define MAXV (2 * MAXH + 4)
#define MAXW ((MAXV + 63) / 64)
#define MAXD 64
#define CHUNK1 40000
#define CHUNK2 10000

static uint64_t rs[2];
static struct timespec T0;
static double DEADLINE;
static int DEG, DIAM, H, vH;
static int *nb, *vnb, *permA;
static uint64_t *bufA, *bufB;

static uint64_t splitmix(uint64_t *x) {
    uint64_t z = (*x += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}

static uint64_t rnd64(void) {
    uint64_t s1 = rs[0];
    const uint64_t s0 = rs[1];
    rs[0] = s0;
    s1 ^= s1 << 23;
    rs[1] = s1 ^ s0 ^ (s1 >> 18) ^ (s0 >> 5);
    return rs[1] + s0;
}

static int rnd_int(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd_unit(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double elapsed(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)(ts.tv_sec - T0.tv_sec) + 1e-9 * (double)(ts.tv_nsec - T0.tv_nsec);
}

static inline int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Ordered pairs at distance > DIAM. Zero iff the graph is valid. */
static long long eval_bad(void) {
    int n = 2 * H;
    int W = (n + 63) >> 6;
    uint64_t *c = bufA, *x = bufB;
    memset(c, 0, sizeof(uint64_t) * (size_t)n * (size_t)W);
    for (int v = 0; v < n; v++) c[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int lvl = 0; lvl < DIAM; lvl++) {
        for (int v = 0; v < n; v++) {
            uint64_t *xv = x + (size_t)v * W;
            const uint64_t *cv = c + (size_t)v * W;
            memcpy(xv, cv, sizeof(uint64_t) * (size_t)W);
            const int *nv = nb + (size_t)v * DEG;
            for (int e = 0; e < DEG; e++) {
                const uint64_t *cu = c + (size_t)nv[e] * W;
                for (int w = 0; w < W; w++) xv[w] |= cu[w];
            }
        }
        uint64_t *t = c; c = x; x = t;
    }
    long long bad = 0;
    for (int v = 0; v < n; v++) {
        const uint64_t *cv = c + (size_t)v * W;
        int cnt = 0;
        for (int w = 0; w < W; w++) cnt += popc64(cv[w]);
        bad += n - cnt;
    }
    return bad;
}

static void build_haar(void) {
    for (int i = 0; i < H; i++) {
        for (int s = 0; s < DEG; s++) {
            int a = 2 * i;
            int b = 2 * ((i + s) % H) + 1;
            nb[(size_t)a * DEG + s] = b;
            nb[(size_t)b * DEG + s] = a;
        }
    }
}

static void save_valid(void) {
    vH = H;
    memcpy(vnb, nb, sizeof(int) * (size_t)2 * H * DEG);
}

static void restore_valid(void) {
    H = vH;
    memcpy(nb, vnb, sizeof(int) * (size_t)2 * H * DEG);
}

static int has_edge(int a, int b) {
    const int *p = nb + (size_t)a * DEG;
    for (int e = 0; e < DEG; e++)
        if (p[e] == b) return 1;
    return 0;
}

static void replace_in(int v, int old, int nw) {
    int *p = nb + (size_t)v * DEG;
    for (int e = 0; e < DEG; e++)
        if (p[e] == old) { p[e] = nw; return; }
}

/* Add two vertices (one per side) by the matching insertion. Returns 0 if no matching found. */
static int insert_one(void) {
    static int markB[MAXH];
    if (H + 1 > MAXH) return 0;
    for (int i = 0; i < H; i++) permA[i] = i;
    for (int i = H - 1; i > 0; i--) {
        int j = rnd_int(i + 1);
        int tmp = permA[i]; permA[i] = permA[j]; permA[j] = tmp;
    }
    memset(markB, 0, sizeof(int) * (size_t)H);
    int ca[MAXD], cb[MAXD];
    int cnt = 0;
    for (int k = 0; k < H && cnt < DEG; k++) {
        int a = 2 * permA[k];
        int st = rnd_int(DEG);
        for (int t = 0; t < DEG; t++) {
            int b = nb[(size_t)a * DEG + (st + t) % DEG];
            int j = b >> 1;
            if (!markB[j]) {
                markB[j] = 1;
                ca[cnt] = a;
                cb[cnt] = b;
                cnt++;
                break;
            }
        }
    }
    if (cnt < DEG) return 0;
    int na = 2 * H, nbv = 2 * H + 1;
    for (int i = 0; i < DEG; i++) {
        int a = ca[i], b = cb[i];
        replace_in(a, b, nbv);
        replace_in(b, a, na);
        nb[(size_t)na * DEG + i] = b;
        nb[(size_t)nbv * DEG + i] = a;
    }
    H++;
    return 1;
}

/* Annealing on double-edge swaps. Returns 0 when valid, else the last cost. */
static long long sa_run(int iters) {
    long long cur = eval_bad();
    if (cur == 0) return 0;
    for (int it = 0; it < iters; it++) {
        if ((it & 255) == 0 && elapsed() > DEADLINE) break;
        double frac = (double)it / (double)iters;
        double temp = 2.0 * (1.0 - frac) + 0.15;
        int a1 = 2 * rnd_int(H);
        int a2 = 2 * rnd_int(H);
        if (a1 == a2) continue;
        int i1 = rnd_int(DEG), i2 = rnd_int(DEG);
        int b1 = nb[(size_t)a1 * DEG + i1];
        int b2 = nb[(size_t)a2 * DEG + i2];
        if (b1 == b2) continue;
        if (has_edge(a1, b2) || has_edge(a2, b1)) continue;
        nb[(size_t)a1 * DEG + i1] = b2;
        nb[(size_t)a2 * DEG + i2] = b1;
        replace_in(b1, a1, a2);
        replace_in(b2, a2, a1);
        long long nc = eval_bad();
        if (nc <= cur || rnd_unit() < exp(-(double)(nc - cur) / temp)) {
            cur = nc;
            if (cur == 0) return 0;
        } else {
            nb[(size_t)a1 * DEG + i1] = b1;
            nb[(size_t)a2 * DEG + i2] = b2;
            replace_in(b1, a2, a1);
            replace_in(b2, a1, a2);
        }
    }
    return cur;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time_limit [start_h]\n");
        return 1;
    }
    timespec_get(&T0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    int start_h = argc > 5 ? atoi(argv[5]) : 0;
    if (DEG < 2 || DEG > MAXD || DIAM < 2) {
        printf("0 0\n");
        return 0;
    }
    nb = malloc(sizeof(int) * (size_t)MAXV * DEG);
    vnb = malloc(sizeof(int) * (size_t)MAXV * DEG);
    permA = malloc(sizeof(int) * (size_t)MAXH);
    bufA = malloc(sizeof(uint64_t) * (size_t)MAXV * MAXW);
    bufB = malloc(sizeof(uint64_t) * (size_t)MAXV * MAXW);
    uint64_t sm = sd * 2654435761ULL + 987654321ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    int startH = start_h;
    if (startH < DEG + 1) startH = DEG + 1;
    if (startH > MAXH - 2) startH = MAXH - 2;
    H = startH;
    build_haar();

    /* Phase 1: find any valid graph, shrinking H if repair fails. */
    int have = 0;
    while (!have && elapsed() < DEADLINE) {
        if (sa_run(CHUNK1) == 0) {
            save_valid();
            have = 1;
        } else {
            int dec = H / 25 + 1;
            H -= dec;
            if (H < DEG + 1) H = DEG + 1;
            build_haar();
        }
    }

    /* Phase 2: grow by 2 vertices at a time, repairing after each insertion. */
    while (have && elapsed() < DEADLINE) {
        restore_valid();
        if (!insert_one()) continue;
        if (sa_run(CHUNK2) == 0) save_valid();
    }

    if (!have || vH <= 0) {
        printf("0 0\n");
        return 0;
    }
    int n = 2 * vH;
    int m = vH * DEG;
    printf("%d %d\n", n, m);
    for (int i = 0; i < vH; i++) {
        for (int e = 0; e < DEG; e++) {
            int a = 2 * i;
            int b = vnb[(size_t)a * DEG + e];
            int la = i;
            int lb = vH + (b >> 1);
            printf("%d %d\n", la, lb);
        }
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Safe baseline: projective plane incidence graphs (diameter 3) and K_{d,d}
# (diameter 2). Both are always valid for the given d and D.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Driver: baselines in Python, then the C local search with growth.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Already at the Moore bound: nothing larger is possible.
    moore = lib.moore_bound(d, D)
    if best_n >= moore:
        return best

    if d < 2 or D < 2:
        return best

    # Give the C search nearly all of the budget. The margin covers process
    # start, the cached compile step, parsing and validation in Python.
    remaining = 0.9 * time_limit - (time.monotonic() - start) - 2.0
    if remaining >= 2.0:
        # Start the local search at a Haar graph about 44% of the Moore bound
        # (per side), then let it grow.
        start_h = max(d + 1, int(0.44 * moore / 2))
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}", start_h],
                            timeout=remaining + 6.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
