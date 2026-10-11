import time

import lib


# ----------------------------------------------------------------------------
# Bold alternative: random d-regular bipartite graphs repaired by local search.
#
# The parent used voltage lifts over semidirect products. This version does not
# use any group structure. It works on a bipartite graph whose sides are A and
# B, with every vertex of degree DEG:
#   1. Start from a random DEG-regular bipartite graph on 2h vertices.
#   2. Anneal with double-edge swaps (a1-b1, a2-b2 -> a1-b2, a2-b1). Swaps keep
#      every degree and the bipartition. The cost is the number of unordered
#      vertex pairs at distance > DIAM, computed with 64-bit reachability
#      bitsets.
#   3. When a zero-cost (valid) graph is found, save it and grow: add DEG-regular
#      vertex pairs by rewiring random old edges, then anneal again. The growth
#      step doubles after success and halves after failure.
#   4. Each failed attempt reverts to the last valid saved graph. If the random
#      start never reaches zero, the start size h is lowered.
#
# Python keeps the projective-plane baseline and K_{d,d} as safe fallbacks. The
# C output is accepted only after lib.is_valid.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 4096
#define MAXW (MAXN / 64)
#define MAXD 16
#define ITER_INIT 40000
#define ITER_GROW 6000

static int DEG, DIAM;
static double DEADLINE;
static struct timespec T0;
static uint64_t rs[2];

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

/* Current graph: vertices 0..N-1, A-list As[0..nA), B-list Bs[0..nB). */
static int N, nA, nB;
static int As[MAXN], Bs[MAXN];
static int adj[MAXN][MAXD];
static int dg[MAXN];
static unsigned char mat[MAXN][MAXN];
static uint64_t BUFA[MAXN][MAXW], BUFB[MAXN][MAXW];

/* Saved valid graph. */
static int sN, snA, snB;
static int sAs[MAXN], sBs[MAXN];
static int sAdj[MAXN][MAXD];

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void add_edge(int a, int b) {
    adj[a][dg[a]++] = b;
    adj[b][dg[b]++] = a;
    mat[a][b] = 1;
    mat[b][a] = 1;
}

static void replace_in(int v, int old, int nw) {
    for (int i = 0; i < dg[v]; i++)
        if (adj[v][i] == old) { adj[v][i] = nw; return; }
}

static void clear_graph(void) {
    for (int v = 0; v < N; v++) {
        for (int e = 0; e < dg[v]; e++) mat[v][adj[v][e]] = 0;
        dg[v] = 0;
    }
    N = nA = nB = 0;
}

/* Random DEG-regular bipartite graph with h vertices per side. */
static int build_random(int h) {
    clear_graph();
    N = 2 * h;
    nA = nB = h;
    for (int i = 0; i < h; i++) { As[i] = i; Bs[i] = h + i; }
    static int p[MAXN / 2];
    for (int l = 0; l < DEG; l++) {
        int ok = 0;
        for (int tr = 0; tr < 100000 && !ok; tr++) {
            for (int i = 0; i < h; i++) p[i] = i;
            for (int i = h - 1; i > 0; i--) {
                int j = rnd_int(i + 1);
                int t = p[i]; p[i] = p[j]; p[j] = t;
            }
            ok = 1;
            for (int i = 0; i < h; i++)
                if (mat[i][h + p[i]]) { ok = 0; break; }
        }
        if (!ok) { clear_graph(); return 0; }
        for (int i = 0; i < h; i++) add_edge(i, h + p[i]);
    }
    return 1;
}

/* Number of unordered pairs at distance > DIAM. */
static long long eval_bad(void) {
    int W = (N + 63) >> 6;
    uint64_t (*cu)[MAXW] = BUFA;
    uint64_t (*nx)[MAXW] = BUFB;
    for (int v = 0; v < N; v++) {
        for (int w = 0; w < W; w++) cu[v][w] = 0;
        cu[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int s = 0; s < DIAM; s++) {
        for (int v = 0; v < N; v++) {
            for (int w = 0; w < W; w++) nx[v][w] = cu[v][w];
            for (int e = 0; e < dg[v]; e++) {
                int u = adj[v][e];
                for (int w = 0; w < W; w++) nx[v][w] |= cu[u][w];
            }
        }
        uint64_t (*tmp)[MAXW] = cu;
        cu = nx;
        nx = tmp;
    }
    long long bad = 0;
    for (int v = 0; v < N; v++) {
        int pc = 0;
        for (int w = 0; w < W; w++) pc += popc(cu[v][w]);
        bad += N - pc;
    }
    return bad / 2;
}

/* Double-edge swap on slots (a1,k1), (a2,k2). Applying it twice restores the graph. */
static void do_swap(int a1, int k1, int a2, int k2) {
    int b1 = adj[a1][k1], b2 = adj[a2][k2];
    adj[a1][k1] = b2;
    adj[a2][k2] = b1;
    replace_in(b1, a1, a2);
    replace_in(b2, a2, a1);
    mat[a1][b1] = 0; mat[b1][a1] = 0;
    mat[a2][b2] = 0; mat[b2][a2] = 0;
    mat[a1][b2] = 1; mat[b2][a1] = 1;
    mat[a2][b1] = 1; mat[b1][a2] = 1;
}

/* Add one DEG-regular vertex pair by rewiring random old edges (a,b) -> (a,y), (x,b). */
static int grow_pair(void) {
    if (N + 2 > MAXN) return 0;
    int oldN = N, oldA = nA;
    int x = N, y = N + 1;
    N += 2;
    dg[x] = dg[y] = 0;
    As[nA++] = x;
    Bs[nB++] = y;
    for (int t = 0; t < DEG; t++) {
        int ok = 0;
        for (int tr = 0; tr < 200000 && !ok; tr++) {
            int a = As[rnd_int(oldA)];
            int k = rnd_int(DEG);
            int b = adj[a][k];
            if (b >= oldN) continue;
            if (mat[x][b] || mat[a][y]) continue;
            adj[a][k] = y;
            replace_in(b, a, x);
            mat[a][b] = 0; mat[b][a] = 0;
            mat[a][y] = 1; mat[y][a] = 1;
            mat[b][x] = 1; mat[x][b] = 1;
            adj[x][dg[x]++] = b;
            adj[y][dg[y]++] = a;
            ok = 1;
        }
        if (!ok) return 0;
    }
    return 1;
}

/* Annealing on the bad-pair count. Returns 0 at cost zero, 1 if not reached, -1 on timeout. */
static int anneal(int iters, long long cost) {
    if (cost == 0) return 0;
    double tscale = 0.01 * (double)cost;
    if (tscale < 1.0) tscale = 1.0;
    for (int it = 0; it < iters; it++) {
        if ((it & 31) == 0 && elapsed() > DEADLINE) return -1;
        double frac = (double)it / (double)iters;
        double temp = tscale * (1.0 - frac) + 0.3;
        int a1 = As[rnd_int(nA)], a2 = As[rnd_int(nA)];
        if (a1 == a2) continue;
        int k1 = rnd_int(DEG), k2 = rnd_int(DEG);
        int b1 = adj[a1][k1], b2 = adj[a2][k2];
        if (mat[a1][b2] || mat[a2][b1]) continue;
        do_swap(a1, k1, a2, k2);
        long long nc = eval_bad();
        long long delta = nc - cost;
        if (delta <= 0 || rnd_unit() < exp(-(double)delta / temp)) {
            cost = nc;
            if (cost == 0) return 0;
        } else {
            do_swap(a1, k1, a2, k2);
        }
    }
    return cost == 0 ? 0 : 1;
}

static void save_state(void) {
    sN = N; snA = nA; snB = nB;
    memcpy(sAs, As, sizeof(int) * (size_t)nA);
    memcpy(sBs, Bs, sizeof(int) * (size_t)nB);
    for (int v = 0; v < N; v++) memcpy(sAdj[v], adj[v], sizeof(int) * DEG);
}

static void load_state(void) {
    clear_graph();
    N = sN; nA = snA; nB = snB;
    memcpy(As, sAs, sizeof(int) * (size_t)nA);
    memcpy(Bs, sBs, sizeof(int) * (size_t)nB);
    for (int v = 0; v < N; v++) {
        for (int e = 0; e < DEG; e++) {
            adj[v][e] = sAdj[v][e];
            mat[v][adj[v][e]] = 1;
        }
        dg[v] = DEG;
    }
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time_limit [h0]\n");
        return 1;
    }
    timespec_get(&T0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    int h0 = argc > 5 ? atoi(argv[5]) : DEG + 1;
    if (DEG < 2 || DEG > MAXD || DIAM < 2) {
        printf("0 0\n");
        return 0;
    }
    uint64_t sm = sd * 2654435761ULL + 987654321ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    int h = h0;
    if (h < DEG + 1) h = DEG + 1;
    if (h > MAXN / 2) h = MAXN / 2;
    int have = 0, fails = 0, gstep = 1;

    while (elapsed() < DEADLINE) {
        if (!have) {
            if (!build_random(h)) {
                if (h <= DEG + 1) break;
                h--;
                continue;
            }
            long long cost = eval_bad();
            int r = anneal(ITER_INIT, cost);
            if (r == 0) {
                have = 1;
                save_state();
                gstep = nA / 50 + 1;
                fails = 0;
            } else if (r < 0) {
                break;
            } else {
                fails++;
                if (fails >= 3) {
                    h -= h / 40 + 1;
                    if (h < DEG + 1) h = DEG + 1;
                    fails = 0;
                }
            }
        } else {
            int gp = gstep < 1 ? 1 : gstep;
            if (N + 2 * gp > MAXN) gp = (MAXN - N) / 2;
            if (gp < 1) break;
            int ok = 1;
            for (int i = 0; i < gp && ok; i++) ok = grow_pair();
            if (!ok) {
                load_state();
                gstep = gp / 2;
                continue;
            }
            long long cost = eval_bad();
            int r = anneal(ITER_GROW, cost);
            if (r == 0) {
                save_state();
                gstep = gp * 2;
                if (gstep > 1024) gstep = 1024;
            } else if (r < 0) {
                load_state();
                break;
            } else {
                load_state();
                gstep = gp / 2;
            }
        }
    }

    if (have) {
        printf("%d %d\n", sN, snA * DEG);
        for (int i = 0; i < snA; i++) {
            int a = sAs[i];
            for (int e = 0; e < DEG; e++) printf("%d %d\n", a, sAdj[a][e]);
        }
    } else {
        printf("0 0\n");
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Safe baseline: incidence graph of PG(2, q), used for D >= 3.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Driver.
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

    moore = lib.moore_bound(d, D)
    if best_n >= moore or d < 2 or d > 16 or D < 2:
        return best

    remaining = 0.85 * time_limit - (time.monotonic() - start) - 1.5
    if remaining < 2.0:
        return best

    # Start near 40% of the Moore bound (2h vertices with h = 0.2 * Moore).
    h0 = max(d + 1, best_n // 2 + 1, int(0.2 * moore))
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}", h0],
                        timeout=remaining + 10.0)
        n, e = lib.parse_graph_text(out)
        consider(n, e)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
