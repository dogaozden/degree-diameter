import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Search engine: degree-preserving edge switching on bipartite graphs.
#
# The graph is d-regular and bipartite. A move picks two edges a1-b1 and
# a2-b2 and rewires them to a1-b2 and a2-b1, which keeps every degree and the
# bipartition. Cost = number of ordered vertex pairs at distance > DIAM,
# computed exactly with bitset balls (no lift symmetry is assumed).
#
# Growth: whenever cost reaches 0, the current graph is saved and grown by
# two vertices (one per side). Each new vertex pair takes d-1 matching edges
# from the graph and reconnects them to the new pair, which keeps the graph
# d-regular. Annealing then repairs the diameter at the larger size.
# The start is a small random Z_m lift of K_{d,d}.
#
# Usage: prog d D seed slice_seconds   (stdin: "n m" + edges, d-regular)
# Prints the largest valid graph found ("n m" + edges) or "0 0".
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define NCAP 2048
#define WCAP ((NCAP + 63) / 64)
#define CYC 4000
#define KICK 3
#define T0 3.0

static int DEG, DIAM, N, NE, W;
static int *EA, *EB, *nb, *cnt, *bEA, *bEB, *lEA, *lEB;
static int bestN = 0, bestNE = 0, lowCost, lNE = 0;
static unsigned char *mat;
static uint64_t *R1, *R2;
static uint64_t rs = 88172645463325252ULL;

static inline uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static inline int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static inline double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static inline int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void setm(int x, int y, int v) {
    mat[(size_t)x * NCAP + y] = (unsigned char)v;
    mat[(size_t)y * NCAP + x] = (unsigned char)v;
}

static int cost_fn(void) {
    W = (N + 63) >> 6;
    memset(cnt, 0, sizeof(int) * (size_t)N);
    for (int e = 0; e < NE; e++) {
        int a = EA[e], b = EB[e];
        nb[a * DEG + cnt[a]++] = b;
        nb[b * DEG + cnt[b]++] = a;
    }
    memset(R1, 0, sizeof(uint64_t) * (size_t)N * W);
    for (int v = 0; v < N; v++) R1[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    uint64_t *cur = R1, *nxt = R2;
    for (int r = 0; r < DIAM; r++) {
        for (int v = 0; v < N; v++) {
            uint64_t *o = nxt + (size_t)v * W;
            memcpy(o, cur + (size_t)v * W, sizeof(uint64_t) * W);
            for (int k = 0; k < DEG; k++) {
                const uint64_t *s = cur + (size_t)nb[v * DEG + k] * W;
                for (int w = 0; w < W; w++) o[w] |= s[w];
            }
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
    }
    long long tot = 0;
    for (int v = 0; v < N; v++) {
        const uint64_t *s = cur + (size_t)v * W;
        int c = 0;
        for (int w = 0; w < W; w++) c += popc64(s[w]);
        tot += N - c;
    }
    return (int)tot;
}

/* Apply the switch (i,j) if it keeps the graph simple. */
static int do_switch(int i, int j) {
    int a1 = EA[i], b1 = EB[i], a2 = EA[j], b2 = EB[j];
    if (a1 == a2 || b1 == b2) return 0;
    if (mat[(size_t)a1 * NCAP + b2] || mat[(size_t)a2 * NCAP + b1]) return 0;
    setm(a1, b1, 0); setm(a2, b2, 0);
    setm(a1, b2, 1); setm(a2, b1, 1);
    EB[i] = b2; EB[j] = b1;
    return 1;
}

static void undo_switch(int i, int j) {
    int a1 = EA[i], b2 = EB[i], a2 = EA[j], b1 = EB[j];
    setm(a1, b2, 0); setm(a2, b1, 0);
    setm(a1, b1, 1); setm(a2, b2, 1);
    EB[i] = b1; EB[j] = b2;
}

static void save_best(void) {
    bestN = N; bestNE = NE;
    memcpy(bEA, EA, sizeof(int) * (size_t)NE);
    memcpy(bEB, EB, sizeof(int) * (size_t)NE);
}

static void save_low(void) {
    lNE = NE;
    memcpy(lEA, EA, sizeof(int) * (size_t)NE);
    memcpy(lEB, EB, sizeof(int) * (size_t)NE);
}

static void load_state(const int *SA, const int *SB, int ne) {
    for (int e = 0; e < NE; e++) setm(EA[e], EB[e], 0);
    memcpy(EA, SA, sizeof(int) * (size_t)ne);
    memcpy(EB, SB, sizeof(int) * (size_t)ne);
    NE = ne;
    for (int e = 0; e < NE; e++) setm(EA[e], EB[e], 1);
}

/* Add a vertex pair (a, b): replace DEG-1 matching edges and add a-b. */
static int grow(void) {
    int k = DEG - 1;
    if (N + 2 > NCAP || k > 31 || NE + DEG > NCAP * DEG) return 0;
    int idx[32], xs[32], ys[32];
    int ok = 0;
    for (int tries = 0; tries < 500 && !ok; tries++) {
        int good = 1;
        for (int t = 0; t < k && good; t++) {
            idx[t] = rndint(NE);
            for (int s = 0; s < t; s++) {
                if (idx[s] == idx[t] || EA[idx[s]] == EA[idx[t]] || EB[idx[s]] == EB[idx[t]]) {
                    good = 0; break;
                }
            }
        }
        ok = good;
    }
    if (!ok) return 0;
    for (int t = 0; t < k; t++) { xs[t] = EA[idx[t]]; ys[t] = EB[idx[t]]; }
    int a = N, b = N + 1;
    for (int t = 0; t < k; t++) {
        setm(xs[t], ys[t], 0);
        EA[idx[t]] = a; EB[idx[t]] = ys[t];
        setm(a, ys[t], 1);
    }
    for (int t = 0; t < k; t++) {
        EA[NE] = xs[t]; EB[NE] = b; NE++;
        setm(xs[t], b, 1);
    }
    EA[NE] = a; EB[NE] = b; NE++;
    setm(a, b, 1);
    N += 2;
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t seed = strtoull(argv[3], NULL, 10);
    double slice = atof(argv[4]);
    if (DEG < 1 || DEG > 32 || DIAM < 1) { printf("0 0\n"); return 0; }
    rs = seed * 0x9E3779B97F4A7C15ULL ^ 0x51ED27ULL;
    if (rs == 0) rs = 1;

    int n0, m0;
    if (scanf("%d %d", &n0, &m0) != 2) { printf("0 0\n"); return 0; }
    if (n0 < 2 || n0 > NCAP || m0 < 0 || m0 > NCAP * DEG / 2) { printf("0 0\n"); return 0; }

    size_t EC = (size_t)NCAP * DEG + DEG;
    EA = malloc(sizeof(int) * EC); EB = malloc(sizeof(int) * EC);
    bEA = malloc(sizeof(int) * EC); bEB = malloc(sizeof(int) * EC);
    lEA = malloc(sizeof(int) * EC); lEB = malloc(sizeof(int) * EC);
    nb = malloc(sizeof(int) * (size_t)NCAP * DEG);
    cnt = malloc(sizeof(int) * NCAP);
    mat = calloc((size_t)NCAP * NCAP, 1);
    R1 = malloc(sizeof(uint64_t) * (size_t)NCAP * WCAP);
    R2 = malloc(sizeof(uint64_t) * (size_t)NCAP * WCAP);
    int *ru = malloc(sizeof(int) * (size_t)(m0 + 1));
    int *rv = malloc(sizeof(int) * (size_t)(m0 + 1));
    int *col = malloc(sizeof(int) * NCAP);
    int *stk = malloc(sizeof(int) * NCAP);
    if (!EA || !EB || !bEA || !bEB || !lEA || !lEB || !nb || !cnt || !mat || !R1 || !R2 ||
        !ru || !rv || !col || !stk) { printf("0 0\n"); return 0; }

    N = n0;
    for (int i = 0; i < m0; i++) {
        if (scanf("%d %d", &ru[i], &rv[i]) != 2) { printf("0 0\n"); return 0; }
        if (ru[i] < 0 || ru[i] >= N || rv[i] < 0 || rv[i] >= N || ru[i] == rv[i]) { printf("0 0\n"); return 0; }
    }
    /* Input must be simple and d-regular. */
    memset(cnt, 0, sizeof(int) * (size_t)N);
    for (int i = 0; i < m0; i++) { cnt[ru[i]]++; cnt[rv[i]]++; }
    for (int v = 0; v < N; v++) if (cnt[v] != DEG) { printf("0 0\n"); return 0; }
    for (int i = 0; i < m0; i++) {
        if (mat[(size_t)ru[i] * NCAP + rv[i]]) { printf("0 0\n"); return 0; }
        setm(ru[i], rv[i], 1);
    }
    memset(cnt, 0, sizeof(int) * (size_t)N);
    for (int i = 0; i < m0; i++) {
        nb[ru[i] * DEG + cnt[ru[i]]++] = rv[i];
        nb[rv[i] * DEG + cnt[rv[i]]++] = ru[i];
    }
    /* Two-colour (bipartition). */
    for (int v = 0; v < N; v++) col[v] = -1;
    for (int s = 0; s < N; s++) {
        if (col[s] != -1) continue;
        col[s] = 0;
        int sp = 0;
        stk[sp++] = s;
        while (sp > 0) {
            int u = stk[--sp];
            for (int k = 0; k < DEG; k++) {
                int v = nb[u * DEG + k];
                if (col[v] == -1) { col[v] = 1 - col[u]; stk[sp++] = v; }
                else if (col[v] == col[u]) { printf("0 0\n"); return 0; }
            }
        }
    }
    NE = 0;
    for (int i = 0; i < m0; i++) {
        if (col[ru[i]] == 0) { EA[NE] = ru[i]; EB[NE] = rv[i]; }
        else { EA[NE] = rv[i]; EB[NE] = ru[i]; }
        NE++;
    }

    int cur = cost_fn();
    if (cur == 0) save_best();
    lowCost = cur;
    save_low();

    clock_t t0 = clock();
    int it = 0, itc = 0;
    while (1) {
        if (cur == 0) {
            if (N > bestN) save_best();
            if (!grow()) break;
            cur = cost_fn();
            lowCost = cur;
            save_low();
            itc = 0;
            continue;
        }
        if ((it & 15) == 0 && (double)(clock() - t0) / CLOCKS_PER_SEC >= slice) break;
        it++;
        int i = rndint(NE), j = rndint(NE);
        if (i == j || !do_switch(i, j)) continue;
        int nc = cost_fn();
        double T = T0 * (1.0 - (double)itc / CYC) + 0.03;
        if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
            cur = nc;
        } else {
            undo_switch(i, j);
        }
        itc++;
        if (cur == 0) continue;
        if (cur < lowCost) { lowCost = cur; save_low(); }
        if (itc >= CYC) {
            load_state(lEA, lEB, lNE);
            for (int q = 0; q < KICK; ) {
                int x = rndint(NE), y = rndint(NE);
                if (x != y && do_switch(x, y)) q++;
            }
            cur = cost_fn();
            itc = 0;
        }
    }

    if (bestN == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", bestN, bestNE);
    for (int e = 0; e < bestNE; e++) printf("%d %d\n", bEA[e], bEB[e]);
    fflush(stdout);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Constructions and driver.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _lift_start(d, m, rng):
    """Random Z_m lift of K_{d,d}: d-regular, bipartite, 2*d*m vertices."""
    darts = [(i, d + j, rng.randrange(m)) for i in range(d) for j in range(d)]
    return lib.group_lift(2 * d, darts, m, lambda x, g: (x + g) % m)


def build(d, D, seed, time_limit):
    t_start = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    budget = max(1.0, min(0.85 * time_limit, time_limit - 5.0))
    deadline = t_start + budget
    rng = random.Random(seed)

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    if not lib.is_valid(best[0], best[1], d, D):
        best = (1, [])

    # Exact construction for D = 3 when d - 1 is a prime power.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None and pg[0] > best[0] and lib.is_valid(pg[0], pg[1], d, D):
            best = pg
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    # Main search: grow from a small random lift by annealing edge switches.
    if d >= 2 and D >= 2:
        remaining = deadline - time.monotonic() - 3.0
        if remaining > 2.0:
            start = _lift_start(d, 4, rng)
            out = None
            try:
                out = lib.run_c(
                    C_SOURCE,
                    [d, D, rng.randrange(1, 10 ** 9), f"{remaining:.2f}"],
                    stdin_graph=start,
                    timeout=remaining + 15.0,
                )
            except RuntimeError:
                out = None
            if out:
                try:
                    n, e = lib.parse_graph_text(out)
                    if n > best[0] and lib.is_valid(n, e, d, D):
                        best = (n, e)
                except ValueError:
                    pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
        if not lib.is_valid(best[0], best[1], d, D):
            best = (1, [])
    return best
