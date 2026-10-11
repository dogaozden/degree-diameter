import time

import lib


# ----------------------------------------------------------------------------
# New construction family (replaces the group-lift annealer).
#
# The search works directly on bipartite graphs with fixed degree DEG and
# equal sides of size N. It does not use a group. The state is a DEG-regular
# bipartite graph, and the objective is the number of ordered vertex pairs at
# distance > DIAM, which is computed with bitset BFS.
#
# Moves:
#   * double-edge switch (a1,b1),(a2,b2) -> (a1,b2),(a2,b1), which keeps
#     every degree and bipartiteness;
#   * vertex-pair growth: take DEG edges (a_i,b_i) with distinct endpoints,
#     add a new A-vertex joined to all b_i and a new B-vertex joined to all
#     a_i, and drop the removed edges. This keeps the graph regular and
#     increases N by one, so the search can climb past a valid size.
#
# Whenever the state reaches zero cost (a valid graph), it is snapshotted and
# the graph grows by one vertex pair. Simulated annealing with geometric
# reheats runs between moves. Only the last valid snapshot is printed.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXSIDE 1600
#define MAXN (2 * MAXSIDE)
#define MAXW ((MAXN + 63) / 64)
#define MAXDEG 32
#define CYC 20000
#define THI 4.0
#define TLO 0.3

static int DEG, DIAM, N;
static int *nbA, *nbB, *ea, *eb;
static uint64_t *cur, *nxt;
static uint64_t rs[2];
static struct timespec T0;
static double DEADLINE;
static int snapN = 0;
static int *snapA, *snapB;

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

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Number of ordered pairs (v,w) with dist(v,w) > DIAM. Zero iff the graph is valid. */
static long long eval_cost(void) {
    int n = 2 * N;
    int W = (n + 63) / 64;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * (size_t)W);
    for (int v = 0; v < n; v++)
        cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int step = 0; step < DIAM; step++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            const uint64_t *src = cur + (size_t)v * W;
            for (int w = 0; w < W; w++) dst[w] = src[w];
            const int *nb;
            int off;
            if (v < N) {
                nb = nbA + (size_t)v * DEG;
                off = N;
            } else {
                nb = nbB + (size_t)(v - N) * DEG;
                off = 0;
            }
            for (int i = 0; i < DEG; i++) {
                const uint64_t *s = cur + (size_t)(nb[i] + off) * W;
                for (int w = 0; w < W; w++) dst[w] |= s[w];
            }
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
    }
    long long miss = 0;
    for (int v = 0; v < n; v++) {
        const uint64_t *r = cur + (size_t)v * W;
        int c = 0;
        for (int w = 0; w < W; w++) c += pc64(r[w]);
        miss += n - c;
    }
    return miss;
}

static int contains(const int *arr, int base, int x) {
    for (int i = 0; i < DEG; i++)
        if (arr[base + i] == x) return 1;
    return 0;
}

static void replace_in(int *arr, int base, int old, int nw) {
    for (int i = 0; i < DEG; i++)
        if (arr[base + i] == old) {
            arr[base + i] = nw;
            return;
        }
}

/* Switch is legal iff neither new edge already exists (this also rules out a1==a2 and b1==b2). */
static int valid_switch(int e1, int e2) {
    int a1 = ea[e1], b1 = eb[e1], a2 = ea[e2], b2 = eb[e2];
    (void)b1;
    (void)a2;
    return !contains(nbA, a1 * DEG, b2) && !contains(nbA, a2 * DEG, eb[e1]);
}

/* Applies (a1,b1),(a2,b2) -> (a1,b2),(a2,b1). Calling it again on the same pair undoes it. */
static void do_switch(int e1, int e2) {
    int a1 = ea[e1], b1 = eb[e1], a2 = ea[e2], b2 = eb[e2];
    replace_in(nbA, a1 * DEG, b1, b2);
    replace_in(nbA, a2 * DEG, b2, b1);
    replace_in(nbB, b1 * DEG, a1, a2);
    replace_in(nbB, b2 * DEG, a2, a1);
    ea[e1] = a1; eb[e1] = b2;
    ea[e2] = a2; eb[e2] = b1;
}

/* Adds one vertex on each side; the graph stays DEG-regular. */
static int try_grow(void) {
    if (N + 1 > MAXSIDE) return 0;
    int E = N * DEG;
    int es[MAXDEG], as_[MAXDEG], bs[MAXDEG];
    long tries = 0;
    for (int i = 0; i < DEG; i++) {
        int ok = 0;
        while (!ok && tries < 200000) {
            tries++;
            int e = rnd_int(E);
            int a = ea[e], b = eb[e];
            ok = 1;
            for (int j = 0; j < i; j++)
                if (as_[j] == a || bs[j] == b) { ok = 0; break; }
            if (ok) { es[i] = e; as_[i] = a; bs[i] = b; }
        }
        if (!ok) return 0;
    }
    int anew = N, bnew = N;
    for (int i = 0; i < DEG; i++) {
        int a = as_[i], b = bs[i], e = es[i];
        replace_in(nbA, a * DEG, b, bnew);   /* a loses b, gains bnew */
        replace_in(nbB, b * DEG, a, anew);   /* b loses a, gains anew */
        ea[e] = a; eb[e] = bnew;
        ea[E + i] = anew; eb[E + i] = b;
        nbA[anew * DEG + i] = b;
        nbB[bnew * DEG + i] = a;
    }
    N++;
    return 1;
}

static void init_graph(int n0) {
    N = n0;
    int *cntB = calloc((size_t)N, sizeof(int));
    for (int a = 0; a < N; a++)
        for (int l = 0; l < DEG; l++) {
            int b = (a + l) % N;
            ea[a * DEG + l] = a;
            eb[a * DEG + l] = b;
            nbA[a * DEG + l] = b;
        }
    int E = N * DEG;
    for (int e = 0; e < E; e++) {
        int b = eb[e];
        nbB[b * DEG + cntB[b]++] = ea[e];
    }
    free(cntB);
    for (int it = 0; it < 20 * E; it++) {
        int e1 = rnd_int(E), e2 = rnd_int(E);
        if (e1 != e2 && valid_switch(e1, e2)) do_switch(e1, e2);
    }
}

static void snapshot(void) {
    int E = N * DEG;
    memcpy(snapA, ea, sizeof(int) * (size_t)E);
    memcpy(snapB, eb, sizeof(int) * (size_t)E);
    snapN = N;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        printf("0 0\n");
        return 1;
    }
    timespec_get(&T0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    int n0 = argc > 5 ? atoi(argv[5]) : 0;
    if (DEG < 1 || DEG > MAXDEG || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    uint64_t sm = sd * 2654435761ULL + 12345ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    nbA = calloc((size_t)MAXSIDE * MAXDEG, sizeof(int));
    nbB = calloc((size_t)MAXSIDE * MAXDEG, sizeof(int));
    ea = calloc((size_t)MAXSIDE * MAXDEG, sizeof(int));
    eb = calloc((size_t)MAXSIDE * MAXDEG, sizeof(int));
    snapA = calloc((size_t)MAXSIDE * MAXDEG, sizeof(int));
    snapB = calloc((size_t)MAXSIDE * MAXDEG, sizeof(int));
    cur = calloc((size_t)MAXN * MAXW, sizeof(uint64_t));
    nxt = calloc((size_t)MAXN * MAXW, sizeof(uint64_t));

    if (n0 < DEG) n0 = DEG;
    if (n0 > MAXSIDE) n0 = MAXSIDE;
    init_graph(n0);

    long long cost = eval_cost();
    long long it = 0;
    long long cyc = 0;
    for (;;) {
        if ((it & 31) == 0 && elapsed() > DEADLINE) break;
        it++;
        if (cost == 0) {
            snapshot();
            if (!try_grow()) break;
            cost = eval_cost();
            cyc = 0;
            continue;
        }
        double phase = (double)(cyc % CYC) / CYC;
        double T = THI * pow(TLO / THI, phase);
        cyc++;
        int E = N * DEG;
        int e1 = rnd_int(E), e2 = rnd_int(E);
        if (e1 == e2 || !valid_switch(e1, e2)) continue;
        do_switch(e1, e2);
        long long c2 = eval_cost();
        if (c2 <= cost || rnd_unit() < exp(-(double)(c2 - cost) / T)) {
            cost = c2;
        } else {
            do_switch(e1, e2);
        }
    }

    if (snapN > 0) {
        int m = snapN * DEG;
        printf("%d %d\n", 2 * snapN, m);
        for (int e = 0; e < m; e++)
            printf("%d %d\n", snapA[e], snapN + snapB[e]);
    } else {
        printf("0 0\n");
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Safe baseline: projective plane incidence graphs and K_{d,d}.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Driver: baselines, then the bipartite local search with vertex growth.
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
    if best_n >= lib.moore_bound(d, D):
        return best

    # Give the search nearly all of the budget. The margin covers the cached
    # compile step, process start, parsing and validation.
    remaining = 0.92 * time_limit - (time.monotonic() - start) - 1.5
    if remaining >= 2.0:
        n0 = max(d, best_n // 2)
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}", n0],
                            timeout=remaining + 3.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
