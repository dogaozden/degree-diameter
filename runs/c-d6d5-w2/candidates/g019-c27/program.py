import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# New construction family: unstructured bipartite graphs, not voltage lifts.
#
# The state is a d-regular bipartite multigraph-free graph with sides of size S
# (A vertices 0..S-1, B vertices 0..S-1). Moves are 2-switches on edges
# (a1,b1),(a2,b2) -> (a1,b2),(a2,b1), which keep every degree equal to d and
# keep the graph bipartite. The cost is the number of ordered vertex pairs at
# distance > DIAM, computed with bitset ball expansion.
#
# Growth: once the cost reaches 0 the graph is saved and grown by one vertex
# per side. Pick d edges (x_i, y_i) with distinct x_i and distinct y_i, add a
# new A vertex joined to every y_i and a new B vertex joined to every x_i, and
# drop the old edges. Regularity is kept, and the annealer repairs the new
# diameter defects. Output is always the last saved zero-cost graph.
#
# Python keeps the safe baselines: K_{d,d}, PG(2,q) incidence for D >= 3, and
# a random cyclic Haar-graph search as an intermediate fallback. The C result
# is used only if it validates and is larger.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXS 1200
#define MAXW 38
#define ITER_CAP 200000
#define TEMP0 1.0
#define TEMP1 0.05

static uint64_t rs[2];
static struct timespec T0;
static double DEADLINE;
static int DEG, DIAM, S, E;
static int *eu, *ev, *adj, *cntv, *bestU, *bestV;
static unsigned char *adjm;
static uint64_t *cur, *nxt;
static int bestS = 0, bestE = 0;
static unsigned char pc16[65536];

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

static int popc64(uint64_t x) {
    return pc16[x & 0xFFFF] + pc16[(x >> 16) & 0xFFFF] +
           pc16[(x >> 32) & 0xFFFF] + pc16[(x >> 48) & 0xFFFF];
}

/* Sum over vertices of the number of vertices at distance > DIAM. */
static long long eval_cost(void) {
    int N = 2 * S, W = (N + 63) / 64;
    for (int v = 0; v < N; v++) cntv[v] = 0;
    for (int e = 0; e < E; e++) {
        int a = eu[e], b = S + ev[e];
        adj[a * DEG + cntv[a]++] = b;
        adj[b * DEG + cntv[b]++] = a;
    }
    memset(cur, 0, sizeof(uint64_t) * (size_t)N * W);
    for (int v = 0; v < N; v++) cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int r = 0; r < DIAM; r++) {
        for (int v = 0; v < N; v++) {
            uint64_t *o = nxt + (size_t)v * W;
            const uint64_t *c = cur + (size_t)v * W;
            memcpy(o, c, sizeof(uint64_t) * W);
            for (int k = 0; k < DEG; k++) {
                const uint64_t *cu = cur + (size_t)adj[v * DEG + k] * W;
                for (int w = 0; w < W; w++) o[w] |= cu[w];
            }
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
    }
    long long tot = 0;
    for (int v = 0; v < N; v++) {
        const uint64_t *c = cur + (size_t)v * W;
        int pc = 0;
        for (int w = 0; w < W; w++) pc += popc64(c[w]);
        tot += N - pc;
    }
    return tot;
}

static void save_best(void) {
    bestS = S;
    bestE = E;
    memcpy(bestU, eu, sizeof(int) * (size_t)E);
    memcpy(bestV, ev, sizeof(int) * (size_t)E);
}

/* Add one A vertex and one B vertex, keeping d-regularity. Returns 0 on failure. */
static int grow(void) {
    if (S + 1 >= MAXS) return 0;
    int *ua = calloc((size_t)S + 1, sizeof(int));
    int *ub = calloc((size_t)S + 1, sizeof(int));
    int *ch = malloc(sizeof(int) * (size_t)DEG);
    int k = 0;
    long tries = 0;
    while (k < DEG && tries < 200000) {
        tries++;
        int e = rnd_int(E);
        int x = eu[e], y = ev[e];
        if (ua[x] || ub[y]) continue;
        ua[x] = 1;
        ub[y] = 1;
        ch[k++] = e;
    }
    if (k == DEG) {
        int s = S;
        for (int i = 0; i < DEG; i++) {
            int e = ch[i];
            int x = eu[e], y = ev[e];
            adjm[x * MAXS + y] = 0;
            ev[e] = s;
            adjm[x * MAXS + s] = 1;
            int f = E + i;
            eu[f] = s;
            ev[f] = y;
            adjm[s * MAXS + y] = 1;
        }
        E += DEG;
        S = s + 1;
    }
    free(ua);
    free(ub);
    free(ch);
    return k == DEG;
}

/* Simulated annealing on 2-switches for one chunk of ITER_CAP steps. */
static long long anneal(long long cost) {
    for (long it = 0; it < ITER_CAP && cost > 0; it++) {
        if ((it & 63) == 0 && elapsed() > DEADLINE) break;
        double temp = TEMP0 * pow(TEMP1 / TEMP0, (double)it / ITER_CAP);
        int e1 = rnd_int(E), e2 = rnd_int(E);
        if (e1 == e2) continue;
        int a1 = eu[e1], b1 = ev[e1], a2 = eu[e2], b2 = ev[e2];
        if (a1 == a2 || b1 == b2) continue;
        if (adjm[a1 * MAXS + b2] || adjm[a2 * MAXS + b1]) continue;
        ev[e1] = b2;
        ev[e2] = b1;
        adjm[a1 * MAXS + b1] = 0;
        adjm[a2 * MAXS + b2] = 0;
        adjm[a1 * MAXS + b2] = 1;
        adjm[a2 * MAXS + b1] = 1;
        long long c2 = eval_cost();
        if (c2 <= cost || rnd_unit() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
        } else {
            ev[e1] = b1;
            ev[e2] = b2;
            adjm[a1 * MAXS + b2] = 0;
            adjm[a2 * MAXS + b1] = 0;
            adjm[a1 * MAXS + b1] = 1;
            adjm[a2 * MAXS + b2] = 1;
        }
    }
    return cost;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time_limit\n");
        return 1;
    }
    timespec_get(&T0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    if (DEG < 2 || DIAM < 2) {
        printf("0 0\n");
        return 0;
    }

    for (int i = 0; i < 65536; i++) pc16[i] = (unsigned char)(pc16[i >> 1] + (i & 1));
    uint64_t sm = sd * 2654435761ULL + 987654321ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    eu = malloc(sizeof(int) * (size_t)DEG * MAXS);
    ev = malloc(sizeof(int) * (size_t)DEG * MAXS);
    bestU = malloc(sizeof(int) * (size_t)DEG * MAXS);
    bestV = malloc(sizeof(int) * (size_t)DEG * MAXS);
    adjm = calloc((size_t)MAXS * MAXS, 1);
    adj = malloc(sizeof(int) * 2 * (size_t)MAXS * DEG);
    cntv = malloc(sizeof(int) * 2 * (size_t)MAXS);
    cur = malloc(sizeof(uint64_t) * 2 * (size_t)MAXS * MAXW);
    nxt = malloc(sizeof(uint64_t) * 2 * (size_t)MAXS * MAXW);

    /* Start from the circulant d-regular bipartite graph on S sides. */
    S = 2 * DEG + 8;
    E = 0;
    for (int a = 0; a < S; a++) {
        for (int k = 0; k < DEG; k++) {
            int b = (a + k) % S;
            eu[E] = a;
            ev[E] = b;
            adjm[a * MAXS + b] = 1;
            E++;
        }
    }

    while (elapsed() < DEADLINE) {
        long long cost = eval_cost();
        while (cost > 0 && elapsed() < DEADLINE) cost = anneal(cost);
        if (cost != 0) break;
        save_best();
        if (!grow()) break;
    }

    if (bestS > 0) {
        printf("%d %d\n", 2 * bestS, bestE);
        for (int e = 0; e < bestE; e++)
            printf("%d %d\n", bestU[e], bestS + bestV[e]);
    } else {
        printf("0 0\n");
    }
    return 0;
}
"""


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _haar_search(d, D, lo_n, end, seed):
    """Random cyclic Haar graphs (two base vertices, d darts): return the largest valid one found."""
    rng = random.Random(seed)
    lo_m = max(d, lo_n // 2 + 1)
    hi_m = lib.moore_bound(d, D) // 2
    best = None
    if lo_m > hi_m:
        return None
    while time.monotonic() < end and lo_m <= hi_m:
        m = rng.randint(lo_m, hi_m)
        shifts = [0] + rng.sample(range(1, m), d - 1)
        n, e = lib.haar_graph(m, shifts)
        if lib.is_valid(n, e, d, D):
            best = (n, e)
            lo_m = m + 1
    return best


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
            best, best_n = (n, e), n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Already at the Moore bound: nothing larger is possible.
    if best_n >= lib.moore_bound(d, D):
        return best

    end = start + 0.92 * time_limit - 1.5

    if d >= 2 and end - time.monotonic() > 2.0:
        haar_end = time.monotonic() + 0.15 * (end - time.monotonic())
        try:
            hs = _haar_search(d, D, best_n, haar_end, seed * 7919 + d * 31 + D)
            if hs is not None:
                consider(hs[0], hs[1])
        except Exception:
            pass

    remaining = end - time.monotonic()
    if d >= 2 and remaining >= 1.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}"],
                            timeout=remaining + 8.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
