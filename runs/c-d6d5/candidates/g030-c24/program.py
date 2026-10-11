import time

import lib


# ----------------------------------------------------------------------------
# New construction: unstructured d-regular bipartite graphs grown by vertex
# insertion and repaired by simulated annealing with 2-switch moves.
#
# State: a bipartite d-regular graph with m vertices per side, stored as E = m*d
# edges (ea[e], eb[e]) with local side indices. Unified ids: A-vertex i -> i,
# B-vertex j -> m + j.
#
# Growth: a perfect-matching-like set of d edges (a_i, b_i) with distinct
# endpoints is rerouted through a new A vertex and a new B vertex:
# (a_i, b_i) becomes (a_i, b') and (a', b_i) is added. Degrees stay d and the
# graph stays bipartite.
#
# Cost: number of unordered vertex pairs at distance > D. Computed by bitset
# BFS (each vertex keeps a bitset of vertices within t steps).
#
# Moves: 2-switches (a1,b1),(a2,b2) -> (a1,b2),(a2,b1), which keep all degrees
# and bipartiteness. Metropolis acceptance on the cost.
#
# Output: the largest zero-cost graph found, if it beats start_n.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXM 1000
#define ITERS 20000
#define TEMP0 2.0
#define TEMP1 0.15

static uint64_t rs[2];
static struct timespec TS0;
static double DEADLINE;
static int DEG, DIAM, M, E, best_n;
static int *ea, *eb, *sb;
static int *adj, *acnt;
static uint64_t *cur, *nxt;
static int WMAX;
static int *bea, *beb, bestM, bestE;
static int *perm, *usedA, *usedB, *sel;

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
    return (double)(ts.tv_sec - TS0.tv_sec) + 1e-9 * (double)(ts.tv_nsec - TS0.tv_nsec);
}

static int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void build_adj(void) {
    int N = 2 * M;
    memset(acnt, 0, sizeof(int) * (size_t)N);
    for (int e = 0; e < E; e++) {
        int u = ea[e], v = M + eb[e];
        adj[u * DEG + acnt[u]++] = v;
        adj[v * DEG + acnt[v]++] = u;
    }
}

static int has_edge(int u, int v) {
    for (int i = 0; i < DEG; i++)
        if (adj[u * DEG + i] == v) return 1;
    return 0;
}

/* Number of unordered pairs at distance > DIAM. Requires build_adj() for current state. */
static long long eval_cost(void) {
    build_adj();
    int N = 2 * M, W = (N + 63) >> 6;
    memset(cur, 0, sizeof(uint64_t) * (size_t)N * W);
    for (int v = 0; v < N; v++) cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int step = 0; step < DIAM; step++) {
        for (int v = 0; v < N; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            memcpy(dst, cur + (size_t)v * W, sizeof(uint64_t) * W);
            for (int i = 0; i < DEG; i++) {
                int u = adj[v * DEG + i];
                const uint64_t *src = cur + (size_t)u * W;
                for (int w = 0; w < W; w++) dst[w] |= src[w];
            }
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
    }
    long long tot = 0;
    size_t words = (size_t)N * W;
    for (size_t i = 0; i < words; i++) tot += popc64(cur[i]);
    return ((long long)N * N - tot) / 2;
}

/* Reroute d edges forming a matching through a new A vertex and a new B vertex. */
static int expand(void) {
    if (M + 1 > MAXM) return 0;
    for (int tr = 0; tr < 200; tr++) {
        for (int i = 0; i < E; i++) perm[i] = i;
        for (int i = E - 1; i > 0; i--) {
            int j = rnd_int(i + 1);
            int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
        }
        memset(usedA, 0, sizeof(int) * (size_t)M);
        memset(usedB, 0, sizeof(int) * (size_t)M);
        int cnt = 0;
        for (int i = 0; i < E && cnt < DEG; i++) {
            int f = perm[i];
            if (!usedA[ea[f]] && !usedB[eb[f]]) {
                usedA[ea[f]] = 1;
                usedB[eb[f]] = 1;
                sel[cnt++] = f;
            }
        }
        if (cnt < DEG) continue;
        int mo = M;
        for (int i = 0; i < DEG; i++) {
            int f = sel[i];
            int a = ea[f], b = eb[f];
            eb[f] = mo;
            ea[E] = mo;
            eb[E] = b;
            E++;
        }
        M++;
        return 1;
    }
    return 0;
}

/* Simulated annealing with 2-switches. Leaves the state at the best configuration found. */
static long long anneal(void) {
    long long cost = eval_cost();
    long long best = cost;
    memcpy(sb, eb, sizeof(int) * (size_t)E);
    for (int it = 0; it < ITERS && best > 0; it++) {
        if ((it & 127) == 0 && elapsed() > DEADLINE) break;
        double T = TEMP0 * pow(TEMP1 / TEMP0, (double)it / ITERS);
        int e1 = rnd_int(E), e2 = rnd_int(E);
        if (e1 == e2) continue;
        int a1 = ea[e1], b1 = eb[e1], a2 = ea[e2], b2 = eb[e2];
        if (a1 == a2 || b1 == b2) continue;
        build_adj();
        if (has_edge(a1, M + b2) || has_edge(a2, M + b1)) continue;
        eb[e1] = b2;
        eb[e2] = b1;
        long long nc = eval_cost();
        if (nc <= cost || rnd_unit() < exp(-(double)(nc - cost) / T)) {
            cost = nc;
            if (cost < best) {
                best = cost;
                memcpy(sb, eb, sizeof(int) * (size_t)E);
            }
        } else {
            eb[e1] = b1;
            eb[e2] = b2;
        }
    }
    memcpy(eb, sb, sizeof(int) * (size_t)E);
    return best;
}

static void record(void) {
    if (2 * M <= best_n) return;
    bestM = M;
    bestE = E;
    memcpy(bea, ea, sizeof(int) * (size_t)E);
    memcpy(beb, eb, sizeof(int) * (size_t)E);
    best_n = 2 * M;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time_limit [start_n]\n");
        return 1;
    }
    timespec_get(&TS0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    best_n = argc > 5 ? atoi(argv[5]) : 0;
    bestM = 0;
    bestE = 0;
    if (DEG < 2 || DIAM < 2) {
        printf("0 0\n");
        return 0;
    }

    size_t maxE = (size_t)MAXM * DEG;
    ea = malloc(sizeof(int) * maxE);
    eb = malloc(sizeof(int) * maxE);
    sb = malloc(sizeof(int) * maxE);
    bea = malloc(sizeof(int) * maxE);
    beb = malloc(sizeof(int) * maxE);
    perm = malloc(sizeof(int) * maxE);
    sel = malloc(sizeof(int) * (size_t)DEG);
    usedA = malloc(sizeof(int) * MAXM);
    usedB = malloc(sizeof(int) * MAXM);
    adj = malloc(sizeof(int) * 2 * maxE);
    acnt = malloc(sizeof(int) * 2 * MAXM);
    WMAX = (2 * MAXM + 63) >> 6;
    cur = calloc((size_t)2 * MAXM * WMAX, sizeof(uint64_t));
    nxt = calloc((size_t)2 * MAXM * WMAX, sizeof(uint64_t));

    uint64_t sm = sd * 2654435761ULL + 12345ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    /* Start: K_{d,d}, d-regular with diameter 2. */
    M = DEG;
    E = 0;
    for (int i = 0; i < M; i++)
        for (int j = 0; j < M; j++) {
            ea[E] = i;
            eb[E] = j;
            E++;
        }
    record();

    while (elapsed() < DEADLINE) {
        long long c = anneal();
        if (c == 0) {
            record();
            if (!expand()) break;
        }
    }

    if (bestM > 0) {
        printf("%d %d\n", 2 * bestM, bestE);
        for (int i = 0; i < bestE; i++)
            printf("%d %d\n", bea[i], bestM + beb[i]);
    } else {
        printf("0 0\n");
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Safe baseline.
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

    if best_n >= lib.moore_bound(d, D):
        return best

    remaining = 0.85 * time_limit - (time.monotonic() - start) - 2.0
    if remaining >= 2.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}", best_n],
                            timeout=remaining + 10.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
