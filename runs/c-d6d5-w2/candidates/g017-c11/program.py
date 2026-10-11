import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: unstructured repair search on a d-regular bipartite graph.
#
# State: a d-regular bipartite graph on n vertices (A side = 0, B side = 1).
# Moves: 2-switches (a1 b1, a2 b2) -> (a1 b2, a2 b1). These keep every degree
# and the bipartition, so the state stays d-regular and bipartite.
# Cost: number of unordered vertex pairs at distance > D, computed exactly with
# bitset ball expansion (ball_r(v) = ball_{r-1}(v) OR the balls of neighbours).
# Simulated annealing on this cost at a fixed temperature.
#
# Growth: when cost reaches 0, the graph is valid and is saved. It then grows by
# an edge split: remove d edges (a_i, b_i) with distinct endpoints, add a new
# A-vertex x adjacent to all b_i and a new B-vertex y adjacent to all a_i. The
# result is still d-regular and bipartite with two more vertices. Annealing
# then repairs the new bad pairs. If the search stalls, it restarts from the
# best saved graph with a fresh split.
#
# The start graph comes from Python (a random Haar graph, which is d-regular and
# bipartite). If the input is invalid, the engine uses K_{d,d}.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXGROW 900
#define STALL 25000
#define TEMP 0.4

static int DEG, DIAM;
static int CAP, WMAX;
static int n, nA, nB;
static int *nb, *side, *listA, *listB;
static uint64_t *bufA, *bufB;
static int bestN = 0;
static int *bestNb, *bestSide;
static struct timespec T0;
static double DEADLINE;
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

static int rnd_int(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rnd_unit(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double elapsed(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)(ts.tv_sec - T0.tv_sec) + 1e-9 * (double)(ts.tv_nsec - T0.tv_nsec);
}

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int slot_of(int v, int u) {
    for (int k = 0; k < DEG; k++)
        if (nb[v * DEG + k] == u) return k;
    return -1;
}

/* Number of unordered pairs at distance > DIAM (0 means valid). */
static long long eval_cost(void) {
    int W = (n + 63) >> 6;
    uint64_t *A = bufA, *B = bufB;
    for (int v = 0; v < n; v++) {
        uint64_t *row = A + (size_t)v * W;
        memset(row, 0, sizeof(uint64_t) * (size_t)W);
        row[v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < DIAM; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *out = B + (size_t)v * W;
            const uint64_t *in = A + (size_t)v * W;
            memcpy(out, in, sizeof(uint64_t) * (size_t)W);
            for (int k = 0; k < DEG; k++) {
                const uint64_t *src = A + (size_t)nb[v * DEG + k] * W;
                for (int w = 0; w < W; w++) out[w] |= src[w];
            }
        }
        uint64_t *t = A; A = B; B = t;
    }
    long long total = 0;
    for (int v = 0; v < n; v++) {
        const uint64_t *row = A + (size_t)v * W;
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(row[w]);
        total += n - c;
    }
    return total / 2;
}

/* Build state from an edge list. Returns 0 if the input is not a d-regular bipartite simple graph. */
static int build_from_edges(int n0, int m, const int *eu, const int *ev) {
    if (n0 < 2 || n0 > CAP) return 0;
    int *cnt = calloc((size_t)n0, sizeof(int));
    int *stack = malloc(sizeof(int) * (size_t)n0);
    int ok = 1;
    for (int i = 0; i < m && ok; i++) {
        int u = eu[i], v = ev[i];
        if (u < 0 || v < 0 || u >= n0 || v >= n0 || u == v) { ok = 0; break; }
        if (cnt[u] >= DEG || cnt[v] >= DEG) { ok = 0; break; }
        for (int k = 0; k < cnt[u]; k++) if (nb[u * DEG + k] == v) { ok = 0; break; }
        if (!ok) break;
        nb[u * DEG + cnt[u]++] = v;
        nb[v * DEG + cnt[v]++] = u;
    }
    for (int v = 0; ok && v < n0; v++) if (cnt[v] != DEG) ok = 0;
    if (ok) {
        for (int v = 0; v < n0; v++) side[v] = -1;
        for (int s = 0; ok && s < n0; s++) {
            if (side[s] != -1) continue;
            side[s] = 0;
            int sp = 0;
            stack[sp++] = s;
            while (sp > 0 && ok) {
                int u = stack[--sp];
                for (int k = 0; k < DEG; k++) {
                    int w = nb[u * DEG + k];
                    if (side[w] == -1) {
                        side[w] = 1 - side[u];
                        stack[sp++] = w;
                    } else if (side[w] == side[u]) {
                        ok = 0;
                        break;
                    }
                }
            }
        }
    }
    free(cnt);
    free(stack);
    if (!ok) return 0;
    n = n0;
    nA = nB = 0;
    for (int v = 0; v < n; v++) {
        if (side[v] == 0) listA[nA++] = v;
        else listB[nB++] = v;
    }
    return 1;
}

static void save_best(void) {
    if (n <= bestN) return;
    memcpy(bestNb, nb, sizeof(int) * (size_t)n * DEG);
    memcpy(bestSide, side, sizeof(int) * (size_t)n);
    bestN = n;
}

static void restore_best(void) {
    n = bestN;
    memcpy(nb, bestNb, sizeof(int) * (size_t)n * DEG);
    memcpy(side, bestSide, sizeof(int) * (size_t)n);
    nA = nB = 0;
    for (int v = 0; v < n; v++) {
        if (side[v] == 0) listA[nA++] = v;
        else listB[nB++] = v;
    }
}

/* Edge split: adds two vertices (x in A, y in B), keeps d-regularity and bipartiteness. */
static int grow(void) {
    if (n + 2 > CAP) return 0;
    int pa[64], pb[64];
    int np = 0;
    for (int tries = 0; tries < 20000 && np < DEG; tries++) {
        int a = listA[rnd_int(nA)];
        int k = rnd_int(DEG);
        int b = nb[a * DEG + k];
        int ok = 1;
        for (int i = 0; i < np; i++)
            if (pa[i] == a || pb[i] == b) { ok = 0; break; }
        if (ok) { pa[np] = a; pb[np] = b; np++; }
    }
    if (np < DEG) return 0;
    int x = n, y = n + 1;
    side[x] = 0;
    side[y] = 1;
    listA[nA++] = x;
    listB[nB++] = y;
    n += 2;
    for (int i = 0; i < DEG; i++) {
        int a = pa[i], b = pb[i];
        int sa = slot_of(a, b);
        int sb = slot_of(b, a);
        nb[a * DEG + sa] = y;
        nb[b * DEG + sb] = x;
        nb[x * DEG + i] = b;
        nb[y * DEG + i] = a;
    }
    return 1;
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
    if (DEG < 2 || DEG > 60 || DIAM < 2) {
        printf("0 0\n");
        return 0;
    }
    uint64_t sm = sd * 2654435761ULL + 987654321ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { n0 = 0; m0 = 0; }
    if (n0 < 0 || m0 < 0 || n0 > 100000 || m0 > 5000000) { n0 = 0; m0 = 0; }
    int *eu = malloc(sizeof(int) * (size_t)(m0 + 1));
    int *ev = malloc(sizeof(int) * (size_t)(m0 + 1));
    int okread = 1;
    for (int i = 0; i < m0; i++) {
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) { okread = 0; break; }
    }
    if (!okread) { n0 = 0; m0 = 0; }

    int base = n0 > 2 * DEG ? n0 : 2 * DEG;
    CAP = base + MAXGROW + 4;
    WMAX = (CAP + 63) >> 6;
    nb = malloc(sizeof(int) * (size_t)CAP * DEG);
    side = malloc(sizeof(int) * (size_t)CAP);
    listA = malloc(sizeof(int) * (size_t)CAP);
    listB = malloc(sizeof(int) * (size_t)CAP);
    bufA = malloc(sizeof(uint64_t) * (size_t)CAP * WMAX);
    bufB = malloc(sizeof(uint64_t) * (size_t)CAP * WMAX);
    bestNb = malloc(sizeof(int) * (size_t)CAP * DEG);
    bestSide = malloc(sizeof(int) * (size_t)CAP);

    if (!build_from_edges(n0, m0, eu, ev)) {
        /* Fallback start: K_{DEG,DEG}. */
        int km = 0;
        for (int i = 0; i < DEG; i++)
            for (int j = 0; j < DEG; j++) {
                eu[km] = i;
                ev[km] = DEG + j;
                km++;
            }
        if (!build_from_edges(2 * DEG, km, eu, ev)) {
            printf("0 0\n");
            return 0;
        }
    }
    free(eu);
    free(ev);

    long long cost = eval_cost();
    long long mincost = cost;
    long long since = 0;

    while (elapsed() < DEADLINE) {
        if (cost == 0) {
            save_best();
            if (!grow()) break;
            cost = eval_cost();
            mincost = cost;
            since = 0;
            continue;
        }
        if (since > STALL) {
            if (bestN == 0) {
                since = 0;
                /* Nothing valid yet: keep annealing. */
            } else {
                restore_best();
                if (!grow()) break;
                cost = eval_cost();
                mincost = cost;
                since = 0;
            }
            continue;
        }

        since++;
        int a1 = listA[rnd_int(nA)];
        int a2 = listA[rnd_int(nA)];
        if (a1 == a2) continue;
        int k1 = rnd_int(DEG), k2 = rnd_int(DEG);
        int b1 = nb[a1 * DEG + k1];
        int b2 = nb[a2 * DEG + k2];
        if (b1 == b2) continue;
        if (slot_of(a1, b2) >= 0 || slot_of(a2, b1) >= 0) continue;
        int s1 = slot_of(b1, a1);
        int s2 = slot_of(b2, a2);
        nb[a1 * DEG + k1] = b2;
        nb[a2 * DEG + k2] = b1;
        nb[b2 * DEG + s2] = a1;
        nb[b1 * DEG + s1] = a2;

        long long nc = eval_cost();
        if (nc <= cost || rnd_unit() < exp(-(double)(nc - cost) / TEMP)) {
            cost = nc;
            if (cost < mincost) {
                mincost = cost;
                since = 0;
            }
        } else {
            nb[a1 * DEG + k1] = b1;
            nb[a2 * DEG + k2] = b2;
            nb[b1 * DEG + s1] = a1;
            nb[b2 * DEG + s2] = a2;
        }
    }

    if (bestN > 0) {
        long long m = 0;
        for (int v = 0; v < bestN; v++)
            if (bestSide[v] == 0) m += DEG;
        printf("%d %lld\n", bestN, m);
        for (int v = 0; v < bestN; v++) {
            if (bestSide[v] != 0) continue;
            for (int k = 0; k < DEG; k++)
                printf("%d %d\n", v, bestNb[v * DEG + k]);
        }
    } else {
        printf("0 0\n");
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python construction and glue.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


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

    remaining = 0.90 * time_limit - (time.monotonic() - start) - 1.5
    if remaining >= 2.0 and d >= 2:
        moore = lib.moore_bound(d, D)
        rng = random.Random(seed * 7919 + 17)
        # Random d-regular Haar start of order 2m, well below the Moore bound; the engine repairs and grows it.
        m = max(d + 1, int(moore * rng.uniform(0.18, 0.24)))
        S = rng.sample(range(m), d)
        sn, se = lib.haar_graph(m, S)
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}"],
                            stdin_graph=(sn, se), timeout=remaining + 6.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
