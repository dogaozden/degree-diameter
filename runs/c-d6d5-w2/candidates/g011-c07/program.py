import itertools
import time

import lib


# ----------------------------------------------------------------------------
# New construction: regular bipartite graphs grown by vertex-pair insertion.
#
# The C engine keeps a DEG-regular bipartite graph that is valid for diameter
# DIAM. It grows the graph by one A-vertex and one B-vertex at a time: six
# edges (a_i, b_i) with distinct endpoints are removed, and x is joined to all
# b_i while y is joined to all a_i. Every degree stays DEG. Simulated annealing
# with regularity-preserving 2-switches then repairs the diameter. Bad ordered
# pairs are counted with bitset BFS. When a repair fails, the search restarts
# from the last valid graph. The largest valid graph is returned.
#
# This is a different family from the voltage-lift search: it has no group
# structure. It is a high-risk experiment. The fallback is the best of
# K_{d,d} and the projective-plane incidence graph, and the output is always
# validated in Python.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXV 1600
#define MAXM (MAXV * 16)
#define MAXW (MAXV / 64 + 2)
#define PHASE_IT 3000
#define TBASE 2.0

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

/* Current graph: edge k joins EU[k] (side 0) and EV[k] (side 1). Vertex ids 0..V-1. */
static int V, M;
static int EU[MAXM], EV[MAXM];
static int bestEU[MAXM], bestEV[MAXM];
static int bestV = 0, bestM = 0;
static int RU[MAXM], RV[MAXM];
static int col[MAXV];
static int deg_in[MAXV];
static int adj[MAXV * 16];
static uint64_t R1[MAXV * MAXW], R2[MAXV * MAXW];
static unsigned char has[MAXV][MAXV];
static int usedA[MAXV], usedB[MAXV];
static int stampc = 0;

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Ordered pairs at distance > DIAM (0 means valid). */
static long long eval_cost(void) {
    static int cnt[MAXV];
    for (int v = 0; v < V; v++) cnt[v] = 0;
    for (int k = 0; k < M; k++) {
        int a = EU[k], b = EV[k];
        adj[a * DEG + cnt[a]++] = b;
        adj[b * DEG + cnt[b]++] = a;
    }
    int W = (V + 63) / 64;
    uint64_t *cur = R1, *nxt = R2;
    for (int v = 0; v < V; v++) {
        for (int w = 0; w < W; w++) cur[v * W + w] = 0;
        cur[v * W + (v >> 6)] = 1ULL << (v & 63);
    }
    for (int lvl = 0; lvl < DIAM; lvl++) {
        for (int v = 0; v < V; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            const uint64_t *src = cur + (size_t)v * W;
            for (int w = 0; w < W; w++) dst[w] = src[w];
            for (int i = 0; i < DEG; i++) {
                const uint64_t *s2 = cur + (size_t)adj[v * DEG + i] * W;
                for (int w = 0; w < W; w++) dst[w] |= s2[w];
            }
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
    }
    long long covered = 0;
    for (int i = 0; i < V * W; i++) covered += popc(cur[i]);
    return (long long)V * V - covered;
}

/* 2-switch: (a1,b1),(a2,b2) -> (a1,b2),(a2,b1). Applying it again to the result undoes it. */
static int do_switch(int k1, int k2) {
    int a1 = EU[k1], b1 = EV[k1], a2 = EU[k2], b2 = EV[k2];
    if (a1 == a2 || b1 == b2) return 0;
    if (has[a1][b2] || has[a2][b1]) return 0;
    has[a1][b1] = 0;
    has[a2][b2] = 0;
    has[a1][b2] = 1;
    has[a2][b1] = 1;
    EV[k1] = b2;
    EV[k2] = b1;
    return 1;
}

/* Insert one A-vertex x = V and one B-vertex y = V+1 with DEG edges each. */
static int grow_once(void) {
    if (V + 2 > MAXV) return 0;
    if (M + DEG > MAXM) return 0;
    stampc++;
    int ks[16];
    int nk = 0;
    for (long att = 0; att < 200000 && nk < DEG; att++) {
        int k = rnd_int(M);
        int a = EU[k], b = EV[k];
        if (usedA[a] == stampc || usedB[b] == stampc) continue;
        usedA[a] = stampc;
        usedB[b] = stampc;
        ks[nk++] = k;
    }
    if (nk < DEG) return 0;
    int x = V, y = V + 1;
    for (int i = 0; i < nk; i++) {
        int k = ks[i];
        int a = EU[k], b = EV[k];
        has[a][b] = 0;
        EU[k] = x;
        EV[k] = b;
        has[x][b] = 1;
        EU[M] = a;
        EV[M] = y;
        has[a][y] = 1;
        M++;
    }
    V += 2;
    return 1;
}

static void save_best(void) {
    bestV = V;
    bestM = M;
    memcpy(bestEU, EU, sizeof(int) * (size_t)M);
    memcpy(bestEV, EV, sizeof(int) * (size_t)M);
}

static void restore_best(void) {
    V = bestV;
    M = bestM;
    memcpy(EU, bestEU, sizeof(int) * (size_t)M);
    memcpy(EV, bestEV, sizeof(int) * (size_t)M);
    memset(has, 0, sizeof has);
    for (int k = 0; k < M; k++) has[EU[k]][EV[k]] = 1;
}

/* Reads a DEG-regular bipartite start graph from stdin, or builds K_{DEG,DEG} if "0 0". */
static int load_input(void) {
    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) n = 0;
    if (n <= 0) {
        V = 2 * DEG;
        M = 0;
        for (int i = 0; i < DEG; i++)
            for (int j = 0; j < DEG; j++) {
                EU[M] = i;
                EV[M] = DEG + j;
                M++;
            }
        return 1;
    }
    if (n > MAXV - 2 || m < 0 || m > MAXM - 16 * 2) return 0;
    for (int k = 0; k < m; k++) {
        if (scanf("%d %d", &RU[k], &RV[k]) != 2) return 0;
        if (RU[k] < 0 || RU[k] >= n || RV[k] < 0 || RV[k] >= n || RU[k] == RV[k]) return 0;
    }
    for (int v = 0; v < n; v++) {
        deg_in[v] = 0;
        col[v] = -1;
    }
    for (int k = 0; k < m; k++) {
        deg_in[RU[k]]++;
        deg_in[RV[k]]++;
    }
    for (int v = 0; v < n; v++)
        if (deg_in[v] != DEG) return 0;
    for (int s = 0; s < n; s++) {
        if (col[s] != -1) continue;
        col[s] = 0;
        int changed = 1;
        while (changed) {
            changed = 0;
            for (int k = 0; k < m; k++) {
                int a = RU[k], b = RV[k];
                if (col[a] != -1 && col[b] == -1) {
                    col[b] = 1 - col[a];
                    changed = 1;
                } else if (col[b] != -1 && col[a] == -1) {
                    col[a] = 1 - col[b];
                    changed = 1;
                }
            }
        }
    }
    for (int k = 0; k < m; k++)
        if (col[RU[k]] == col[RV[k]]) return 0;
    V = n;
    M = m;
    for (int k = 0; k < m; k++) {
        if (col[RU[k]] == 0) {
            EU[k] = RU[k];
            EV[k] = RV[k];
        } else {
            EU[k] = RV[k];
            EV[k] = RU[k];
        }
    }
    return 1;
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
    uint64_t sm = sd * 2654435761ULL + 987654321ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);
    if (DEG < 2 || DEG > 16 || DIAM < 2 || !load_input()) {
        printf("0 0\n");
        return 0;
    }
    for (int k = 0; k < M; k++) {
        if (has[EU[k]][EV[k]]) {
            printf("0 0\n");
            return 0;
        }
        has[EU[k]][EV[k]] = 1;
    }

    long long cost = eval_cost();
    int it = 0;
    while (elapsed() < DEADLINE) {
        if (cost == 0) {
            save_best();
            if (!grow_once()) break;
            cost = eval_cost();
            it = 0;
            continue;
        }
        if (it >= PHASE_IT) {
            if (bestV > 0) {
                restore_best();
                cost = eval_cost();
            }
            it = 0;
            continue;
        }
        it++;
        int k1 = rnd_int(M), k2 = rnd_int(M);
        if (k1 == k2) continue;
        if (!do_switch(k1, k2)) continue;
        long long c2 = eval_cost();
        double T = TBASE * (1.0 - (double)it / PHASE_IT) + 0.05;
        if (c2 <= cost || rnd_unit() < exp(-(double)(c2 - cost) / T)) {
            cost = c2;
        } else {
            do_switch(k1, k2);
        }
    }

    if (bestV > 0) {
        printf("%d %d\n", bestV, bestM);
        for (int k = 0; k < bestM; k++)
            printf("%d %d\n", bestEU[k], bestEV[k]);
    } else {
        printf("0 0\n");
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Safe baseline: projective-plane incidence graphs (diameter 3, valid for D >= 3).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Driver: baselines in Python, then the C grow-and-repair search from the best baseline.
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

    # The C deadline is measured from its own start, so reserve time for compile and parsing.
    remaining = 0.9 * time_limit - (time.monotonic() - start) - 1.5
    if remaining >= 2.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}"],
                            stdin_graph=best, timeout=remaining + 8.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
