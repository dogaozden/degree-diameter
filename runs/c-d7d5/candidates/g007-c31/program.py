import random
import time

import lib


# ----------------------------------------------------------------------------
# New construction: annealing on the full (non-symmetric) bipartite graph.
#
# The engine keeps a bipartite graph with max degree DEG and diameter <= DIAM.
# Two kinds of step:
#   * Grow: when the current graph is valid, insert a new pair (x in A, y in B).
#     Take DEG edges (a_i, b_i) with distinct a_i and distinct b_i, and rewire
#     each to (a_i, y) plus a new edge (x, b_i). Degrees of old vertices are
#     unchanged, x and y get degree DEG, and the vertex count rises by 2.
#   * Repair: simulated annealing with 2-switches (a1 b1, a2 b2 -> a1 b2, a2 b1),
#     which keep every degree. Cost = number of ordered vertex pairs at distance
#     > DIAM, computed exactly with bitset BFS from all vertices.
# The best valid graph is snapshotted. After a stall, the engine restores that
# snapshot and grows again with new random choices.
#
# Usage: prog DEG DIAM CAP seed slice_seconds < start_graph
# Start graph: "n m" + edges, or "0 0" for K_{DEG,DEG}. Prints a valid graph
# ("n m" + edges), or "0 0" if none was found.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

static int DEG, DIAM, CAP, CAPE, WMAX;
static int N, E;
static int *eu, *ev, *side, *deg, *adj;
static int *snapEU, *snapEV, *snapSide;
static int snapN = 0, snapE = 0;
static uint64_t *R0, *R1;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int has_edge(int a, int b) {
    const int *p = adj + (size_t)a * DEG;
    for (int t = 0; t < deg[a]; t++) if (p[t] == b) return 1;
    return 0;
}

static void add_nb(int v, int w) {
    adj[(size_t)v * DEG + deg[v]] = w;
    deg[v]++;
}

static void replace_nb(int v, int old, int nw) {
    int *p = adj + (size_t)v * DEG;
    for (int t = 0; t < deg[v]; t++) {
        if (p[t] == old) { p[t] = nw; return; }
    }
}

/* Unconditional 2-switch. Calling it again on the same pair undoes it. */
static void apply_switch(int e1, int e2) {
    int a1 = eu[e1], b1 = ev[e1], a2 = eu[e2], b2 = ev[e2];
    replace_nb(a1, b1, b2);
    replace_nb(a2, b2, b1);
    replace_nb(b1, a1, a2);
    replace_nb(b2, a2, a1);
    eu[e1] = a1; ev[e1] = b2;
    eu[e2] = a2; ev[e2] = b1;
}

static int try_switch(int e1, int e2) {
    if (e1 == e2) return 0;
    int a1 = eu[e1], b1 = ev[e1], a2 = eu[e2], b2 = ev[e2];
    if (a1 == a2 || b1 == b2) return 0;
    if (has_edge(a1, b2) || has_edge(a2, b1)) return 0;
    apply_switch(e1, e2);
    return 1;
}

static int cost_eval(void) {
    int W = (N + 63) >> 6;
    for (int v = 0; v < N; v++) {
        uint64_t *r = R0 + (size_t)v * W;
        memset(r, 0, sizeof(uint64_t) * (size_t)W);
        r[v >> 6] |= 1ULL << (v & 63);
    }
    for (int it = 0; it < DIAM; it++) {
        for (int v = 0; v < N; v++) {
            uint64_t *dst = R1 + (size_t)v * W;
            memcpy(dst, R0 + (size_t)v * W, sizeof(uint64_t) * (size_t)W);
            const int *av = adj + (size_t)v * DEG;
            for (int t = 0; t < deg[v]; t++) {
                const uint64_t *src = R0 + (size_t)av[t] * W;
                for (int w = 0; w < W; w++) dst[w] |= src[w];
            }
        }
        uint64_t *tmp = R0; R0 = R1; R1 = tmp;
    }
    long long cost = 0;
    for (int v = 0; v < N; v++) {
        const uint64_t *r = R0 + (size_t)v * W;
        int pc = 0;
        for (int w = 0; w < W; w++) pc += __builtin_popcountll(r[w]);
        cost += N - pc;
    }
    return (int)cost;
}

/* Insert a new A vertex x = N and B vertex y = N+1 by rewiring DEG edges. */
static int grow(void) {
    if (N + 2 > CAP || E < DEG || E + DEG > CAPE) return 0;
    int ch[64];
    int tries = 0, k = 0;
    while (k < DEG && tries < 20000) {
        tries++;
        int e = rndint(E);
        int dup = 0;
        for (int i = 0; i < k; i++) if (ch[i] == e) { dup = 1; break; }
        if (dup) continue;
        int a = eu[e], b = ev[e], bad = 0;
        for (int i = 0; i < k; i++) {
            if (eu[ch[i]] == a || ev[ch[i]] == b) { bad = 1; break; }
        }
        if (bad) continue;
        ch[k++] = e;
    }
    if (k < DEG) return 0;
    int x = N, y = N + 1;
    side[x] = 0; side[y] = 1;
    deg[x] = 0; deg[y] = 0;
    for (int i = 0; i < DEG; i++) {
        int e = ch[i], a = eu[e], b = ev[e];
        replace_nb(a, b, y);
        replace_nb(b, a, x);
        ev[e] = y;
        add_nb(y, a);
        add_nb(x, b);
        eu[E] = x; ev[E] = b; E++;
    }
    N += 2;
    return 1;
}

static void take_snap(void) {
    snapN = N;
    snapE = E;
    memcpy(snapEU, eu, sizeof(int) * (size_t)E);
    memcpy(snapEV, ev, sizeof(int) * (size_t)E);
    memcpy(snapSide, side, sizeof(int) * (size_t)N);
}

static void rebuild(void) {
    for (int v = 0; v < N; v++) deg[v] = 0;
    for (int e = 0; e < E; e++) {
        add_nb(eu[e], ev[e]);
        add_nb(ev[e], eu[e]);
    }
}

static void restore(void) {
    N = snapN;
    E = snapE;
    memcpy(eu, snapEU, sizeof(int) * (size_t)E);
    memcpy(ev, snapEV, sizeof(int) * (size_t)E);
    memcpy(side, snapSide, sizeof(int) * (size_t)N);
    rebuild();
}

int main(int argc, char **argv) {
    if (argc < 6) { printf("0 0\n"); return 0; }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    CAP = atoi(argv[3]);
    uint64_t seed = strtoull(argv[4], NULL, 10);
    double slice = atof(argv[5]);
    if (DEG < 2 || DEG > 64 || DIAM < 1 || CAP < 4) { printf("0 0\n"); return 0; }

    rs = seed * 0x9E3779B97F4A7C15ULL ^ 0x1234567ULL;
    if (rs == 0) rs = 1;

    CAPE = CAP * DEG + 16;
    WMAX = (CAP + 63) >> 6;
    eu = malloc(sizeof(int) * CAPE);
    ev = malloc(sizeof(int) * CAPE);
    snapEU = malloc(sizeof(int) * CAPE);
    snapEV = malloc(sizeof(int) * CAPE);
    side = malloc(sizeof(int) * CAP);
    snapSide = malloc(sizeof(int) * CAP);
    deg = malloc(sizeof(int) * CAP);
    adj = malloc(sizeof(int) * (size_t)CAP * DEG);
    R0 = malloc(sizeof(uint64_t) * (size_t)CAP * WMAX);
    R1 = malloc(sizeof(uint64_t) * (size_t)CAP * WMAX);
    int *stk = malloc(sizeof(int) * CAP);
    if (!eu || !ev || !snapEU || !snapEV || !side || !snapSide || !deg || !adj || !R0 || !R1 || !stk) {
        printf("0 0\n");
        return 0;
    }

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) { n = 0; m = 0; }

    if (n > 0) {
        if (n > CAP || m < 0 || m > CAPE - 4 * DEG) { printf("0 0\n"); return 0; }
        for (int v = 0; v < n; v++) { deg[v] = 0; side[v] = -1; }
        int ok = 1;
        for (int i = 0; i < m && ok; i++) {
            int u, v;
            if (scanf("%d %d", &u, &v) != 2) { ok = 0; break; }
            if (u < 0 || v < 0 || u >= n || v >= n || u == v) { ok = 0; break; }
            if (has_edge(u, v) || deg[u] >= DEG || deg[v] >= DEG) { ok = 0; break; }
            add_nb(u, v);
            add_nb(v, u);
            eu[i] = u; ev[i] = v;
        }
        for (int s = 0; s < n && ok; s++) {
            if (side[s] != -1) continue;
            side[s] = 0;
            int sp = 0;
            stk[sp++] = s;
            while (sp > 0 && ok) {
                int u = stk[--sp];
                for (int t = 0; t < deg[u]; t++) {
                    int w = adj[(size_t)u * DEG + t];
                    if (side[w] == -1) {
                        side[w] = 1 - side[u];
                        stk[sp++] = w;
                    } else if (side[w] == side[u]) {
                        ok = 0;
                        break;
                    }
                }
            }
        }
        if (!ok) { printf("0 0\n"); return 0; }
        for (int i = 0; i < m; i++) {
            if (side[eu[i]] == 1) {
                int t = eu[i]; eu[i] = ev[i]; ev[i] = t;
            }
        }
        N = n;
        E = m;
    } else {
        if (CAP < 2 * DEG) { printf("0 0\n"); return 0; }
        N = 2 * DEG;
        E = 0;
        for (int i = 0; i < DEG; i++) {
            side[i] = 0;
            side[DEG + i] = 1;
        }
        for (int i = 0; i < DEG; i++) {
            for (int j = 0; j < DEG; j++) {
                eu[E] = i;
                ev[E] = DEG + j;
                E++;
            }
        }
        rebuild();
    }

    clock_t t0 = clock();
    int cur = cost_eval();
    if (cur == 0) take_snap();

    int stall = 0;
    const int STALL = 6000;
    while ((double)(clock() - t0) / CLOCKS_PER_SEC < slice) {
        if (cur == 0) {
            if (N > snapN) take_snap();
            if (!grow()) break;
            cur = cost_eval();
            stall = 0;
            continue;
        }
        double T = 0.3 + 1.5 * (1.0 - (double)stall / STALL);
        int e1 = rndint(E), e2 = rndint(E);
        if (try_switch(e1, e2)) {
            int nc = cost_eval();
            if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
                cur = nc;
            } else {
                apply_switch(e1, e2);
            }
        }
        stall++;
        if (stall >= STALL) {
            stall = 0;
            if (snapN > 0) {
                restore();
                cur = cost_eval();
            }
        }
    }

    if (snapN > 0) {
        printf("%d %d\n", snapN, snapE);
        for (int e = 0; e < snapE; e++) {
            printf("%d %d\n", snapEU[e], snapEV[e]);
        }
    } else {
        printf("0 0\n");
    }
    fflush(stdout);
    return 0;
}
"""


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    t_start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = t_start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    if D == 2:
        return best

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact construction for D = 3 when d - 1 is a prime power.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    # Vertex cap: the Moore bound, bounded for speed.
    cap = min(lib.moore_bound(d, D), 3200)

    # Grow-and-repair annealing. Each run continues from the best graph so far.
    while True:
        if best[0] >= cap:
            break
        remaining = deadline - time.monotonic()
        if remaining < 3.0:
            break
        slice_s = min(remaining - 1.0, max(5.0, budget / 2.5))
        try:
            out = lib.run_c(
                C_SOURCE,
                [d, D, cap, rng.randrange(1, 10 ** 9), f"{slice_s:.2f}"],
                stdin_graph=best,
                timeout=slice_s + 15.0,
            )
        except Exception:
            break
        try:
            n, e = lib.parse_graph_text(out)
        except ValueError:
            continue
        consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
