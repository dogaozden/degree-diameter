import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: annealed repair with validity-guarded vertex insertion.
#
# State: a bipartite graph with max degree d. cost = number of unordered vertex
# pairs farther apart than D. A vertex w joined to a set N of opposite-colour
# vertices is at distance <= D from every old vertex x whenever x lies within
# distance D-1 of some u in N, and insertion never lengthens old distances. So
# inserting while cost == 0 keeps the graph valid.
#
# Moves when cost > 0 or no insertion is possible:
#   - remove a random edge, accept by Metropolis on the change in cost
#     (this can pass through invalid states, which the plain greedy engine cannot),
#   - add a random spare cross edge (never increases cost).
# The best valid graph seen is kept and printed.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>

#define MAXN 1024
#define MAXD 64
#define MAXW (MAXN / 64)
#define MAXE 40000

static int n, d, D, W;
static int deg[MAXN];
static int adj[MAXN][MAXD];
static int col[MAXN];
static uint64_t reach[MAXN][MAXW];
static uint64_t nxt[MAXN][MAXW];
static uint64_t rs = 88172645463325252ULL;
static int bestn = 0, bestm = 0;
static int bestE[MAXE][2];

static uint32_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return (uint32_t)(rs >> 16);
}

static int popc(uint64_t x) {
    int c = 0;
    while (x) { x &= x - 1; c++; }
    return c;
}

static int has_edge(int u, int v) {
    for (int i = 0; i < deg[u]; i++) if (adj[u][i] == v) return 1;
    return 0;
}

static void add_edge(int u, int v) {
    adj[u][deg[u]++] = v;
    adj[v][deg[v]++] = u;
}

static void drop_one(int u, int v) {
    for (int i = 0; i < deg[u]; i++) {
        if (adj[u][i] == v) {
            adj[u][i] = adj[u][--deg[u]];
            return;
        }
    }
}

static void del_edge(int u, int v) {
    drop_one(u, v);
    drop_one(v, u);
}

static void compute_balls(int R) {
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) reach[v][w] = 0;
        reach[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < R; r++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < W; w++) nxt[v][w] = reach[v][w];
            for (int i = 0; i < deg[v]; i++) {
                int u = adj[v][i];
                for (int w = 0; w < W; w++) nxt[v][w] |= reach[u][w];
            }
        }
        for (int v = 0; v < n; v++)
            for (int w = 0; w < W; w++) reach[v][w] = nxt[v][w];
    }
}

/* Number of unordered pairs at distance > D (unreachable pairs included). */
static int cost_now(void) {
    W = (n + 63) >> 6;
    compute_balls(D);
    long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(reach[v][w]);
        bad += n - c;
    }
    return (int)(bad / 2);
}

static int covers_all(const uint64_t *cov) {
    for (int w = 0; w < W; w++) {
        uint64_t want;
        if (w < W - 1) {
            want = ~0ULL;
        } else {
            int r = n - 64 * (W - 1);
            want = (r >= 64) ? ~0ULL : ((1ULL << r) - 1);
        }
        if ((cov[w] & want) != want) return 0;
    }
    return 1;
}

/* Insert a new vertex on `side` if the spare neighbours' (D-1)-balls cover everything.
   Requires reach to hold (D-1)-balls of the current graph. */
static int try_insert(int side) {
    static int cand[MAXN];
    static int used[MAXN];
    int nc = 0;
    for (int u = 0; u < n; u++)
        if (col[u] == 1 - side && deg[u] < d) cand[nc++] = u;
    if (nc == 0) return 0;
    for (int i = nc - 1; i > 0; i--) {
        int j = (int)(rnd() % (uint32_t)(i + 1));
        int t = cand[i]; cand[i] = cand[j]; cand[j] = t;
    }
    for (int i = 0; i < n; i++) used[i] = 0;
    uint64_t cov[MAXW];
    for (int w = 0; w < W; w++) cov[w] = 0;
    int chosen[MAXD];
    int nch = 0;
    while (nch < d && !covers_all(cov)) {
        int best = -1, bg = 0;
        for (int i = 0; i < nc; i++) {
            int u = cand[i];
            if (used[u]) continue;
            int g = 0;
            for (int w = 0; w < W; w++) g += popc(reach[u][w] & ~cov[w]);
            if (g > bg) { bg = g; best = u; }
        }
        if (best < 0) break;
        used[best] = 1;
        chosen[nch++] = best;
        for (int w = 0; w < W; w++) cov[w] |= reach[best][w];
    }
    if (!covers_all(cov)) return 0;
    int w = n;
    n++;
    col[w] = side;
    deg[w] = 0;
    for (int i = 0; i < nch; i++) add_edge(chosen[i], w);
    return 1;
}

static void save_best(void) {
    int m = 0;
    for (int u = 0; u < n; u++) {
        for (int i = 0; i < deg[u]; i++) {
            if (adj[u][i] > u && m < MAXE) {
                bestE[m][0] = u;
                bestE[m][1] = adj[u][i];
                m++;
            }
        }
    }
    bestm = m;
    bestn = n;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXD || D < 2) { printf("0 0\n"); return 0; }

    int N0, M0;
    if (scanf("%d %d", &N0, &M0) != 2) { printf("0 0\n"); return 0; }
    if (N0 < 1 || N0 > MAXN) { printf("0 0\n"); return 0; }
    n = N0;
    W = (n + 63) >> 6;
    for (int i = 0; i < M0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) continue;
        if (deg[u] >= d || deg[v] >= d || has_edge(u, v)) continue;
        add_edge(u, v);
    }

    static int queue[MAXN];
    for (int s = 0; s < n; s++) col[s] = -1;
    for (int s = 0; s < n; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int qh = 0, qt = 0;
        queue[qt++] = s;
        while (qh < qt) {
            int u = queue[qh++];
            for (int i = 0; i < deg[u]; i++) {
                int v = adj[u][i];
                if (col[v] < 0) {
                    col[v] = 1 - col[u];
                    queue[qt++] = v;
                }
            }
        }
    }

    if (cost_now() != 0) { printf("0 0\n"); return 0; }
    save_best();

    clock_t t0 = clock();
    int cur = 0;
    long it = 0;
    while (n < MAXN) {
        if ((double)(clock() - t0) / CLOCKS_PER_SEC > budget) break;
        it++;

        if (cur == 0) {
            W = (n + 63) >> 6;
            compute_balls(D - 1);
            int sides[2] = {0, 1};
            if (rnd() & 1u) { sides[0] = 1; sides[1] = 0; }
            int ok = 0;
            for (int k = 0; k < 2 && !ok; k++) ok = try_insert(sides[k]);
            if (ok) {
                cur = cost_now();
                if (cur == 0 && n > bestn) save_best();
                continue;
            }
        }

        double T = 0.3 + 1.2 * (double)(it % 4000) / 4000.0;
        if ((rnd() % 100u) < 70u) {
            int u = (int)(rnd() % (uint32_t)n);
            if (deg[u] == 0) continue;
            int v = adj[u][rnd() % (uint32_t)deg[u]];
            del_edge(u, v);
            int c2 = cost_now();
            double delta = (double)(c2 - cur);
            int acc = 0;
            if (delta <= 0) acc = 1;
            else if ((double)(rnd() % 1000000u) / 1000000.0 < exp(-delta / T)) acc = 1;
            if (acc) cur = c2;
            else add_edge(u, v);
        } else {
            for (int t = 0; t < 50; t++) {
                int u = (int)(rnd() % (uint32_t)n);
                int v = (int)(rnd() % (uint32_t)n);
                if (u == v || col[u] == col[v]) continue;
                if (deg[u] >= d || deg[v] >= d || has_edge(u, v)) continue;
                add_edge(u, v);
                break;
            }
            cur = cost_now();
        }
    }

    printf("%d %d\n", bestn, bestm);
    for (int i = 0; i < bestm; i++)
        printf("%d %d\n", bestE[i][0], bestE[i][1]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Constructions (all diameter 3 when used for D >= 3, all validated before use).
# ----------------------------------------------------------------------------

def _pg_start(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(min(d - 1, 23), 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo and Lopez graph for degree d when d - 2 is a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        return lib.araujo_lopez_graph(q)
    return None


def _safe(f, *args):
    try:
        return f(*args)
    except Exception:
        return None


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return (2, [(0, 1)]) if d >= 1 else (1, [])

    # Safe fallback: K_{d,d}, diameter 2.
    n0, e0 = lib.haar_graph(d, range(d))
    best = (n0, e0)
    if not lib.is_valid(best[0], best[1], d, D):
        best = (1, [])

    def consider(g):
        nonlocal best
        if g is None:
            return
        try:
            n, e = g
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
        except Exception:
            pass

    # Algebraic starts (valid for D >= 3, and PG incidence is valid for any D >= 3).
    if D >= 3:
        consider(_safe(_pg_start, d))
        consider(_safe(_araujo, d))

    # Annealed repair search from the best start, with a safety margin on time.
    remaining = 0.85 * time_limit - (time.monotonic() - t0) - 1.5
    if remaining >= 0.5:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, round(remaining, 2)],
                            stdin_graph=best, timeout=remaining + 3.0)
            n2, e2 = lib.parse_graph_text(out)
            consider((n2, e2))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
