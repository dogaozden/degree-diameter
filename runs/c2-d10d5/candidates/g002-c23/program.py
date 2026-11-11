"""Random bipartite regular graph grown by vertex insertion, then repaired by 2-switch annealing (C).

Not a lift: the graph is kept d-regular and bipartite throughout. Starting from K_{d,d},
each step inserts new A and B vertices by splitting d existing edges, then a simulated
annealing over 2-switches minimizes the number of vertex pairs at distance > D. A state
is kept only when that count reaches zero. Exact D = 3 constructions and K_{d,d} remain
the fallbacks.
"""
import time

import lib

C_SOURCE = r'''
/* Grow-and-repair search for bipartite degree-diameter graphs.
 *
 * Usage:  prog d D seed time_limit   (stdin is read and ignored)
 * stdout: "n m" then m lines "u v" for the largest valid graph found.
 *
 * State: h A-vertices (0..h-1) and h B-vertices (h..2h-1), d-regular, bipartite.
 * Cost: number of unordered pairs at distance > D, from bitset BFS of depth D.
 * Moves: 2-switch (a1,b1),(a2,b2) -> (a1,b2),(a2,b1), accepted by annealing.
 * Growth: add one A and one B vertex by splitting d random edges.
 * Only zero-cost states are saved as the current valid graph.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXH 2600
#define MAXN (2 * MAXH)
#define MAXW ((MAXN + 63) / 64)
#define MAXD 32
#define MAXE (MAXH * MAXD)

static int d, D;
static double t_end;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

/* current state */
static int h, E;
static int eu[MAXE], ev[MAXE];
static unsigned char adj[MAXH][MAXH];

/* last valid state */
static int sv_h, sv_E;
static int sv_eu[MAXE], sv_ev[MAXE];
static unsigned char sv_adj[MAXH][MAXH];

/* evaluation buffers */
static int nbl[MAXN][MAXD];
static int ncnt[MAXN];
static uint64_t bsA[MAXN * MAXW], bsB[MAXN * MAXW];
static int unr_v[MAXN];

static long evaluate(void) {
    int N = 2 * h, W = (N + 63) / 64;
    uint64_t *cur = bsA, *nx = bsB, *tmp;
    memset(cur, 0, sizeof(uint64_t) * (size_t)N * W);
    for (int v = 0; v < N; v++) ncnt[v] = 0;
    for (int e = 0; e < E; e++) {
        int a = eu[e], b = h + ev[e];
        nbl[a][ncnt[a]++] = b;
        nbl[b][ncnt[b]++] = a;
    }
    for (int v = 0; v < N; v++) cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < N; v++) {
            uint64_t *dst = nx + (size_t)v * W;
            const uint64_t *src = cur + (size_t)v * W;
            memcpy(dst, src, sizeof(uint64_t) * (size_t)W);
            for (int k = 0; k < ncnt[v]; k++) {
                const uint64_t *s2 = cur + (size_t)nbl[v][k] * W;
                for (int w = 0; w < W; w++) dst[w] |= s2[w];
            }
        }
        tmp = cur;
        cur = nx;
        nx = tmp;
    }
    long unr = 0;
    for (int v = 0; v < N; v++) {
        int pc = 0;
        const uint64_t *row = cur + (size_t)v * W;
        for (int w = 0; w < W; w++) pc += __builtin_popcountll(row[w]);
        unr_v[v] = N - pc;
        unr += N - pc;
    }
    return unr / 2;
}

static void save_state(void) {
    sv_h = h;
    sv_E = E;
    memcpy(sv_eu, eu, sizeof(int) * (size_t)E);
    memcpy(sv_ev, ev, sizeof(int) * (size_t)E);
    memcpy(sv_adj, adj, sizeof(adj));
}

static void restore_state(void) {
    h = sv_h;
    E = sv_E;
    memcpy(eu, sv_eu, sizeof(int) * (size_t)E);
    memcpy(ev, sv_ev, sizeof(int) * (size_t)E);
    memcpy(adj, sv_adj, sizeof(adj));
}

/* Add one A vertex and one B vertex, each with d edges, by splitting d existing edges. */
static int grow_one(void) {
    int na = h, nb = h;
    h++;
    for (int t = 0; t < d; t++) {
        int i = -1, found = 0;
        for (int tr = 0; tr < 200000 && !found; tr++) {
            int e = rndint(E);
            int x = eu[e], y = ev[e];
            if (x == na || y == nb) continue;
            if (adj[na][y] || adj[x][nb]) continue;
            i = e;
            found = 1;
        }
        if (!found) return 0;
        int x = eu[i], y = ev[i];
        adj[x][y] = 0;
        adj[na][y] = 1;
        adj[x][nb] = 1;
        ev[i] = nb;          /* edge i becomes (x, nb) */
        eu[E] = na;          /* new edge (na, y) */
        ev[E] = y;
        E++;
    }
    return 1;
}

/* Simulated annealing on 2-switches. Returns the final cost; 0 means the state is valid. */
static long repair(long max_moves, double tcap) {
    long cost = evaluate();
    if (cost == 0) return 0;
    double T0 = 0.5 + 0.02 * (double)cost;
    for (long t = 0; t < max_moves && cost > 0; t++) {
        if (now() > tcap) break;
        double frac = (double)t / (double)max_moves;
        double T = T0 * (1.0 - frac) + 0.05;
        int i = -1;
        if (rnd01() < 0.5) {
            int v = -1;
            for (int tr = 0; tr < 64; tr++) {
                int u = rndint(2 * h);
                if (unr_v[u] > 0) { v = u; break; }
            }
            if (v >= 0) {
                int st = rndint(E);
                for (int k = 0; k < E; k++) {
                    int e = st + k;
                    if (e >= E) e -= E;
                    if (v < h ? (eu[e] == v) : (ev[e] == v - h)) { i = e; break; }
                }
            }
        }
        if (i < 0) i = rndint(E);
        int j = rndint(E);
        if (i == j) continue;
        int a1 = eu[i], b1 = ev[i], a2 = eu[j], b2 = ev[j];
        if (adj[a1][b2] || adj[a2][b1]) continue;
        adj[a1][b1] = 0;
        adj[a2][b2] = 0;
        adj[a1][b2] = 1;
        adj[a2][b1] = 1;
        eu[i] = a1; ev[i] = b2;
        eu[j] = a2; ev[j] = b1;
        long c2 = evaluate();
        long delta = c2 - cost;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cost = c2;
        } else {
            adj[a1][b2] = 0;
            adj[a2][b1] = 0;
            adj[a1][b1] = 1;
            adj[a2][b2] = 1;
            eu[i] = a1; ev[i] = b1;
            eu[j] = a2; ev[j] = b2;
        }
    }
    return cost;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit < start\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit * 0.9;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    while (getchar() != EOF) {
    }

    if (D < 2 || d < 2 || d > MAXD || d > MAXH) {
        printf("0 0\n");
        return 0;
    }

    /* Start: K_{d,d}, valid for D >= 2. */
    h = d;
    E = 0;
    memset(adj, 0, sizeof(adj));
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) {
            adj[a][b] = 1;
            eu[E] = a;
            ev[E] = b;
            E++;
        }
    save_state();

    int inc = 1, stuck = 0;
    while (now() < t_end) {
        if (h + inc > MAXH) break;
        int ok = 1;
        for (int p = 0; p < inc && ok; p++) ok = grow_one();
        long c = -1;
        if (ok) {
            double rem = t_end - now();
            double share = rem * 0.25 > 0.3 ? rem * 0.25 : 0.3;
            double cap = now() + share;
            if (cap > t_end) cap = t_end;
            c = repair(4000, cap);
        }
        if (ok && c == 0) {
            save_state();
            stuck = 0;
            int lim = sv_h / 30;
            if (lim < 1) lim = 1;
            inc = inc * 2;
            if (inc > lim) inc = lim;
        } else {
            restore_state();
            if (inc > 1) {
                inc /= 2;
            } else if (++stuck >= 4) {
                break;
            }
        }
    }

    printf("%d %d\n", 2 * sv_h, sv_E);
    for (int e = 0; e < sv_E; e++) printf("%d %d\n", sv_eu[e], sv_h + sv_ev[e]);
    return 0;
}
'''


def _exact(d, D):
    """Exact or record constructions Python builds directly (D = 3 only)."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)           # record order 2(q^2+q+5)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if D < 1 or d < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    try:
        ex = _exact(d, D)
    except Exception:
        ex = None
    if ex is not None and lib.is_valid(ex[0], ex[1], d, D):
        if D == 3 and lib.is_prime_power(d - 1):
            return ex   # calibration: Moore graph, return instantly
        best = ex

    budget = 0.85 * time_limit - 3.0 - (time.monotonic() - t0)
    if budget > 1.0:
        timeout = max(1.0, time_limit - (time.monotonic() - t0) - 4.0)
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             stdin_graph=None, timeout=timeout)
            n, edges = lib.parse_graph_text(text)
            if n > best[0] and lib.is_valid(n, edges, d, D):
                best = (n, edges)
        except Exception:
            pass

    return best
