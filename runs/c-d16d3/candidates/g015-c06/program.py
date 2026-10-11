"""Diameter-3 bipartite search, second approach: degree-preserving annealing repair.

The previous engine only added vertices greedily (one new vertex joined to a covering set).
This version keeps the bipartition fixed and treats the graph as a state to repair:

  * cost = number of unordered vertex pairs at distance > D (exact, bitset BFS).
  * moves: fill spare degree with cross-side edges (never increases cost), and
    degree-preserving double-edge swaps accepted by the Metropolis rule.
  * growth: add one vertex on a random side, joined to d vertices (stealing an edge
    from a saturated neighbour when needed), then anneal until cost is 0 again.
    A failed attempt is rolled back to the last valid snapshot.

Starts are arc-extended projective plane incidence graphs (valid by construction).
Python re-checks everything with lib.is_valid and falls back to a valid graph.
"""
import itertools
import random
import time

import lib

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1024
#define WORDS (MAXN / 64)
#define MAXDEG 32

static int N, Dd, Dist, W;
static int deg[MAXN], adj[MAXN][MAXDEG], side[MAXN];
static uint64_t BUFA[MAXN][WORDS], BUFB[MAXN][WORDS];

static int sdeg[MAXN], sadj[MAXN][MAXDEG], sside[MAXN], sN;
static long cur_cost;
static double T;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double urand(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double elapsed(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Number of unordered pairs at distance > Dist. */
static long cost(void) {
    uint64_t (*c)[WORDS] = BUFA;
    uint64_t (*nx)[WORDS] = BUFB;
    W = (N + 63) / 64;
    for (int v = 0; v < N; v++) {
        for (int w = 0; w < W; w++) c[v][w] = 0;
        c[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int s = 0; s < Dist; s++) {
        for (int v = 0; v < N; v++) {
            for (int w = 0; w < W; w++) nx[v][w] = c[v][w];
            for (int k = 0; k < deg[v]; k++) {
                int u = adj[v][k];
                for (int w = 0; w < W; w++) nx[v][w] |= c[u][w];
            }
        }
        uint64_t (*t)[WORDS] = c;
        c = nx;
        nx = t;
    }
    long bad = 0;
    for (int v = 0; v < N; v++) {
        int p = 0;
        for (int w = 0; w < W; w++) p += popc(c[v][w]);
        bad += N - p;
    }
    return bad / 2;
}

static int has_edge(int a, int b) {
    for (int k = 0; k < deg[a]; k++)
        if (adj[a][k] == b) return 1;
    return 0;
}

static void remove_from(int v, int u) {
    for (int k = 0; k < deg[v]; k++) {
        if (adj[v][k] == u) {
            adj[v][k] = adj[v][--deg[v]];
            return;
        }
    }
}

static void remove_edge(int a, int b) {
    remove_from(a, b);
    remove_from(b, a);
}

static void add_edge(int a, int b) {
    adj[a][deg[a]++] = b;
    adj[b][deg[b]++] = a;
}

static void snap_save(void) {
    sN = N;
    memcpy(sdeg, deg, sizeof(deg));
    memcpy(sadj, adj, sizeof(adj));
    memcpy(sside, side, sizeof(side));
}

static void snap_restore(void) {
    N = sN;
    memcpy(deg, sdeg, sizeof(deg));
    memcpy(adj, sadj, sizeof(adj));
    memcpy(side, sside, sizeof(side));
    cur_cost = 0;
}

/* Add one spare-degree cross-side edge; returns 1 if an edge was added. */
static int fill_one(void) {
    static int L0[MAXN], L1[MAXN];
    int n0 = 0, n1 = 0;
    for (int v = 0; v < N; v++) {
        if (deg[v] >= Dd) continue;
        if (side[v] == 0) L0[n0++] = v;
        else L1[n1++] = v;
    }
    if (n0 == 0 || n1 == 0) return 0;
    for (int t = 0; t < 200; t++) {
        int x = L0[rndint(n0)], y = L1[rndint(n1)];
        if (!has_edge(x, y)) {
            add_edge(x, y);
            cur_cost = cost();
            return 1;
        }
    }
    return 0;
}

/* Degree-preserving double-edge swap, Metropolis acceptance. */
static int swap_move(void) {
    int p = rndint(N), p2 = rndint(N);
    if (deg[p] == 0 || deg[p2] == 0) return 0;
    int q1 = adj[p][rndint(deg[p])];
    int q2 = adj[p2][rndint(deg[p2])];
    int x, y, x2, y2;
    if (side[p] == 0) { x = p; y = q1; } else { x = q1; y = p; }
    if (side[p2] == 0) { x2 = p2; y2 = q2; } else { x2 = q2; y2 = p2; }
    if (x == x2 || y == y2) return 0;
    if (has_edge(x, y2) || has_edge(x2, y)) return 0;
    remove_edge(x, y);
    remove_edge(x2, y2);
    add_edge(x, y2);
    add_edge(x2, y);
    long nc = cost();
    long delta = nc - cur_cost;
    if (delta <= 0 || urand() < exp(-(double)delta / T)) {
        cur_cost = nc;
        return 1;
    }
    remove_edge(x, y2);
    remove_edge(x2, y);
    add_edge(x, y);
    add_edge(x2, y2);
    return 0;
}

static int anneal(long K, double tlimit) {
    for (long it = 0; it < K; it++) {
        if (cur_cost == 0) return 1;
        if (fill_one()) continue;
        swap_move();
        if ((it & 63) == 0 && elapsed() > tlimit) break;
    }
    return cur_cost == 0;
}

/* Add a new vertex on side X joined to up to Dd vertices of the other side. */
static void add_vertex(int X) {
    int x = N;
    side[x] = X;
    deg[x] = 0;
    N++;
    for (int t = 0; t < Dd; t++) {
        int cand = -1;
        for (int tries = 0; tries < 200 && cand < 0; tries++) {
            int y = rndint(N);
            if (side[y] == X || deg[y] >= Dd || has_edge(x, y)) continue;
            cand = y;
        }
        if (cand < 0) {
            int y = -1;
            for (int tries = 0; tries < 200; tries++) {
                int z = rndint(N);
                if (side[z] != X && !has_edge(x, z)) { y = z; break; }
            }
            if (y < 0) break;
            if (deg[y] >= Dd) {
                int z = adj[y][rndint(deg[y])];
                remove_edge(y, z);
            }
            cand = y;
        }
        add_edge(x, cand);
    }
}

static int bip_sides(void) {
    static int q[MAXN];
    for (int v = 0; v < N; v++) side[v] = -1;
    for (int s = 0; s < N; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int h = 0, t = 0;
        q[t++] = s;
        while (h < t) {
            int u = q[h++];
            for (int k = 0; k < deg[u]; k++) {
                int v = adj[u][k];
                if (side[v] < 0) {
                    side[v] = 1 - side[u];
                    q[t++] = v;
                } else if (side[v] == side[u]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    Dd = atoi(argv[1]);
    if (Dd > MAXDEG - 1) Dd = MAXDEG - 1;
    Dist = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 777ULL;
    if (rs == 0) rs = 1;

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) n = 0;
    if (n <= 0 || n > MAXN - 8 || Dist < 1 || Dd < 1) {
        printf("0 0\n");
        return 0;
    }
    N = n;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || u >= N || v < 0 || v >= N || u == v) continue;
        if (deg[u] >= Dd || deg[v] >= Dd || has_edge(u, v)) continue;
        add_edge(u, v);
    }
    if (!bip_sides()) {
        printf("0 0\n");
        return 0;
    }

    double t_end = elapsed() + budget;
    cur_cost = cost();
    snap_save();

    /* If the start is not valid, try to repair it at fixed size; otherwise give up. */
    if (cur_cost > 0) {
        while (cur_cost > 0 && elapsed() < t_end) {
            T = 0.3 + 0.7 * urand();
            anneal(3000, t_end);
        }
        if (cur_cost > 0) {
            snap_restore();
            cur_cost = 0;
            /* the original start is not guaranteed valid; let the caller reject it */
        }
    }
    if (cur_cost == 0) {
        /* Growth loop: add a vertex, anneal to cost 0, roll back on failure. */
        while (elapsed() < t_end && N < MAXN - 4) {
            snap_save();
            int X = rndint(2);
            add_vertex(X);
            cur_cost = cost();
            T = 0.3 + 0.8 * urand();
            int ok = anneal(4000, t_end);
            if (!ok) snap_restore();
        }
    }
    if (cur_cost != 0) {
        snap_restore();
    }

    int M = 0;
    for (int v = 0; v < N; v++)
        for (int k = 0; k < deg[v]; k++)
            if (adj[v][k] > v) M++;
    printf("%d %d\n", N, M);
    for (int v = 0; v < N; v++)
        for (int k = 0; k < deg[v]; k++)
            if (adj[v][k] > v) printf("%d %d\n", v, adj[v][k]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence starts (diameter 3), as in the parent.
# ----------------------------------------------------------------------------

def _pg_data(q):
    """Return (m, edges, point_lines, line_points, index, pts) for PG(2, q)."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, point_lines, line_points, index, pts


def _loads_ok(S, s, m, point_lines, line_points):
    """True if every line holds <= s points of S and every point lies on <= s lines indexed by S."""
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
    """Randomized greedy choice of S with all loads <= s; returns the largest found."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        cl = [0] * m
        cp = [0] * m
        S = []
        for P in order:
            if all(cl[L] < s for L in point_lines[P]) and all(cp[Q] < s for Q in line_points[P]):
                S.append(P)
                for L in point_lines[P]:
                    cl[L] += 1
                for Q in line_points[P]:
                    cp[Q] += 1
        if len(S) > len(best):
            best = S
    return best


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    """Old PG incidence plus a new A and a new B vertex per element of S."""
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _arc_extensions(d, deadline, rng):
    """Return (n, edges) candidates for each prime power q with q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, pl, lp, index, _pts = _pg_data(q)
        cands = [[]]
        if s >= 1:
            cands.append(_greedy_arc(m, s, pl, lp, rng, 40, deadline))
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if _loads_ok(cs, s, m, pl, lp):
                cands.append(cs)
        S = max(cands, key=len)
        if not _loads_ok(S, s, m, pl, lp):
            continue
        out.append(_arc_graph(m, edges, pl, lp, S))
    return out


# ----------------------------------------------------------------------------
# C annealing driver.
# ----------------------------------------------------------------------------

def _anneal(n0, e0, d, D, seed, budget, timeout):
    """Run the C annealing repair engine from (n0, e0) and parse its output."""
    text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                     stdin_graph=(n0, e0), timeout=timeout)
    return lib.parse_graph_text(text)


def build(d, D, seed, time_limit):
    """Return the best valid (n, edges) found within about 75% of time_limit."""
    t0 = time.monotonic()

    def left():
        return time_limit - (time.monotonic() - t0)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for every D >= 2.
    fallback = lib.haar_graph(d, range(d))
    best = fallback if lib.is_valid(fallback[0], fallback[1], d, D) else (1, [])

    # Starts: arc-extended projective plane graphs (valid by construction for D >= 3).
    start = best
    if D >= 3 and d >= 3:
        try:
            rng = random.Random(seed * 7919 + d)
            starts = _arc_extensions(d, t0 + 0.15 * time_limit, rng)
            for g in sorted(starts, key=lambda g: -g[0]):
                if lib.is_valid(g[0], g[1], d, D):
                    start = g
                    break
        except Exception:
            start = best
    if start[0] > best[0]:
        best = start

    # Repair/grow the start with the annealing engine.
    budget = 0.75 * time_limit - (time.monotonic() - t0) - 2.0
    if budget >= 2.0 and left() > budget + 3.0:
        try:
            n1, e1 = _anneal(start[0], start[1], d, D, seed * 31 + 7, budget,
                             timeout=max(1.0, left() - 1.0))
            if n1 > best[0] and lib.is_valid(n1, e1, d, D):
                best = (n1, e1)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
