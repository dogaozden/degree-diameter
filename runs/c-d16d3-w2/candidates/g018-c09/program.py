import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bad-pair annealing with degree-bounded bipartite moves.
#
# The state is a bipartite graph (every edge joins colour 0 to colour 1) with
# max degree d. A new isolated vertex is added, and simulated annealing then
# minimises the number of ordered vertex pairs at distance > D (unreachable
# pairs included). Moves:
#   - 2-switch: (a,b),(c,e) -> (a,e),(c,b). Degrees and bipartiteness are kept.
#   - transfer: a spare vertex x takes an edge (y,z) from a same-side vertex z,
#     so z gives up one edge and x gains one.
#   - add: join two spare vertices on opposite sides.
#   - delete: remove a random edge, which frees capacity.
# Only zero-cost states are kept as the new base. A failed stage is undone, and
# the search retries from the last valid graph. Output is always a valid graph,
# or "0 0" when nothing was found.
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
#define MAXOPS 8
#define ITERS 40000L
#define MAXFAILS 6

static int n, d, D, W;
static int deg[MAXN];
static int adj[MAXN][MAXD];
static int col[MAXN];
static uint64_t reach[MAXN][MAXW];
static uint64_t nxt[MAXN][MAXW];
static int bdeg[MAXN];
static int badj[MAXN][MAXD];
static int bcol[MAXN];
static int bn;
static uint64_t rs = 88172645463325252ULL;
static clock_t t0;
static double budget;

typedef struct { int u, v, add; } Op;
static Op oplog[MAXOPS];
static int nops = 0;

static uint32_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return (uint32_t)(rs >> 16);
}

static double urand(void) { return (rnd() + 0.5) / 4294967296.0; }

static double elapsed(void) { return (double)(clock() - t0) / CLOCKS_PER_SEC; }

static int popc(uint64_t x) {
    int c = 0;
    while (x) { x &= x - 1; c++; }
    return c;
}

static int has_edge(int u, int v) {
    for (int i = 0; i < deg[u]; i++) if (adj[u][i] == v) return 1;
    return 0;
}

static void raw_add(int u, int v) {
    adj[u][deg[u]++] = v;
    adj[v][deg[v]++] = u;
}

static void raw_rem1(int u, int v) {
    for (int i = 0; i < deg[u]; i++) {
        if (adj[u][i] == v) {
            adj[u][i] = adj[u][--deg[u]];
            return;
        }
    }
}

static void raw_rem(int u, int v) {
    raw_rem1(u, v);
    raw_rem1(v, u);
}

static void do_add(int u, int v) {
    raw_add(u, v);
    oplog[nops].u = u;
    oplog[nops].v = v;
    oplog[nops].add = 1;
    nops++;
}

static void do_rem(int u, int v) {
    raw_rem(u, v);
    oplog[nops].u = u;
    oplog[nops].v = v;
    oplog[nops].add = 0;
    nops++;
}

static void undo_all(void) {
    while (nops > 0) {
        nops--;
        Op o = oplog[nops];
        if (o.add) raw_rem(o.u, o.v);
        else raw_add(o.u, o.v);
    }
    nops = 0;
}

/* Number of ordered pairs (x,y), x != y, at distance > D (unreachable included). */
static long bad_count(void) {
    W = (n + 63) >> 6;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) reach[v][w] = 0;
        reach[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < D; r++) {
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
    long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(reach[v][w]);
        bad += n - c;
    }
    return bad;
}

/* Random edge oriented so that *a has colour 0 and *b has colour 1. */
static int random_edge(int *a, int *b) {
    for (int t = 0; t < 200; t++) {
        int u = (int)(rnd() % (uint32_t)n);
        if (deg[u] == 0) continue;
        int v = adj[u][rnd() % (uint32_t)deg[u]];
        if (col[u] == 0) { *a = u; *b = v; }
        else { *a = v; *b = u; }
        return 1;
    }
    return 0;
}

/* Random vertex with spare degree, of colour `side` (or any if side < 0), not equal to avoid. */
static int random_spare(int side, int avoid) {
    for (int t = 0; t < 200; t++) {
        int u = (int)(rnd() % (uint32_t)n);
        if (u == avoid) continue;
        if (side >= 0 && col[u] != side) continue;
        if (deg[u] >= d) continue;
        return u;
    }
    return -1;
}

/* Propose one move; apply it through do_* (logged) and return 1, or return 0 with no change. */
static int propose(void) {
    nops = 0;
    int r = (int)(rnd() % 100u);

    if (r < 40) {                                   /* degree-preserving 2-switch */
        int a, b, c, e;
        if (!random_edge(&a, &b) || !random_edge(&c, &e)) return 0;
        if (has_edge(a, e) || has_edge(c, b)) return 0;
        do_rem(a, b);
        do_rem(c, e);
        do_add(a, e);
        do_add(c, b);
        return 1;
    }
    if (r < 75) {                                   /* transfer an edge endpoint to a spare vertex */
        int x = random_spare(-1, -1);
        if (x < 0) return 0;
        int z = -1;
        for (int t = 0; t < 200; t++) {
            int u = (int)(rnd() % (uint32_t)n);
            if (u != x && col[u] == col[x] && deg[u] > 0) { z = u; break; }
        }
        if (z < 0) return 0;
        int y = adj[z][rnd() % (uint32_t)deg[z]];
        if (y == x || has_edge(x, y)) return 0;
        do_rem(y, z);
        do_add(y, x);
        return 1;
    }
    if (r < 92) {                                   /* add an edge between spare vertices */
        int x = random_spare(-1, -1);
        if (x < 0) return 0;
        int y = random_spare(1 - col[x], x);
        if (y < 0 || has_edge(x, y)) return 0;
        do_add(x, y);
        return 1;
    }
    {                                               /* delete a random edge */
        int a, b;
        if (!random_edge(&a, &b)) return 0;
        do_rem(a, b);
        return 1;
    }
}

/* Anneal until bad_count reaches 0 (return 1) or iterations/time run out (return 0). */
static int anneal(long iters, double T0, double T1, double tlimit) {
    long cost = bad_count();
    if (cost == 0) return 1;
    for (long it = 0; it < iters; it++) {
        if ((it & 127) == 0 && elapsed() > tlimit) break;
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        if (!propose()) continue;
        long c2 = bad_count();
        long delta = c2 - cost;
        if (delta <= 0 || urand() < exp(-(double)delta / T)) {
            cost = c2;
            nops = 0;
        } else {
            undo_all();
        }
        if (cost == 0) return 1;
    }
    return 0;
}

static void save_best(void) {
    bn = n;
    memcpy(badj, adj, sizeof adj);
    memcpy(bdeg, deg, sizeof deg);
    memcpy(bcol, col, sizeof col);
}

static void restore_best(void) {
    n = bn;
    memcpy(adj, badj, sizeof adj);
    memcpy(deg, bdeg, sizeof deg);
    memcpy(col, bcol, sizeof col);
    nops = 0;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    budget = atof(argv[4]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    t0 = clock();

    if (d < 1 || d > MAXD || D < 2) { printf("0 0\n"); return 0; }

    int N0, M0;
    if (scanf("%d %d", &N0, &M0) != 2 || N0 < 1 || N0 >= MAXN - 1) {
        printf("0 0\n");
        return 0;
    }
    n = N0;
    for (int i = 0; i < M0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) continue;
        if (deg[u] >= d || deg[v] >= d || has_edge(u, v)) continue;
        raw_add(u, v);
    }

    /* 2-colour the start graph; it must be bipartite. */
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
                } else if (col[v] == col[u]) {
                    printf("0 0\n");
                    return 0;
                }
            }
        }
    }

    if (bad_count() != 0) { printf("0 0\n"); return 0; }
    save_best();

    int fails = 0;
    while (fails < MAXFAILS && n < MAXN - 1 && elapsed() < budget) {
        int side = (int)(rnd() & 1u);
        int w = n;
        n++;
        col[w] = side;
        deg[w] = 0;
        nops = 0;
        if (anneal(ITERS, 2.0, 0.15, budget)) {
            save_best();
            fails = 0;
        } else {
            restore_best();
            fails++;
        }
    }

    int m2 = 0;
    for (int u = 0; u < bn; u++)
        for (int i = 0; i < bdeg[u]; i++)
            if (badj[u][i] > u) m2++;
    printf("%d %d\n", bn, m2);
    for (int u = 0; u < bn; u++)
        for (int i = 0; i < bdeg[u]; i++)
            if (badj[u][i] > u) printf("%d %d\n", u, badj[u][i]);
    return 0;
}
"""


def _c_grow(graph, d, D, seed, budget):
    """Run the C annealing engine on graph; return (n, edges) or None on any failure."""
    if graph is None or budget < 1.0 or d > 64 or graph[0] >= 1000:
        return None
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                        stdin_graph=(graph[0], graph[1]), timeout=budget + 5.0)
        n2, e2 = lib.parse_graph_text(out)
    except Exception:
        return None
    return (n2, e2) if n2 >= 1 else None


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from PG(2, q) incidence (points 0..m-1, lines m..2m-1). Each old vertex
# has degree q+1, so spare s = d - q - 1.
#
# A-side: a set SA of points; each P in SA gets a new vertex joined to the q+1
# lines through P. Every line may hold at most s points of SA.
# B-side: a set SB of lines; each j in SB gets a new vertex joined to the q+1
# points on j. Every point may lie on at most s lines of SB.
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


def _loads_ok(S, s, m, nbr):
    """True if every target is hit by <= s elements of S, where element x hits nbr[x]."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomized greedy choice of elements so that every target is hit <= s times."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        load = [0] * m
        S = []
        for x in order:
            if all(load[t] < s for t in nbr[x]):
                S.append(x)
                for t in nbr[x]:
                    load[t] += 1
        if len(S) > len(best):
            best = S
    return best


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, SA, SB):
    """Old PG incidence plus one new A-vertex per SA point and one new B-vertex per SB line."""
    na, nb = len(SA), len(SB)
    n = 2 * m + na + nb
    E = list(edges)
    for t, P in enumerate(SA):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(SB):
        b = 2 * m + na + t
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
        m, edges, point_lines, line_points, index, pts = _pg_data(q)

        SA = _greedy_side(m, s, point_lines, rng, 40, deadline)
        SB = _greedy_side(m, s, line_points, rng, 40, deadline)
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if len(cs) > len(SA) and _loads_ok(cs, s, m, point_lines):
                SA = cs
            if len(cs) > len(SB) and _loads_ok(cs, s, m, line_points):
                SB = cs

        if not (_loads_ok(SA, s, m, point_lines) and _loads_ok(SB, s, m, line_points)):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, SA, SB))
    return out


# ----------------------------------------------------------------------------
# Driver. Time plan:
#   0.00-0.08  arc-extended PG graphs (A and B sets chosen independently)
#   0.08-0.80  C bad-pair annealing, growing the best valid graph by one vertex per stage
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()

    def elapsed():
        return time.monotonic() - start

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(g):
        nonlocal best, best_n
        if g is None:
            return
        n, e = g
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        arcs = _arc_extensions(d, start + 0.08 * time_limit,
                               random.Random(seed * 7919 + d))
        for g in sorted(arcs, key=lambda t: -t[0]):
            consider(g)
        grow = 0.80 * time_limit - elapsed() - 2.5
        if grow >= 1.0:
            consider(_c_grow(best, d, D, seed, grow))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
