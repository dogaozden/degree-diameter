import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing on a whole bipartite graph, with growth.
#
# The state is a bipartite graph with max degree d. Colours are fixed by a BFS
# 2-colouring of the input and never change. Cost = number of ordered vertex
# pairs at distance > D (computed with bitset balls). Moves are:
#   add    : join two spare-degree vertices of opposite colour,
#   remove : delete an edge (frees degree),
#   swap   : degree-preserving double-edge swap (a-b, c-e -> a-e, c-b).
# Whenever cost reaches 0 the graph is a valid answer; it is snapshotted and a
# new isolated vertex is added on the smaller colour class, then annealing
# continues. The last snapshot is printed.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>

#define MAXN 512
#define MAXD 64
#define MAXW (MAXN / 64)

static int n, d, D, W;
static int deg[MAXN];
static int adj[MAXN][MAXD];
static int col[MAXN];
static uint64_t reach[MAXN][MAXW];
static uint64_t nxt[MAXN][MAXW];
static uint64_t rs = 88172645463325252ULL;

static int sn = 0;
static int sdeg[MAXN];
static int sadj[MAXN][MAXD];

static uint32_t rnd32(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return (uint32_t)(rs >> 16);
}

static double rndu(void) {
    return (double)(rnd32() & 0xFFFFFFu) / 16777216.0;
}

static int rndi(int k) {
    return (int)(rnd32() % (uint32_t)k);
}

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int u, int v) {
    for (int i = 0; i < deg[u]; i++) if (adj[u][i] == v) return 1;
    return 0;
}

static void add_edge(int u, int v) {
    adj[u][deg[u]++] = v;
    adj[v][deg[v]++] = u;
}

static void rem_one(int u, int v) {
    for (int i = 0; i < deg[u]; i++) {
        if (adj[u][i] == v) {
            adj[u][i] = adj[u][--deg[u]];
            return;
        }
    }
}

static void del_edge(int u, int v) {
    rem_one(u, v);
    rem_one(v, u);
}

/* Number of ordered pairs (x, y), x != y, with dist(x, y) > D. */
static long eval_cost(void) {
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
        for (int w = 0; w < W; w++) c += pc64(reach[v][w]);
        bad += n - c;
    }
    return bad;
}

static void save_best(void) {
    sn = n;
    for (int v = 0; v < n; v++) {
        sdeg[v] = deg[v];
        for (int i = 0; i < deg[v]; i++) sadj[v][i] = adj[v][i];
    }
}

static int grow(void) {
    if (n >= MAXN) return 0;
    int ca = 0;
    for (int v = 0; v < n; v++) if (col[v] == 0) ca++;
    int side = (ca <= n - ca) ? 0 : 1;
    col[n] = side;
    deg[n] = 0;
    n++;
    return 1;
}

static int accept(long delta, double T) {
    if (delta <= 0) return 1;
    return rndu() < exp(-(double)delta / T);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) rnd32();

    if (d < 1 || d > MAXD || D < 2) { printf("0 0\n"); return 0; }

    int N0, M0;
    if (scanf("%d %d", &N0, &M0) != 2) { printf("0 0\n"); return 0; }
    if (N0 < 1 || N0 >= MAXN) { printf("0 0\n"); return 0; }
    n = N0;
    for (int i = 0; i < n; i++) deg[i] = 0;
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
    for (int u = 0; u < n; u++)
        for (int i = 0; i < deg[u]; i++)
            if (col[adj[u][i]] == col[u]) { printf("0 0\n"); return 0; }

    const double THI = 2.0;
    const double TLO = 0.25;
    const long PER = 40000;

    clock_t t0 = clock();
    long cost = eval_cost();
    long it = 0;

    while (1) {
        if ((it & 63) == 0) {
            if ((double)(clock() - t0) / CLOCKS_PER_SEC > budget) break;
        }
        it++;

        if (cost == 0) {
            save_best();
            if (!grow()) break;
            cost = eval_cost();
            continue;
        }

        double ph = (double)(it % PER) / (double)PER;
        double T = TLO * pow(THI / TLO, 1.0 - ph);
        int mv = rndi(100);

        if (mv < 30) {
            int u = rndi(n), v = rndi(n);
            if (col[u] == col[v] || deg[u] >= d || deg[v] >= d || has_edge(u, v)) continue;
            add_edge(u, v);
            long c2 = eval_cost();
            if (accept(c2 - cost, T)) cost = c2;
            else del_edge(u, v);
        } else if (mv < 40) {
            int u = rndi(n);
            if (deg[u] == 0) continue;
            int v = adj[u][rndi(deg[u])];
            del_edge(u, v);
            long c2 = eval_cost();
            if (accept(c2 - cost, T)) cost = c2;
            else add_edge(u, v);
        } else {
            int a = rndi(n);
            if (deg[a] == 0) continue;
            int b = adj[a][rndi(deg[a])];
            int c = rndi(n);
            if (deg[c] == 0) continue;
            int e = adj[c][rndi(deg[c])];
            if (col[a] != col[c] || a == c || b == e) continue;
            if (has_edge(a, e) || has_edge(c, b)) continue;
            del_edge(a, b);
            del_edge(c, e);
            add_edge(a, e);
            add_edge(c, b);
            long c2 = eval_cost();
            if (accept(c2 - cost, T)) cost = c2;
            else {
                del_edge(a, e);
                del_edge(c, b);
                add_edge(a, b);
                add_edge(c, e);
            }
        }
    }

    if (sn == 0) { printf("0 0\n"); return 0; }
    long m2 = 0;
    for (int u = 0; u < sn; u++)
        for (int i = 0; i < sdeg[u]; i++)
            if (sadj[u][i] > u) m2++;
    printf("%d %ld\n", sn, m2);
    for (int u = 0; u < sn; u++)
        for (int i = 0; i < sdeg[u]; i++)
            if (sadj[u][i] > u) printf("%d %d\n", u, sadj[u][i]);
    return 0;
}
"""


def _c_grow(graph, d, D, seed, budget):
    """Run the C annealing/growth engine from graph; return (n, edges) or None on any failure."""
    if graph is None or budget < 1.0 or d > 64:
        return None
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                        stdin_graph=(graph[0], graph[1]), timeout=budget + 8.0)
        n2, e2 = lib.parse_graph_text(out)
    except Exception:
        return None
    if n2 < 1:
        return None
    return n2, e2


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3). Start point.
#
# Start from PG(2, q) incidence (points 0..m-1, lines m..2m-1), degree q+1,
# spare s = d - q - 1. New A-vertices attach to lines through chosen points
# (each line loaded at most s times); new B-vertices attach to points on
# chosen lines (each point loaded at most s times).
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
    """True if every target is hit by at most s elements of S."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomized greedy choice so that every target is hit at most s times."""
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
    """Conic (plus nucleus for even q): an arc with no three collinear points."""
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
# Generalized quadrangle baseline (D = 4).
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Driver. Time plan (fractions of time_limit):
#   0.00-0.10  arc-extended PG graphs (and GQ start for D >= 4)
#   0.10-0.80  C annealing with growth, starting from the best graph so far
# The output is always validated; K_{d,d} is the final fallback.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def elapsed():
        return time.monotonic() - start

    def consider(g):
        nonlocal best
        if g is None:
            return
        n, e = g
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        for g in _arc_extensions(d, start + 0.10 * time_limit,
                                 random.Random(seed * 7919 + d)):
            consider(g)

    if D >= 4 and elapsed() < 0.20 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq)

    if D >= 3:
        budget = 0.80 * time_limit - elapsed() - 2.0
        if budget > 1.0:
            consider(_c_grow(best, d, D, seed, budget))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
