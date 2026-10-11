import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: penalty annealing over fixed-size graphs, growing one vertex at a time.
#
# State: a bipartite graph with max degree d. Cost = number of ordered vertex
# pairs at distance > D (unreachable counts too). Moves: join a random
# non-adjacent cross pair (u, v); if u or v is saturated, first delete one of its
# random edges (the displaced neighbour is remembered for undo). Metropolis
# acceptance on cost, with periodic temperature resets. Whenever cost hits 0 the
# current graph is valid and is snapshotted, then a fresh isolated vertex is
# added and the search continues. The best snapshot is printed.
# This is a structure-free local search, unlike greedy ball-cover insertion.
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
#define MAXE (MAXN * MAXD / 2)

static int n, d, D, W;
static int deg[MAXN];
static int adj[MAXN][MAXD];
static int col[MAXN];
static uint64_t reach[MAXN][MAXW];
static uint64_t nxt[MAXN][MAXW];
static uint64_t rs = 88172645463325252ULL;

static uint32_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return (uint32_t)(rs >> 16);
}

static double rnd01(void) {
    return (double)(rnd() & 0xFFFFFFu) / 16777216.0;
}

static int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int u, int v) {
    for (int i = 0; i < deg[u]; i++) if (adj[u][i] == v) return 1;
    return 0;
}

static void del_one(int u, int v) {
    for (int i = 0; i < deg[u]; i++) {
        if (adj[u][i] == v) {
            adj[u][i] = adj[u][deg[u] - 1];
            deg[u]--;
            return;
        }
    }
}

static void add_edge(int u, int v) {
    adj[u][deg[u]++] = v;
    adj[v][deg[v]++] = u;
}

static void del_edge(int u, int v) {
    del_one(u, v);
    del_one(v, u);
}

/* Number of ordered pairs (x, y) with dist(x, y) > D. */
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
    long c = 0;
    for (int v = 0; v < n; v++) {
        int cnt = 0;
        for (int w = 0; w < W; w++) cnt += popc64(reach[v][w]);
        c += n - cnt;
    }
    return c;
}

static int bn, bm;
static int bu[MAXE], bv[MAXE];

static void snapshot(void) {
    bn = n;
    bm = 0;
    for (int u = 0; u < n; u++)
        for (int i = 0; i < deg[u]; i++) {
            int v = adj[u][i];
            if (v > u && bm < MAXE) {
                bu[bm] = u;
                bv[bm] = v;
                bm++;
            }
        }
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
    if (N0 < 1 || N0 > MAXN - 2) { printf("0 0\n"); return 0; }
    n = N0;
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
            int x = queue[qh++];
            for (int i = 0; i < deg[x]; i++) {
                int y = adj[x][i];
                if (col[y] < 0) {
                    col[y] = 1 - col[x];
                    queue[qt++] = y;
                }
            }
        }
    }

    snapshot();  /* the input graph is the fallback answer */

    const double T0 = 1.6, Tmin = 0.25;
    const long CYC = 40000;
    const double kdec = log(T0 / Tmin) / (double)CYC;

    clock_t t0 = clock();
    long c = eval_cost();
    if (c == 0 && n < MAXN - 1) {
        snapshot();
        col[n] = (int)(rnd() & 1u);
        deg[n] = 0;
        n++;
        c = eval_cost();
    }

    long it = 0;
    while (1) {
        if ((it & 127) == 0 &&
            (double)(clock() - t0) / CLOCKS_PER_SEC > budget) break;
        it++;

        int u = (rnd() % 3 == 0) ? (n - 1) : (int)(rnd() % (uint32_t)n);
        int v = (int)(rnd() % (uint32_t)n);
        if (u == v || col[u] == col[v] || has_edge(u, v)) continue;

        int ru = -1, rv = -1;
        if (deg[u] >= d) {
            ru = adj[u][rnd() % (uint32_t)deg[u]];
            del_edge(u, ru);
        }
        if (deg[v] >= d) {
            rv = adj[v][rnd() % (uint32_t)deg[v]];
            del_edge(v, rv);
        }
        add_edge(u, v);

        double T = T0 * exp(-kdec * (double)(it % CYC));
        long c2 = eval_cost();
        int acc = 0;
        if (c2 <= c) acc = 1;
        else if (rnd01() < exp(-(double)(c2 - c) / T)) acc = 1;

        if (acc) {
            c = c2;
        } else {
            del_edge(u, v);
            if (ru >= 0) add_edge(u, ru);
            if (rv >= 0) add_edge(v, rv);
        }

        if (c == 0) {
            snapshot();
            if (n >= MAXN - 1) break;
            col[n] = (int)(rnd() & 1u);
            deg[n] = 0;
            n++;
            c = eval_cost();
        }
    }

    printf("%d %d\n", bn, bm);
    for (int i = 0; i < bm; i++) printf("%d %d\n", bu[i], bv[i]);
    return 0;
}
"""


def _c_anneal(graph, d, D, seed, budget):
    """Run the C penalty annealer on a valid graph; return (n, edges) or None on failure."""
    if graph is None or budget < 0.5 or d > 64:
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
# Projective-plane base graphs (diameter 3): PG(2, q) incidence plus arc
# extensions. Each new A-vertex joins a full pencil of lines through a chosen
# point; each new B-vertex joins the points of a chosen line. Spare degree
# limits how many such vertices each old vertex can absorb.
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
    """Randomized greedy choice of elements so that every target is hit at most s times."""
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
# Generalized quadrangle W(q) incidence graph (diameter 4), used for D >= 4.
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
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Driver.
#   0.00-0.10  base graph: arc-extended PG graphs (D = 3) or W(q) (D >= 4)
#   0.10-0.84  C penalty annealing with vertex growth, starting from the base
#   end        validate; fall back to K_{d,d} if anything is wrong
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    fallback = lib.haar_graph(d, range(d))
    best = fallback

    def elapsed():
        return time.monotonic() - start

    def consider(g):
        nonlocal best
        if g is None:
            return
        n, e = g
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    try:
        if D == 3:
            arcs = _arc_extensions(d, start + 0.10 * time_limit,
                                   random.Random(seed * 7919 + d))
            for g in arcs:
                consider(g)
        if D >= 4 and elapsed() < 0.10 * time_limit:
            consider(_best_gq(d))
    except Exception:
        pass

    # Already at the Moore bound (e.g. PG(2, d-1) when d-1 is a prime power): done.
    if best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.84 * time_limit - elapsed()
    if budget > 1.0:
        try:
            consider(_c_anneal(best, d, D, seed, budget))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
