import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q) (points 0..m-1, lines m..2m-1).
# Every old vertex has degree q+1, so with d >= q+1 it has spare s = d - q - 1.
#
# A-side: a set SA of points. Each SA point P gets a new vertex joined to all
#         q+1 lines through P. Constraint: every line holds <= s points of SA.
# B-side: a set SB of lines. Each j in SB gets a new vertex joined to all
#         q+1 points on j. Constraint: every point lies on <= s lines of SB.
#
# Diameter stays 3 for any SA, SB, so the two sides are maximized separately.
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
    """True if every target t is hit by <= s elements of S, where element x hits nbr[x]."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomized greedy: choose elements x so that every target is hit by <= s chosen elements."""
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
    """Yield (n, edges) candidates for each prime power q with q + 1 <= d."""
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
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# C engine: vertex insertion with repair annealing.
#
# State: a bipartite graph with max degree DEG. Cost = number of unordered
# vertex pairs at distance > DIAM (computed exactly with bitset balls).
# Loop: add one new vertex (random side, greedily attached to spare-degree
# opposite-side vertices), then anneal edge add / delete / rewire moves until
# cost 0. On success the graph is snapshotted and grows by one vertex; on
# failure it is restored from the snapshot and retried with a longer budget.
# Every saved snapshot has cost 0, so it is valid by construction.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1200
#define WMAX ((MAXN + 63) / 64)
#define MAXDEG 96
#define MAXE 60000

static int N, DEG, DIAM;
static int side[MAXN];
static int deg[MAXN];
static int nbr[MAXN][MAXDEG];
static unsigned char adj[MAXN][MAXN];
static uint64_t BA[MAXN][WMAX], BB[MAXN][WMAX];

static int SU[MAXE], SV[MAXE], SM, SN;
static int NEWV = -1;

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double now_sec(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Number of unordered pairs at distance > DIAM (unreachable counts as bad). */
static long bad_pairs(void) {
    int W = (N + 63) / 64;
    uint64_t (*cur)[WMAX] = BA, (*nx)[WMAX] = BB;
    for (int v = 0; v < N; v++) {
        memset(cur[v], 0, sizeof(uint64_t) * WMAX);
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int s = 0; s < DIAM; s++) {
        for (int v = 0; v < N; v++) {
            memcpy(nx[v], cur[v], sizeof(uint64_t) * (size_t)W);
            for (int i = 0; i < deg[v]; i++) {
                uint64_t *src = cur[nbr[v][i]];
                for (int w = 0; w < W; w++) nx[v][w] |= src[w];
            }
        }
        uint64_t (*t)[WMAX] = cur;
        cur = nx;
        nx = t;
    }
    long bad = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(cur[v][w]);
        bad += N - c;
    }
    return bad / 2;
}

static void add_edge(int u, int v) {
    adj[u][v] = adj[v][u] = 1;
    nbr[u][deg[u]++] = v;
    nbr[v][deg[v]++] = u;
}

static void remove_from(int u, int v) {
    for (int i = 0; i < deg[u]; i++) {
        if (nbr[u][i] == v) {
            nbr[u][i] = nbr[u][--deg[u]];
            return;
        }
    }
}

static void del_edge(int u, int v) {
    adj[u][v] = adj[v][u] = 0;
    remove_from(u, v);
    remove_from(v, u);
}

static void save_state(void) {
    SM = 0;
    SN = N;
    for (int v = 0; v < N; v++)
        for (int i = 0; i < deg[v]; i++)
            if (nbr[v][i] > v && SM < MAXE) {
                SU[SM] = v;
                SV[SM] = nbr[v][i];
                SM++;
            }
}

static void restore_state(void) {
    for (int v = 0; v < N; v++) {
        memset(adj[v], 0, (size_t)N);
        deg[v] = 0;
    }
    N = SN;
    for (int i = 0; i < SM; i++) add_edge(SU[i], SV[i]);
}

/* Metropolis annealing at fixed N over add / delete / rewire moves. Returns final cost. */
static long anneal(long iters, double T0, double T1, double deadline) {
    long cost = bad_pairs();
    for (long it = 0; it < iters && cost > 0; it++) {
        if ((it & 31) == 0 && now_sec() > deadline) break;
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        int mv = rndint(100);
        if (mv < 40) {
            int u = (NEWV >= 0 && rnd01() < 0.5) ? NEWV : rndint(N);
            int w = rndint(N);
            if (u == w || side[u] == side[w] || adj[u][w] || deg[u] >= DEG || deg[w] >= DEG)
                continue;
            add_edge(u, w);
            long c2 = bad_pairs();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) cost = c2;
            else del_edge(u, w);
        } else if (mv < 55) {
            int u = rndint(N);
            if (deg[u] == 0) continue;
            int w = nbr[u][rndint(deg[u])];
            del_edge(u, w);
            long c2 = bad_pairs();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) cost = c2;
            else add_edge(u, w);
        } else {
            int u = rndint(N);
            if (deg[u] == 0) continue;
            int w = nbr[u][rndint(deg[u])];
            int w2 = rndint(N);
            if (w2 == w || side[w2] != side[w] || adj[u][w2] || deg[w2] >= DEG) continue;
            del_edge(u, w);
            add_edge(u, w2);
            long c2 = bad_pairs();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) cost = c2;
            else {
                del_edge(u, w2);
                add_edge(u, w);
            }
        }
    }
    return cost;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    double budget = atof(argv[4]);
    double deadline = now_sec() + budget;

    if (DEG < 1 || DEG > MAXDEG - 1 || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }

    int n0, m0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 < 1 || n0 > MAXN - 300 || m0 < 0 || m0 > MAXE) {
        printf("0 0\n");
        return 0;
    }
    N = n0;
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= N || v >= N || u == v ||
            adj[u][v] || deg[u] >= DEG || deg[v] >= DEG) {
            printf("0 0\n");
            return 0;
        }
        add_edge(u, v);
    }

    /* Bipartition by BFS; a conflict means the input is not bipartite. */
    static int col[MAXN], queue[MAXN];
    for (int v = 0; v < N; v++) col[v] = -1;
    for (int s = 0; s < N; s++) {
        if (col[s] >= 0) continue;
        int qh = 0, qt = 0;
        col[s] = 0;
        queue[qt++] = s;
        while (qh < qt) {
            int u = queue[qh++];
            for (int i = 0; i < deg[u]; i++) {
                int w = nbr[u][i];
                if (col[w] < 0) {
                    col[w] = 1 - col[u];
                    queue[qt++] = w;
                } else if (col[w] == col[u]) {
                    printf("0 0\n");
                    return 0;
                }
            }
        }
    }
    for (int v = 0; v < N; v++) side[v] = col[v];

    if (bad_pairs() > 0) {
        if (anneal(200000, 1.0, 0.05, deadline) > 0) {
            printf("0 0\n");
            return 0;
        }
    }
    save_state();

    int fails = 0;
    while (N < MAXN - 1 && now_sec() < deadline) {
        int x = N;
        side[x] = rndint(2);
        N = x + 1;
        deg[x] = 0;
        for (int v = 0; v < x; v++) adj[v][x] = adj[x][v] = 0;
        /* Greedy attach to random spare-degree vertices on the other side. */
        for (int t = 0; t < 8 * x && deg[x] < DEG; t++) {
            int w = rndint(x);
            if (side[w] != side[x] && deg[w] < DEG && !adj[x][w]) add_edge(x, w);
        }
        NEWV = x;
        long iters = 4000 + 200L * (fails < 20 ? fails : 20);
        long c = anneal(iters, 2.0, 0.05, deadline);
        NEWV = -1;
        if (c == 0) {
            save_state();
            fails = 0;
        } else {
            restore_state();
            fails++;
        }
    }

    printf("%d %d\n", SN, SM);
    for (int i = 0; i < SM; i++) printf("%d %d\n", SU[i], SV[i]);
    return 0;
}
"""


def _c_improve(graph, d, D, seed, budget, timeout):
    """Run the C insertion engine on graph; return a validated (n, edges) or None."""
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                        stdin_graph=graph, timeout=timeout)
        n2, e2 = lib.parse_graph_text(out)
    except (RuntimeError, ValueError, OSError):
        return None
    if lib.is_valid(n2, e2, d, D):
        return n2, e2
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()

    def elapsed():
        return time.monotonic() - t0

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    rng = random.Random(seed * 7919 + d)
    if D >= 3:
        for n_c, e_c in _arc_extensions(d, t0 + 0.25 * time_limit, rng):
            consider(n_c, e_c)
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Stop early if the start already meets the Moore bound.
    if best_n >= lib.moore_bound(d, D):
        return best

    # C insertion-and-repair search from the best start graph.
    hard = 0.9 * time_limit - elapsed()
    budget = min(0.75 * time_limit - elapsed(), hard - 1.5)
    if budget >= 1.0:
        res = _c_improve(best, d, D, seed, budget, hard)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
