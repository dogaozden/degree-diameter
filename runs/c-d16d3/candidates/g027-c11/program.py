import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bipartite annealing growth with a bitset distance cost.
#
# State: a bipartite graph (sides 0/1) with max degree d. Cost = number of ordered
# vertex pairs at distance > D, computed with D rounds of bitset OR. Moves keep
# bipartiteness and the degree bound: add an edge, transfer an endpoint to another
# spare vertex, 2-switch, or (rarely) remove an edge. A vertex is added only after
# the current graph is valid; the engine keeps the last valid snapshot and restores
# it when an attempt fails.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1024
#define MAXD 64
#define MAXW 16
#define MAXLOG 16
#define ATTEMPT_ITERS 40000

static int N, DD, DIST;
static int side[MAXN];
static int deg[MAXN];
static int adj[MAXN][MAXD];
static unsigned char adjm[MAXN][MAXN];
static uint64_t RA[MAXN][MAXW], RB[MAXN][MAXW];

static int sN;
static int sSide[MAXN], sDeg[MAXN];
static int sAdj[MAXN][MAXD];
static unsigned char sAdjm[MAXN][MAXN];

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rint_(int n) { return (int)(rnd() % (uint64_t)n); }

static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void add_edge(int u, int v) {
    adj[u][deg[u]++] = v;
    adj[v][deg[v]++] = u;
    adjm[u][v] = 1;
    adjm[v][u] = 1;
}

static void remove_edge(int u, int v) {
    for (int k = 0; k < deg[u]; k++)
        if (adj[u][k] == v) { adj[u][k] = adj[u][--deg[u]]; break; }
    for (int k = 0; k < deg[v]; k++)
        if (adj[v][k] == u) { adj[v][k] = adj[v][--deg[v]]; break; }
    adjm[u][v] = 0;
    adjm[v][u] = 0;
}

static long long eval_cost(void) {
    int W = (N + 63) >> 6;
    uint64_t (*cur)[MAXW] = RA;
    uint64_t (*nxt)[MAXW] = RB;
    for (int v = 0; v < N; v++) {
        for (int w = 0; w < W; w++) cur[v][w] = 0;
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < DIST; r++) {
        for (int v = 0; v < N; v++) {
            for (int w = 0; w < W; w++) nxt[v][w] = cur[v][w];
            for (int k = 0; k < deg[v]; k++) {
                const uint64_t *src = cur[adj[v][k]];
                for (int w = 0; w < W; w++) nxt[v][w] |= src[w];
            }
        }
        uint64_t (*t)[MAXW] = cur;
        cur = nxt;
        nxt = t;
    }
    long long cost = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(cur[v][w]);
        cost += N - c;
    }
    return cost;
}

typedef struct { int type, u, v; } Op;
static Op lg[MAXLOG];
static int nlg = 0;

static void op_add(int u, int v) {
    add_edge(u, v);
    lg[nlg].type = 0; lg[nlg].u = u; lg[nlg].v = v; nlg++;
}

static void op_rem(int u, int v) {
    remove_edge(u, v);
    lg[nlg].type = 1; lg[nlg].u = u; lg[nlg].v = v; nlg++;
}

static void undo_all(void) {
    while (nlg > 0) {
        nlg--;
        if (lg[nlg].type == 0) remove_edge(lg[nlg].u, lg[nlg].v);
        else add_edge(lg[nlg].u, lg[nlg].v);
    }
}

static int spA[MAXN], spB[MAXN], nspA, nspB;

static void build_spare(void) {
    nspA = nspB = 0;
    for (int v = 0; v < N; v++) {
        if (deg[v] < DD) {
            if (side[v] == 0) spA[nspA++] = v;
            else spB[nspB++] = v;
        }
    }
}

static int pick_side_nonzero(int s) {
    for (int t = 0; t < 64; t++) {
        int v = rint_(N);
        if (side[v] == s && deg[v] > 0) return v;
    }
    return -1;
}

static int pick_any(void) {
    for (int t = 0; t < 64; t++) {
        int v = rint_(N);
        if (deg[v] > 0) return v;
    }
    return -1;
}

static int move_add(void) {
    build_spare();
    if (nspA == 0 || nspB == 0) return 0;
    for (int t = 0; t < 40; t++) {
        int a = spA[rint_(nspA)];
        int b = spB[rint_(nspB)];
        if (!adjm[a][b]) { op_add(a, b); return 1; }
    }
    return 0;
}

static int move_transfer(void) {
    int u = pick_any();
    if (u < 0) return 0;
    build_spare();
    int v = adj[u][rint_(deg[u])];
    if (side[u] == 0) {
        if (nspA == 0) return 0;
        for (int t = 0; t < 20; t++) {
            int a = spA[rint_(nspA)];
            if (a != u && !adjm[a][v]) { op_rem(u, v); op_add(a, v); return 1; }
        }
    } else {
        if (nspB == 0) return 0;
        for (int t = 0; t < 20; t++) {
            int b = spB[rint_(nspB)];
            if (b != u && !adjm[v][b]) { op_rem(u, v); op_add(v, b); return 1; }
        }
    }
    return 0;
}

static int move_switch(void) {
    int u = pick_side_nonzero(0);
    if (u < 0) return 0;
    int a = pick_side_nonzero(0);
    if (a < 0 || a == u) return 0;
    int v = adj[u][rint_(deg[u])];
    int b = adj[a][rint_(deg[a])];
    if (v == b) return 0;
    if (adjm[u][b] || adjm[a][v]) return 0;
    op_rem(u, v);
    op_rem(a, b);
    op_add(u, b);
    op_add(a, v);
    return 1;
}

static int move_remove(void) {
    int u = pick_any();
    if (u < 0) return 0;
    int v = adj[u][rint_(deg[u])];
    op_rem(u, v);
    return 1;
}

static long long anneal(long long iters, double T0, double T1, long long cost, double deadline) {
    for (long long it = 0; it < iters && cost != 0; it++) {
        if ((it & 63) == 0 && now() > deadline) break;
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        double p = rdbl();
        int ok;
        nlg = 0;
        if (p < 0.20) ok = move_add();
        else if (p < 0.45) ok = move_transfer();
        else if (p < 0.90) ok = move_switch();
        else ok = move_remove();
        if (!ok) { nlg = 0; continue; }
        long long c2 = eval_cost();
        long long delta = c2 - cost;
        if (delta <= 0 || rdbl() < exp(-(double)delta / T)) cost = c2;
        else undo_all();
        nlg = 0;
    }
    return cost;
}

static void add_vertex(int s) {
    int x = N;
    for (int j = 0; j < N; j++) { adjm[x][j] = 0; adjm[j][x] = 0; }
    adjm[x][x] = 0;
    side[x] = s;
    deg[x] = 0;
    N++;
}

static void save_snap(void) {
    sN = N;
    memcpy(sSide, side, sizeof(side));
    memcpy(sDeg, deg, sizeof(deg));
    memcpy(sAdj, adj, sizeof(adj));
    memcpy(sAdjm, adjm, sizeof(adjm));
}

static void restore_snap(void) {
    N = sN;
    memcpy(side, sSide, sizeof(side));
    memcpy(deg, sDeg, sizeof(deg));
    memcpy(adj, sAdj, sizeof(adj));
    memcpy(adjm, sAdjm, sizeof(adjm));
}

static void print_snap(void) {
    long long m = 0;
    for (int v = 0; v < sN; v++) m += sDeg[v];
    m /= 2;
    printf("%d %lld\n", sN, m);
    for (int u = 0; u < sN; u++)
        for (int k = 0; k < sDeg[u]; k++)
            if (sAdj[u][k] > u) printf("%d %d\n", u, sAdj[u][k]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    double deadline = now() + budget;
    rs ^= (seed + 1ULL) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) rnd();
    if (d < 1 || d > MAXD || D < 1) { printf("0 0\n"); return 0; }
    DD = d;
    DIST = D;

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { printf("0 0\n"); return 0; }
    if (n0 == 0) {
        if (2 * d > MAXN - 64) { printf("0 0\n"); return 0; }
        N = 2 * d;
        for (int v = 0; v < N; v++) { side[v] = (v >= d); deg[v] = 0; }
        for (int i = 0; i < d; i++)
            for (int j = 0; j < d; j++) add_edge(i, d + j);
    } else {
        if (n0 < 1 || n0 > MAXN - 64 || m0 < 0) { printf("0 0\n"); return 0; }
        N = n0;
        for (int v = 0; v < N; v++) {
            deg[v] = 0;
            side[v] = 0;
            for (int w = 0; w < N; w++) adjm[v][w] = 0;
        }
        for (int i = 0; i < m0; i++) {
            int u, v;
            if (scanf("%d %d", &u, &v) != 2) { printf("0 0\n"); return 0; }
            if (u < 0 || v < 0 || u >= N || v >= N || u == v || adjm[u][v] ||
                deg[u] >= d || deg[v] >= d) {
                printf("0 0\n");
                return 0;
            }
            add_edge(u, v);
        }
        int col[MAXN], q[MAXN];
        for (int v = 0; v < N; v++) col[v] = -1;
        for (int s = 0; s < N; s++) {
            if (col[s] >= 0) continue;
            col[s] = 0;
            int qh = 0, qt = 0;
            q[qt++] = s;
            while (qh < qt) {
                int x = q[qh++];
                for (int k = 0; k < deg[x]; k++) {
                    int y = adj[x][k];
                    if (col[y] < 0) { col[y] = 1 - col[x]; q[qt++] = y; }
                    else if (col[y] == col[x]) { printf("0 0\n"); return 0; }
                }
            }
        }
        for (int v = 0; v < N; v++) side[v] = col[v];
    }

    long long cost = eval_cost();
    while (cost != 0 && now() < deadline)
        cost = anneal(40000, 1.5, 0.2, cost, deadline);
    if (cost != 0) { printf("0 0\n"); return 0; }

    save_snap();
    while (now() < deadline && N < MAXN - 2) {
        add_vertex((int)(rnd() & 1ULL));
        cost = eval_cost();
        cost = anneal(ATTEMPT_ITERS, 2.0, 0.15, cost, deadline);
        if (cost == 0) save_snap();
        else restore_snap();
    }
    print_snap();
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q). Each old vertex has degree q+1, so
# with d >= q+1 it has spare s = d - q - 1. New A-vertices attach to all lines
# through a chosen point (each line hit by <= s chosen points); new B-vertices
# attach to all points on a chosen line (each point hit by <= s chosen lines).
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
    """True if every target is hit by <= s elements of S."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomized greedy choice of elements so that every target is hit by <= s chosen elements."""
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
    """Return a list of (n, edges) arc-extended candidates for each prime power q with q + 1 <= d."""
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
# Generalized quadrangle W(q) incidence graph (diameter 4).
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
# build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(cand):
        nonlocal best, best_n
        try:
            n, e = cand
            if n > best_n and lib.is_valid(n, e, d, D):
                best, best_n = (n, e), n
        except Exception:
            pass

    # Algebraic constructions (diameter 3 for arc graphs, 4 for W(q)).
    if D >= 3:
        for cand in _arc_extensions(d, t0 + 0.25 * time_limit, random.Random(seed * 7919 + d)):
            consider(cand)
        if d >= 5 and lib.is_prime_power(d - 2):
            try:
                consider(lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass
    if D == 4 and time.monotonic() - t0 < 0.4 * time_limit:
        g = _best_gq(d)
        if g is not None:
            consider(g)

    # Native search: grow the best valid graph in C. Skipped when the Moore bound is met.
    remaining = time_limit - (time.monotonic() - t0)
    if best_n < lib.moore_bound(d, D) and remaining > 8:
        budget = 0.9 * remaining - 3.0
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                            stdin_graph=best, timeout=remaining - 3.0)
            consider(lib.parse_graph_text(out))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
