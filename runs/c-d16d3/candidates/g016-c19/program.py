import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Strategy (bold change from parent)
#
# The parent only used algebraic arc extensions of PG(2,q) and voltage-lift
# annealing. This version keeps the arc extensions and the W(q) baseline as
# safe starting points, then hands the best graph to a C engine that grows it
# by LOCAL SEARCH on the graph itself:
#
#   * add one vertex on a random side, joined to up to d spare-capacity
#     vertices of the other side;
#   * simulated annealing over edge moves (add an edge, rewire an edge
#     endpoint, delete an edge), with cost = number of vertex pairs at
#     distance > D (computed with bitset ball expansion);
#   * if cost reaches 0 the graph is valid and larger, so keep it and grow
#     again; otherwise roll back to the last valid graph.
#
# Bipartiteness and degree bounds hold by construction. Python re-checks the
# output with lib.is_valid and falls back to the best valid graph otherwise.
# ----------------------------------------------------------------------------


C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1024
#define MAXD 64
#define MAXW (MAXN / 64)
#define ITERS 15000

typedef struct {
    int n;
    int deg[MAXN];
    int col[MAXN];
    int nb[MAXN][MAXD];
    unsigned char am[MAXN][MAXN];
} Graph;

static Graph cur, best_g;
static int DEGMAX = 1, RADIUS = 1;
static double BUDGET = 1.0;
static clock_t T_START;
static uint64_t rs = 88172645463325252ULL;
static uint64_t BUF1[MAXN][MAXW], BUF2[MAXN][MAXW];

static uint64_t rnd64(void) {
    rs ^= rs >> 12;
    rs ^= rs << 25;
    rs ^= rs >> 27;
    return rs * 2685821657736338717ULL;
}

static int rndint(int k) {
    return (int)(rnd64() % (uint64_t)k);
}

static double rnd01(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}

static double elapsed(void) {
    return (double)(clock() - T_START) / (double)CLOCKS_PER_SEC;
}

static int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void add_edge(Graph *g, int u, int v) {
    g->am[u][v] = 1;
    g->am[v][u] = 1;
    g->nb[u][g->deg[u]++] = v;
    g->nb[v][g->deg[v]++] = u;
}

static void del_one(Graph *g, int u, int v) {
    int i;
    for (i = 0; i < g->deg[u]; i++) {
        if (g->nb[u][i] == v) {
            g->nb[u][i] = g->nb[u][g->deg[u] - 1];
            g->deg[u]--;
            return;
        }
    }
}

static void remove_edge(Graph *g, int u, int v) {
    g->am[u][v] = 0;
    g->am[v][u] = 0;
    del_one(g, u, v);
    del_one(g, v, u);
}

/* Number of unordered vertex pairs at distance > RADIUS (unreachable counts). */
static long long bad_pairs(const Graph *g) {
    int n = g->n;
    int W = (n + 63) >> 6;
    int v, k, w, r;
    uint64_t (*P)[MAXW] = BUF1;
    uint64_t (*Q)[MAXW] = BUF2;
    uint64_t (*tmp)[MAXW];
    long long bad = 0;

    for (v = 0; v < n; v++) {
        for (w = 0; w < W; w++) P[v][w] = 0;
        P[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (r = 0; r < RADIUS; r++) {
        for (v = 0; v < n; v++) {
            for (w = 0; w < W; w++) Q[v][w] = P[v][w];
            for (k = 0; k < g->deg[v]; k++) {
                int u = g->nb[v][k];
                for (w = 0; w < W; w++) Q[v][w] |= P[u][w];
            }
        }
        tmp = P;
        P = Q;
        Q = tmp;
    }
    for (v = 0; v < n; v++) {
        int c = 0;
        for (w = 0; w < W; w++) c += popc64(P[v][w]);
        bad += n - c;
    }
    return bad / 2;
}

/* Two-colour the graph; returns 1 if bipartite. Fills g->col. */
static int bipartite_colour(Graph *g) {
    static int stack[MAXN];
    int s, k;
    for (s = 0; s < g->n; s++) g->col[s] = -1;
    for (s = 0; s < g->n; s++) {
        int sp = 0;
        if (g->col[s] != -1) continue;
        g->col[s] = 0;
        stack[sp++] = s;
        while (sp > 0) {
            int u = stack[--sp];
            for (k = 0; k < g->deg[u]; k++) {
                int v = g->nb[u][k];
                if (g->col[v] == -1) {
                    g->col[v] = 1 - g->col[u];
                    stack[sp++] = v;
                } else if (g->col[v] == g->col[u]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

/* Add a new vertex on a random side, joined to up to DEGMAX spare vertices of the other side. */
static int try_add(Graph *g) {
    static int cand[MAXN];
    int n = g->n, c, v, i, nc = 0, want;
    if (n >= MAXN - 1) return 0;
    c = rndint(2);
    for (i = 0; i < n; i++) {
        if (g->col[i] != c && g->deg[i] < DEGMAX) cand[nc++] = i;
    }
    if (nc == 0) return 0;
    for (i = nc - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = cand[i];
        cand[i] = cand[j];
        cand[j] = t;
    }
    want = nc < DEGMAX ? nc : DEGMAX;
    v = n;
    g->n = n + 1;
    g->deg[v] = 0;
    g->col[v] = c;
    for (i = 0; i < want; i++) add_edge(g, v, cand[i]);
    return 1;
}

/* Simulated annealing over edge moves. Returns final cost (0 means valid). */
static long long anneal(Graph *g, long long iters) {
    long long cost = bad_pairs(g);
    const double T0 = 2.0, T1 = 0.15;
    long long it;
    if (cost == 0) return 0;
    for (it = 0; it < iters && cost > 0; it++) {
        int n = g->n, mv, a, b, x, y, z;
        long long nc;
        double T;
        if ((it & 255) == 0 && elapsed() > BUDGET) break;
        T = T0 * pow(T1 / T0, (double)it / (double)iters);
        mv = rndint(10);
        if (mv < 5) {
            /* add an edge between opposite sides with spare degree */
            a = rndint(n);
            b = rndint(n);
            if (a == b || g->col[a] == g->col[b] || g->am[a][b] ||
                g->deg[a] >= DEGMAX || g->deg[b] >= DEGMAX)
                continue;
            add_edge(g, a, b);
            nc = bad_pairs(g);
            if (nc <= cost || rnd01() < exp(-(double)(nc - cost) / T)) {
                cost = nc;
            } else {
                remove_edge(g, a, b);
            }
        } else if (mv < 9) {
            /* rewire: move one endpoint of edge (x,y) to z on y's side */
            x = rndint(n);
            if (g->deg[x] == 0) continue;
            y = g->nb[x][rndint(g->deg[x])];
            z = rndint(n);
            if (z == y || g->col[z] != g->col[y] || g->am[x][z] || g->deg[z] >= DEGMAX)
                continue;
            remove_edge(g, x, y);
            add_edge(g, x, z);
            nc = bad_pairs(g);
            if (nc <= cost || rnd01() < exp(-(double)(nc - cost) / T)) {
                cost = nc;
            } else {
                remove_edge(g, x, z);
                add_edge(g, x, y);
            }
        } else {
            /* delete an edge */
            x = rndint(n);
            if (g->deg[x] == 0) continue;
            y = g->nb[x][rndint(g->deg[x])];
            remove_edge(g, x, y);
            nc = bad_pairs(g);
            if (nc <= cost || rnd01() < exp(-(double)(nc - cost) / T)) {
                cost = nc;
            } else {
                add_edge(g, x, y);
            }
        }
    }
    return cost;
}

int main(int argc, char **argv) {
    int d, D, n = 0, m = 0, i, ok = 1;
    unsigned long seed;
    double tb;
    int fails = 0;
    long long c0;

    T_START = clock();
    if (argc < 5) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    seed = strtoul(argv[3], NULL, 10);
    tb = atof(argv[4]);
    rs = (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 0x1234567ULL;
    if (rs == 0) rs = 1;
    if (d < 1 || d > MAXD || D < 1) {
        printf("0 0\n");
        return 0;
    }
    DEGMAX = d;
    RADIUS = D;
    BUDGET = tb;

    memset(&cur, 0, sizeof(cur));
    if (scanf("%d %d", &n, &m) != 2) {
        n = 0;
        m = 0;
    }
    if (n == 0 && m == 0) {
        cur.n = 2;
        add_edge(&cur, 0, 1);
    } else {
        if (n < 2 || n >= MAXN - 1 || m < 0) ok = 0;
        if (ok) {
            cur.n = n;
            for (i = 0; i < m; i++) {
                int u, v;
                if (scanf("%d %d", &u, &v) != 2) { ok = 0; break; }
                if (u < 0 || v < 0 || u >= n || v >= n || u == v ||
                    cur.am[u][v] || cur.deg[u] >= DEGMAX || cur.deg[v] >= DEGMAX) {
                    ok = 0;
                    break;
                }
                add_edge(&cur, u, v);
            }
        }
    }
    if (!ok) {
        printf("0 0\n");
        return 0;
    }
    if (!bipartite_colour(&cur)) {
        printf("0 0\n");
        return 0;
    }
    if (anneal(&cur, 20000) != 0) {
        printf("0 0\n");
        return 0;
    }
    best_g = cur;

    /* Growth loop: add a vertex, anneal to validity, keep it or roll back. */
    c0 = 0;
    while (elapsed() < BUDGET && fails < 200) {
        long long cost;
        cur = best_g;
        if (!try_add(&cur)) {
            fails++;
            continue;
        }
        cost = anneal(&cur, ITERS);
        if (cost == 0) {
            best_g = cur;
            fails = 0;
            c0++;
        } else {
            fails++;
        }
    }

    {
        int total = 0, u, k;
        for (u = 0; u < best_g.n; u++) total += best_g.deg[u];
        printf("%d %d\n", best_g.n, total / 2);
        for (u = 0; u < best_g.n; u++) {
            for (k = 0; k < best_g.deg[u]; k++) {
                int v = best_g.nb[u][k];
                if (v > u) printf("%d %d\n", u, v);
            }
        }
    }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
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
    """True if every target t is hit by <= s elements of S."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomized greedy: choose elements so every target is hit by <= s chosen elements."""
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
        n_c, e_c = _arc_graph(m, edges, point_lines, line_points, SA, SB)
        out.append((n_c, e_c))
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
# Build: best algebraic start, then C local-search growth.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit

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
        arc_deadline = start + 0.3 * time_limit
        cands = _arc_extensions(d, arc_deadline, random.Random(seed * 7919 + d))
        for n_c, e_c in sorted(cands, key=lambda t: -t[0]):
            consider(n_c, e_c)

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Bold step: local-search growth in C, starting from the best valid graph.
    remaining = deadline - time.monotonic() - 2.0
    if remaining > 1.0 and d <= 64:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, round(remaining, 2)],
                            stdin_graph=best, timeout=remaining + 5.0)
            n_c, e_c = lib.parse_graph_text(out)
            consider(n_c, e_c)
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
