import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing over bipartite graphs with vertex growth.
#
# State: a bipartite graph (colour classes fixed per vertex) with max degree d.
# Cost: number of unordered vertex pairs at distance > D (bitset balls).
# Moves: rewire an edge endpoint, add a cross edge, swap two cross edges,
# delete an edge. Every move keeps the graph bipartite and degree-bounded.
# When cost reaches 0 the graph is snapshotted and a new vertex is attached
# (taking spare degree from opposite-colour vertices, stealing a neighbour
# edge when needed). On stagnation the search restarts from the best snapshot.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 2048
#define MAXD 64
#define MAXW (MAXN / 64)
#define MAXE (MAXN * MAXD / 2)
#define STAG 30000

static int n, d, D, W;
static int deg[MAXN];
static int adj[MAXN][MAXD];
static int col[MAXN];
static unsigned char M[MAXN][MAXN];
static uint64_t reach[MAXN][MAXW];
static uint64_t nxt[MAXN][MAXW];

static int have_best = 0;
static int bn = 0, bm = 0;
static int bu[MAXE], bv[MAXE], bcol[MAXN];

static int in_n = 0, im = 0;
static int iu[MAXE], iv[MAXE], icol[MAXN];

static int mv_type, mv_a, mv_b, mv_c, mv_e;

static uint64_t rs = 88172645463325252ULL;

static uint64_t nextr(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rnd(int m) {
    return (int)(nextr() % (uint64_t)m);
}

static double rndf(void) {
    return (double)(nextr() >> 11) * (1.0 / 9007199254740992.0);
}

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void rem_one(int u, int v) {
    for (int i = 0; i < deg[u]; i++) {
        if (adj[u][i] == v) {
            adj[u][i] = adj[u][--deg[u]];
            return;
        }
    }
}

static void add_e(int u, int v) {
    M[u][v] = 1;
    M[v][u] = 1;
    adj[u][deg[u]++] = v;
    adj[v][deg[v]++] = u;
}

static void del_e(int u, int v) {
    rem_one(u, v);
    rem_one(v, u);
    M[u][v] = 0;
    M[v][u] = 0;
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
                const uint64_t *src = reach[adj[v][i]];
                for (int w = 0; w < W; w++) nxt[v][w] |= src[w];
            }
        }
        for (int v = 0; v < n; v++)
            for (int w = 0; w < W; w++) reach[v][w] = nxt[v][w];
    }
}

static long eval_cost(void) {
    W = (n + 63) >> 6;
    if (W < 1) W = 1;
    compute_balls(D);
    long c = 0;
    for (int v = 0; v < n; v++) {
        int cnt = 0;
        for (int w = 0; w < W; w++) cnt += pc64(reach[v][w]);
        c += n - cnt;
    }
    return c / 2;
}

static int collect(int *eu, int *ev) {
    int m = 0;
    for (int u = 0; u < n; u++) {
        for (int i = 0; i < deg[u]; i++) {
            int v = adj[u][i];
            if (v > u && m < MAXE) {
                eu[m] = u;
                ev[m] = v;
                m++;
            }
        }
    }
    return m;
}

static void snapshot(void) {
    bn = n;
    bm = collect(bu, bv);
    memcpy(bcol, col, sizeof(int) * (size_t)n);
    have_best = 1;
}

static void load_from(int nn, int mm, const int *eu, const int *ev, const int *cl) {
    memset(M, 0, sizeof(M));
    n = nn;
    for (int v = 0; v < n; v++) {
        deg[v] = 0;
        col[v] = cl[v];
    }
    for (int i = 0; i < mm; i++) add_e(eu[i], ev[i]);
}

static void grow(void) {
    if (n >= MAXN) return;
    int w = n;
    int s = rnd(2);
    col[w] = s;
    deg[w] = 0;
    for (int i = 0; i < w; i++) {
        M[w][i] = 0;
        M[i][w] = 0;
    }
    n = w + 1;

    static int cand[MAXN];
    int nc = 0;
    for (int v = 0; v < w; v++)
        if (col[v] != s && deg[v] < d) cand[nc++] = v;
    for (int i = nc - 1; i > 0; i--) {
        int j = rnd(i + 1);
        int t = cand[i];
        cand[i] = cand[j];
        cand[j] = t;
    }
    int k = 0;
    for (int i = 0; i < nc && k < d; i++) {
        add_e(w, cand[i]);
        k++;
    }
    int tries = 0;
    while (k < d && tries < 500) {
        tries++;
        int x = rnd(w);
        if (col[x] == s || deg[x] < d || M[x][w]) continue;
        if (deg[x] == 0) continue;
        int y = adj[x][rnd(deg[x])];
        del_e(x, y);
        add_e(x, w);
        k++;
    }
}

static void load_best_or_input(void) {
    if (have_best)
        load_from(bn, bm, bu, bv, bcol);
    else
        load_from(in_n, im, iu, iv, icol);
}

/* Propose a random move and apply it. Returns 0 if no move was applied. */
static int propose(void) {
    int t = rnd(100);
    if (t < 45) {
        int a = rnd(n);
        if (!deg[a]) return 0;
        int b = adj[a][rnd(deg[a])];
        int e = -1;
        for (int tr = 0; tr < 30; tr++) {
            int x = rnd(n);
            if (col[x] == col[b] && x != b && !M[a][x] && deg[x] < d) {
                e = x;
                break;
            }
        }
        if (e < 0) return 0;
        del_e(a, b);
        add_e(a, e);
        mv_type = 0;
        mv_a = a;
        mv_b = b;
        mv_e = e;
        return 1;
    } else if (t < 65) {
        int a = rnd(n), b = rnd(n);
        if (col[a] == col[b] || deg[a] >= d || deg[b] >= d || M[a][b]) return 0;
        add_e(a, b);
        mv_type = 1;
        mv_a = a;
        mv_b = b;
        return 1;
    } else if (t < 92) {
        int a = rnd(n);
        if (!deg[a]) return 0;
        int b = adj[a][rnd(deg[a])];
        int c = rnd(n);
        if (c == a || col[c] != col[a] || !deg[c]) return 0;
        int e = adj[c][rnd(deg[c])];
        if (e == a || e == b || c == b) return 0;
        if (M[a][e] || M[c][b]) return 0;
        del_e(a, b);
        del_e(c, e);
        add_e(a, e);
        add_e(c, b);
        mv_type = 2;
        mv_a = a;
        mv_b = b;
        mv_c = c;
        mv_e = e;
        return 1;
    } else {
        int a = rnd(n);
        if (!deg[a]) return 0;
        int b = adj[a][rnd(deg[a])];
        del_e(a, b);
        mv_type = 3;
        mv_a = a;
        mv_b = b;
        return 1;
    }
}

static void undo(void) {
    switch (mv_type) {
    case 0:
        del_e(mv_a, mv_e);
        add_e(mv_a, mv_b);
        break;
    case 1:
        del_e(mv_a, mv_b);
        break;
    case 2:
        del_e(mv_a, mv_e);
        del_e(mv_c, mv_b);
        add_e(mv_a, mv_b);
        add_e(mv_c, mv_e);
        break;
    case 3:
        add_e(mv_a, mv_b);
        break;
    default:
        break;
    }
}

static void output(int nn, int mm, const int *eu, const int *ev) {
    printf("%d %d\n", nn, mm);
    for (int i = 0; i < mm; i++) printf("%d %d\n", eu[i], ev[i]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 10; i++) nextr();

    if (d < 1 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }

    int N0, M0;
    if (scanf("%d %d", &N0, &M0) != 2 || N0 < 1 || N0 > MAXN) {
        printf("0 0\n");
        return 0;
    }
    n = N0;
    for (int i = 0; i < M0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) continue;
        if (deg[u] >= d || deg[v] >= d || M[u][v]) continue;
        add_e(u, v);
    }

    static int queue[MAXN];
    for (int v = 0; v < n; v++) col[v] = -1;
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

    in_n = n;
    im = collect(iu, iv);
    memcpy(icol, col, sizeof(int) * (size_t)n);

    long cost = eval_cost();
    long cur_min = cost;
    long stag = 0;
    clock_t t0 = clock();

    while (1) {
        if ((double)(clock() - t0) / CLOCKS_PER_SEC > budget) break;

        if (cost == 0) {
            if (!have_best || n > bn) snapshot();
            if (n >= MAXN) break;
            grow();
            cost = eval_cost();
            cur_min = cost;
            stag = 0;
            continue;
        }

        if (!propose()) continue;
        long c2 = eval_cost();
        long delta = c2 - cost;
        double T = 0.15 + 0.8 * exp(-(double)stag / 1500.0);
        if (delta <= 0 || rndf() < exp(-(double)delta / T)) {
            cost = c2;
        } else {
            undo();
        }

        if (cost < cur_min) {
            cur_min = cost;
            stag = 0;
        } else {
            stag++;
        }

        if (stag > STAG) {
            load_best_or_input();
            grow();
            cost = eval_cost();
            cur_min = cost;
            stag = 0;
        }
    }

    static int outu[MAXE], outv[MAXE];
    if (have_best) {
        output(bn, bm, bu, bv);
    } else {
        output(in_n, im, iu, iv);
    }
    (void)outu;
    (void)outv;
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from PG(2, q) incidence (points 0..m-1, lines m..2m-1). Each old vertex
# has degree q+1, so spare s = d - q - 1. A new A-vertex joined to the q+1 lines
# through a chosen point, and a new B-vertex joined to the q+1 points on a
# chosen line. Loads are capped by s so degrees stay <= d.
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
    """Randomized greedy choice so that every target is hit <= s times."""
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
# Generalized quadrangle baseline (D >= 4).
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
# Glue: run the C annealer from a start graph.
# ----------------------------------------------------------------------------

def _c_anneal(graph, d, D, seed, budget):
    """Run the C annealing engine on graph; return (n, edges) or None on any failure."""
    if graph is None or budget < 0.5:
        return None
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                        stdin_graph=(graph[0], graph[1]), timeout=budget + 8.0)
        n2, e2 = lib.parse_graph_text(out)
    except Exception:
        return None
    return n2, e2


# ----------------------------------------------------------------------------
# Driver.
#   D == 3: arc-extended PG graphs as start points
#   D >= 4: generalized quadrangle W(q) as start point
#   otherwise, and as fallback: K_{d,d} (diameter 2, valid for every D >= 2)
#   then C annealing with vertex growth for most of the budget.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
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

    if D == 3:
        arcs = _arc_extensions(d, start + 0.15 * time_limit,
                               random.Random(seed * 7919 + d))
        arcs.sort(key=lambda t: -t[0])
        for g in arcs[:3]:
            consider(g)
    elif D >= 4:
        consider(_best_gq(d))

    budget = 0.72 * time_limit - elapsed()
    if budget >= 1.0:
        consider(_c_anneal(best, d, D, seed, budget))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
