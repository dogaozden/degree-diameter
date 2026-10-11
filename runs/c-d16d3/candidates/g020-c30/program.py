import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C search engine: vertex insertion with simulated-annealing repair.
#
# State: a bipartite graph with max degree d. Growth step: add a vertex v of a
# random colour and join it to d opposite-colour vertices, removing one edge at
# each of them (degrees stay <= d, the edge count is unchanged). Then anneal the
# number of ordered-pair distance violations (distance > D) with degree-
# preserving 2-switches, "relocations" that move a free slot, and free edge
# additions. Each time the cost reaches 0 the graph is saved and grown again;
# after too many failed moves the best valid graph is restored and a new
# insertion is tried. Distances are computed with 64-bit reachability bitsets.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1200
#define MAXDEG 40
#define WMAX ((MAXN + 63) / 64)
#define MOVES_PER_TRY 3000

static int N, Dg, Dia, W;
static int adj[MAXN][MAXDEG];
static int deg[MAXN];
static int col[MAXN];
static int best_N = 0;
static int best_adj[MAXN][MAXDEG];
static int best_deg[MAXN];
static int best_col[MAXN];
static uint64_t BA[MAXN][WMAX], BB[MAXN][WMAX];
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rnd(int m) { return (int)(rnd64() % (uint64_t)m); }
static double rndu(void) { return (double)(rnd64() >> 11) / 9007199254740992.0; }

static int has_edge(int a, int b) {
    for (int k = 0; k < deg[a]; k++) if (adj[a][k] == b) return 1;
    return 0;
}
static void add_edge(int a, int b) {
    adj[a][deg[a]++] = b;
    adj[b][deg[b]++] = a;
}
static void rem_half(int a, int b) {
    for (int k = 0; k < deg[a]; k++)
        if (adj[a][k] == b) { adj[a][k] = adj[a][--deg[a]]; return; }
}
static void del_edge(int a, int b) { rem_half(a, b); rem_half(b, a); }

static int popc(uint64_t x) { int c = 0; while (x) { x &= x - 1; c++; } return c; }

/* Number of unordered pairs at distance > Dia (unreachable pairs included). */
static long bad_pairs(void) {
    uint64_t (*cur)[WMAX] = BA, (*nx)[WMAX] = BB;
    W = (N + 63) / 64;
    for (int v = 0; v < N; v++) {
        for (int w = 0; w < W; w++) cur[v][w] = 0;
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int it = 0; it < Dia; it++) {
        for (int v = 0; v < N; v++) {
            for (int w = 0; w < W; w++) nx[v][w] = cur[v][w];
            for (int k = 0; k < deg[v]; k++) {
                int u = adj[v][k];
                for (int w = 0; w < W; w++) nx[v][w] |= cur[u][w];
            }
        }
        uint64_t (*t)[WMAX] = cur; cur = nx; nx = t;
    }
    long bad = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(cur[v][w]);
        bad += N - c;
    }
    return bad / 2;
}

static void save_best(void) {
    best_N = N;
    memcpy(best_adj, adj, sizeof(adj));
    memcpy(best_deg, deg, sizeof(deg));
    memcpy(best_col, col, sizeof(col));
}
static void restore_best(void) {
    N = best_N;
    memcpy(adj, best_adj, sizeof(adj));
    memcpy(deg, best_deg, sizeof(deg));
    memcpy(col, best_col, sizeof(col));
}

static int insert_vertex(void) {
    if (N >= MAXN - 1) return 0;
    int c = rnd(2);
    int bs[MAXDEG];
    int nb = 0;
    for (int tries = 0; tries < 60 * Dg && nb < Dg; tries++) {
        int b = rnd(N);
        if (col[b] == c || deg[b] == 0) continue;
        int dup = 0;
        for (int i = 0; i < nb; i++) if (bs[i] == b) { dup = 1; break; }
        if (!dup) bs[nb++] = b;
    }
    if (nb == 0) return 0;
    int v = N++;
    col[v] = c;
    deg[v] = 0;
    for (int i = 0; i < nb; i++) {
        int b = bs[i];
        int a = adj[b][rnd(deg[b])];
        del_edge(a, b);
        add_edge(v, b);
    }
    return 1;
}

static int pick_vertex_color(int c) {
    for (int t = 0; t < 200; t++) {
        int x = rnd(N);
        if (col[x] == c && deg[x] > 0) return x;
    }
    return -1;
}

/* Replace (a,b),(a2,b2) by (a,b2),(a2,b): degrees unchanged. */
static int do_switch(int *pa, int *pb, int *pa2, int *pb2) {
    int a = rnd(N);
    if (deg[a] == 0) return 0;
    int b = adj[a][rnd(deg[a])];
    int a2 = pick_vertex_color(col[a]);
    if (a2 < 0 || a2 == a) return 0;
    int b2 = adj[a2][rnd(deg[a2])];
    if (b2 == b || has_edge(a, b2) || has_edge(a2, b)) return 0;
    del_edge(a, b); del_edge(a2, b2);
    add_edge(a, b2); add_edge(a2, b);
    *pa = a; *pb = b; *pa2 = a2; *pb2 = b2;
    return 1;
}
static void undo_switch(int a, int b, int a2, int b2) {
    del_edge(a, b2); del_edge(a2, b);
    add_edge(a, b); add_edge(a2, b2);
}

/* Move one edge end from a2 to a deficient vertex a of the same colour. */
static int do_relocate(int *pa, int *pa2, int *pb2) {
    int a = -1;
    for (int t = 0; t < 200; t++) {
        int x = rnd(N);
        if (deg[x] < Dg) { a = x; break; }
    }
    if (a < 0) return 0;
    int a2 = pick_vertex_color(col[a]);
    if (a2 < 0 || a2 == a) return 0;
    int b2 = adj[a2][rnd(deg[a2])];
    if (has_edge(a, b2)) return 0;
    del_edge(a2, b2); add_edge(a, b2);
    *pa = a; *pa2 = a2; *pb2 = b2;
    return 1;
}
static void undo_relocate(int a, int a2, int b2) {
    del_edge(a, b2); add_edge(a2, b2);
}

static void print_graph(int n, int A[][MAXDEG], const int *dg) {
    long m = 0;
    for (int v = 0; v < n; v++) m += dg[v];
    printf("%d %ld\n", n, m / 2);
    for (int v = 0; v < n; v++)
        for (int k = 0; k < dg[v]; k++)
            if (v < A[v][k]) printf("%d %d\n", v, A[v][k]);
}

static void echo_input(int n, int m, const int *eu, const int *ev) {
    printf("%d %d\n", n, m);
    for (int i = 0; i < m; i++) printf("%d %d\n", eu[i], ev[i]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) rnd64();

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) { n = 0; m = 0; }
    if (m < 0) m = 0;
    int *eu = malloc(sizeof(int) * (m + 1));
    int *ev = malloc(sizeof(int) * (m + 1));
    int readok = 1;
    for (int i = 0; i < m; i++) {
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) { readok = 0; m = i; break; }
    }
    if (n <= 0 || n >= MAXN - 1 || D < 1 || d < 1 || d > MAXDEG - 2 || !readok) {
        echo_input(n, m, eu, ev);
        return 0;
    }

    N = n; Dg = d; Dia = D; W = (N + 63) / 64;
    int ok = 1;
    for (int i = 0; i < m && ok; i++) {
        int a = eu[i], b = ev[i];
        if (a < 0 || b < 0 || a >= n || b >= n || a == b) { ok = 0; break; }
        if (deg[a] >= d || deg[b] >= d || has_edge(a, b)) { ok = 0; break; }
        add_edge(a, b);
    }
    for (int v = 0; v < n; v++) col[v] = -1;
    int *q = malloc(sizeof(int) * (n + 1));
    for (int s = 0; s < n && ok; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int qh = 0, qt = 0;
        q[qt++] = s;
        while (qh < qt && ok) {
            int u = q[qh++];
            for (int k = 0; k < deg[u]; k++) {
                int w = adj[u][k];
                if (col[w] < 0) { col[w] = 1 - col[u]; q[qt++] = w; }
                else if (col[w] == col[u]) { ok = 0; break; }
            }
        }
    }
    free(q);
    if (!ok) {
        echo_input(n, m, eu, ev);
        return 0;
    }

    clock_t t0 = clock();
    long cost = bad_pairs();
    int have_best = 0;
    if (cost == 0) { save_best(); have_best = 1; }
    int left = MOVES_PER_TRY;
    const double T = 0.6;

    for (;;) {
        if ((double)(clock() - t0) / CLOCKS_PER_SEC > budget) break;
        if (cost == 0) {
            save_best(); have_best = 1;
            if (!insert_vertex()) break;
            cost = bad_pairs();
            left = MOVES_PER_TRY;
            continue;
        }
        if (left <= 0) {
            if (have_best) {
                restore_best();
                if (!insert_vertex()) break;
            }
            cost = bad_pairs();
            left = MOVES_PER_TRY;
            continue;
        }
        left--;
        double r = rndu();
        if (r < 0.15) {
            int x = rnd(N), y = rnd(N);
            if (deg[x] < Dg && deg[y] < Dg && col[x] != col[y] && !has_edge(x, y)) {
                add_edge(x, y);
                cost = bad_pairs();
            }
            continue;
        }
        long old = cost;
        int a = 0, b = 0, a2 = 0, b2 = 0;
        if (r < 0.6) {
            if (!do_switch(&a, &b, &a2, &b2)) continue;
            long nc = bad_pairs();
            if (nc <= old || rndu() < exp(-(double)(nc - old) / T)) cost = nc;
            else undo_switch(a, b, a2, b2);
        } else {
            if (!do_relocate(&a, &a2, &b2)) continue;
            long nc = bad_pairs();
            if (nc <= old || rndu() < exp(-(double)(nc - old) / T)) cost = nc;
            else undo_relocate(a, a2, b2);
        }
    }

    if (cost == 0) { save_best(); have_best = 1; }
    if (have_best) print_graph(best_N, best_adj, best_deg);
    else echo_input(n, m, eu, ev);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Construction: arc-extended projective plane graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q). Add an A-vertex for each point P
# in a set SA (joined to the q+1 lines through P) and a B-vertex for each line
# j in a set SB (joined to the q+1 points on j). Old lines get one extra edge per
# SA-point on them, so SA needs at most s = d-q-1 points per line. Old points
# get one extra edge per SB-line through them, so SB needs at most s lines per
# point. The two conditions are independent, so SA and SB are chosen separately
# (the parent used one set for both).
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


def _capped_ok(S, targets_of, ntar, s):
    """True if every target is hit by at most s chosen sources."""
    load = [0] * ntar
    for x in S:
        for t in targets_of[x]:
            load[t] += 1
            if load[t] > s:
                return False
    return True


def _capped_greedy(count, targets_of, ntar, s, rng, trials, deadline):
    """Randomized greedy: largest source set found with every target hit <= s times."""
    best = []
    order = list(range(count))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        load = [0] * ntar
        S = []
        for x in order:
            tg = targets_of[x]
            if all(load[t] < s for t in tg):
                S.append(x)
                for t in tg:
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


def _best_capped(count, targets_of, ntar, s, rng, deadline, conic):
    """Best of the greedy and conic candidates for one capacity problem."""
    best = []
    if s >= 1:
        best = _capped_greedy(count, targets_of, ntar, s, rng, 40, deadline)
    if conic is not None and s >= 2 and len(conic) > len(best) \
            and _capped_ok(conic, targets_of, ntar, s):
        best = conic
    return best


def _arc_graph(m, edges, point_lines, line_points, SA, SB):
    """Old PG incidence plus A-vertices (pencils at SA) and B-vertices (dual pencils at SB)."""
    n = 2 * m + len(SA) + len(SB)
    E = list(edges)
    for t, P in enumerate(SA):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    base_b = 2 * m + len(SA)
    for t, j in enumerate(SB):
        b = base_b + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _arc_extensions(d, deadline, rng):
    """Candidate (n, edges) for each prime power q with q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        conic = _conic_set(q, index, lib.GF(q)) if s >= 2 else None
        SA = _best_capped(m, point_lines, m, s, rng, deadline, conic)
        SB = _best_capped(m, line_points, m, s, rng, deadline, conic)
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
# Build: construction, then the C insertion/annealing search from the best graph.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t_start = time.monotonic()
    rng = random.Random(seed)

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
        deadline = t_start + 0.25 * time_limit
        for n_c, e_c in _arc_extensions(d, deadline, random.Random(seed * 7919 + d)):
            consider(n_c, e_c)

    if D >= 4 and time.monotonic() < t_start + 0.3 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # C search: grow the best graph by vertex insertion plus annealing repair.
    elapsed = time.monotonic() - t_start
    budget = 0.75 * time_limit - elapsed - 1.0
    if budget >= 1.0 and best_n < lib.moore_bound(d, D) and d <= 30:
        try:
            remaining = time_limit - (time.monotonic() - t_start)
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             stdin_graph=best, timeout=max(1.0, remaining - 3.0))
            n2, e2 = lib.parse_graph_text(text)
            consider(n2, e2)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
