import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: local search on bipartite graphs with diameter <= D.
#
# Input: a graph (n, edges) with max degree <= d. It anneals over degree-
# preserving 2-switches, endpoint moves, and edge additions, minimising the
# number of vertex pairs at distance > D (bitset BFS). It prints the first
# graph with zero violations, or "0 0" if none is found within the budget.
# Sides come from BFS colouring, so every move keeps the graph bipartite.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1100
#define MAXW 18
#define MAXDEG 64

static int n, d, D, nw;
static int deg[MAXN];
static int adj[MAXN][MAXDEG];
static int side[MAXN];
static int L0[MAXN], L1[MAXN], c0, c1;
static int F0[MAXN], F1[MAXN], f0, f1;
static uint64_t X[MAXN][MAXW], Y[MAXN][MAXW];
static uint64_t rs;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rndu(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int has_edge(int a, int b) {
    for (int i = 0; i < deg[a]; i++)
        if (adj[a][i] == b) return 1;
    return 0;
}
static void del_arc(int a, int b) {
    for (int i = 0; i < deg[a]; i++)
        if (adj[a][i] == b) { adj[a][i] = adj[a][--deg[a]]; return; }
}
static void add_e(int a, int b) {
    adj[a][deg[a]++] = b;
    adj[b][deg[b]++] = a;
}
static void del_e(int a, int b) {
    del_arc(a, b);
    del_arc(b, a);
}
static int popc(uint64_t x) {
    int c = 0;
    while (x) { x &= x - 1; c++; }
    return c;
}

/* Number of unordered vertex pairs at distance > D. */
static long long cost_of(void) {
    uint64_t (*cur)[MAXW] = X;
    uint64_t (*nxt)[MAXW] = Y;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < nw; w++) cur[v][w] = 0;
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int s = 0; s < D; s++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < nw; w++) nxt[v][w] = cur[v][w];
            for (int i = 0; i < deg[v]; i++) {
                int u = adj[v][i];
                for (int w = 0; w < nw; w++) nxt[v][w] |= cur[u][w];
            }
        }
        uint64_t (*t)[MAXW] = cur;
        cur = nxt;
        nxt = t;
    }
    long long total = 0;
    for (int v = 0; v < n; v++)
        for (int w = 0; w < nw; w++) total += popc(cur[v][w]);
    return ((long long)n * n - total) / 2;
}

static int colour(void) {
    static int stk[MAXN];
    for (int v = 0; v < n; v++) side[v] = -1;
    for (int s = 0; s < n; s++) {
        if (side[s] != -1) continue;
        side[s] = 0;
        int sp = 0;
        stk[sp++] = s;
        while (sp) {
            int u = stk[--sp];
            for (int i = 0; i < deg[u]; i++) {
                int v = adj[u][i];
                if (side[v] == -1) {
                    side[v] = 1 - side[u];
                    stk[sp++] = v;
                } else if (side[v] == side[u]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

static void output_graph(void) {
    long long m = 0;
    for (int i = 0; i < c0; i++) m += deg[L0[i]];
    printf("%d %lld\n", n, m);
    for (int i = 0; i < c0; i++) {
        int a = L0[i];
        for (int j = 0; j < deg[a]; j++) printf("%d %d\n", a, adj[a][j]);
    }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    rs = strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (rs == 0) rs = 1;
    double tl = atof(argv[4]);
    clock_t t0 = clock();

    int nn, mm;
    if (scanf("%d %d", &nn, &mm) != 2 || nn <= 0 || nn > MAXN - 1 || mm < 0 ||
        d < 1 || d > MAXDEG) {
        printf("0 0\n");
        return 0;
    }
    n = nn;
    nw = (n + 63) / 64;
    if (nw > MAXW) { printf("0 0\n"); return 0; }
    memset(deg, 0, sizeof deg);
    for (int i = 0; i < mm; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { printf("0 0\n"); return 0; }
        if (u < 0 || v < 0 || u >= n || v >= n || u == v || deg[u] >= d ||
            deg[v] >= d || has_edge(u, v)) {
            printf("0 0\n");
            return 0;
        }
        add_e(u, v);
    }
    if (!colour()) { printf("0 0\n"); return 0; }
    c0 = c1 = 0;
    for (int v = 0; v < n; v++) {
        if (side[v] == 0) L0[c0++] = v;
        else L1[c1++] = v;
    }
    if (c0 == 0 || c1 == 0) { printf("0 0\n"); return 0; }

    long long cur = cost_of();
    long long it = 0;
    double T = 1.0;
    while (cur != 0) {
        if ((it & 31) == 0) {
            double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
            if (el >= tl) break;
            double fr = el / tl;
            T = 4.0 * pow(0.03 / 4.0, fr);
        }
        it++;

        f0 = f1 = 0;
        for (int i = 0; i < c0; i++) if (deg[L0[i]] < d) F0[f0++] = L0[i];
        for (int i = 0; i < c1; i++) if (deg[L1[i]] < d) F1[f1++] = L1[i];

        int nr = 0, na = 0;
        int ra[2][2], aa[2][2];
        double r = rndu();
        if (r < 0.45) {
            /* 2-switch: degree preserving. */
            int a1 = L0[rndint(c0)];
            int a2 = L0[rndint(c0)];
            if (a1 == a2 || deg[a1] == 0 || deg[a2] == 0) continue;
            int b1 = adj[a1][rndint(deg[a1])];
            int b2 = adj[a2][rndint(deg[a2])];
            if (b1 == b2 || has_edge(a1, b2) || has_edge(a2, b1)) continue;
            ra[0][0] = a1; ra[0][1] = b1; ra[1][0] = a2; ra[1][1] = b2; nr = 2;
            aa[0][0] = a1; aa[0][1] = b2; aa[1][0] = a2; aa[1][1] = b1; na = 2;
        } else if (r < 0.7) {
            /* Move the side-1 endpoint of an edge to a non-full side-1 vertex. */
            if (f1 == 0) continue;
            int a = L0[rndint(c0)];
            if (deg[a] == 0) continue;
            int b = adj[a][rndint(deg[a])];
            int bp = F1[rndint(f1)];
            if (bp == b || has_edge(a, bp)) continue;
            ra[0][0] = a; ra[0][1] = b; nr = 1;
            aa[0][0] = a; aa[0][1] = bp; na = 1;
        } else if (r < 0.95) {
            /* Move the side-0 endpoint of an edge to a non-full side-0 vertex. */
            if (f0 == 0) continue;
            int b = L1[rndint(c1)];
            if (deg[b] == 0) continue;
            int a = adj[b][rndint(deg[b])];
            int ap = F0[rndint(f0)];
            if (ap == a || has_edge(ap, b)) continue;
            ra[0][0] = a; ra[0][1] = b; nr = 1;
            aa[0][0] = ap; aa[0][1] = b; na = 1;
        } else {
            /* Add an edge between two non-full vertices on opposite sides. */
            if (f0 == 0 || f1 == 0) continue;
            int a = F0[rndint(f0)];
            int b = F1[rndint(f1)];
            if (has_edge(a, b)) continue;
            aa[0][0] = a; aa[0][1] = b; na = 1;
        }

        for (int i = 0; i < nr; i++) del_e(ra[i][0], ra[i][1]);
        for (int i = 0; i < na; i++) add_e(aa[i][0], aa[i][1]);
        long long nc = cost_of();
        long long delta = nc - cur;
        if (delta <= 0 || rndu() < exp(-(double)delta / T)) {
            cur = nc;
        } else {
            for (int i = 0; i < na; i++) del_e(aa[i][0], aa[i][1]);
            for (int i = 0; i < nr; i++) add_e(ra[i][0], ra[i][1]);
        }
    }

    if (cur == 0) output_graph();
    else printf("0 0\n");
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions.
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
    """Randomized greedy set S with all loads <= s; returns the largest found."""
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
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    """PG(2,q) incidence plus a new A vertex per P in S (joined to lines through P)
    and a new B vertex per j in S (joined to points on line j)."""
    k = len(S)
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in line_points[j]:
            E.append((Q, b))
    return 2 * m + 2 * k, E


def _arc_candidates(d, deadline, rng):
    """Arc-extended projective plane graphs (diameter 3) for each prime power q with q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        if s < 0:
            continue
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        if s == 0:
            S = []
        else:
            cands = [_greedy_arc(m, s, point_lines, line_points, rng, 40, deadline)]
            if s >= 2:
                F = lib.GF(q)
                cs = _conic_set(q, index, F)
                if _loads_ok(cs, s, m, point_lines, line_points):
                    cands.append(cs)
            S = max(cands, key=len)
        if not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


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


def _grow(d, D, seed, start, deadline):
    """Repeatedly ask the C engine for one more vertex, starting from the best valid graph.

    Each run adds one vertex attached to a minimum-degree vertex, then anneals.
    Only valid, larger graphs replace the current best, so the result is never worse.
    """
    best = start
    it = 0
    while True:
        remaining = deadline - time.monotonic()
        n0, e0 = best
        if remaining < 4 or n0 + 1 > 1000 or n0 >= lib.moore_bound(d, D):
            break
        deg = [0] * n0
        for u, v in e0:
            deg[u] += 1
            deg[v] += 1
        v0 = min(range(n0), key=deg.__getitem__)
        if deg[v0] >= d:
            break
        budget = min(remaining - 2.0, 18.0)
        if budget < 1.0:
            break
        start_graph = (n0 + 1, e0 + [(v0, n0)])
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed * 1000 + it, round(budget, 2)],
                            stdin_graph=start_graph, timeout=budget + 4.0)
            n_new, e_new = lib.parse_graph_text(out)
        except Exception:
            break
        if n_new > n0 and lib.is_valid(n_new, e_new, d, D):
            best = (n_new, e_new)
        it += 1
    return best


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    deadline = t0 + 0.7 * time_limit
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    if not lib.is_valid(best[0], best[1], d, D):
        best = (2, [(0, 1)])

    def consider(n_c, e_c):
        nonlocal best
        if n_c > best[0] and lib.is_valid(n_c, e_c, d, D):
            best = (n_c, e_c)

    if D >= 3:
        rng = random.Random(seed * 7919 + d)
        for n_c, e_c in _arc_candidates(d, deadline, rng):
            consider(n_c, e_c)

    if D >= 4 and time.monotonic() < deadline:
        g = _best_gq(d)
        if g is not None:
            consider(g[0], g[1])

    # Bold step: C local search adds vertices to the best graph found so far.
    # Skipped when the graph already meets the Moore bound, or when d is out of range.
    if D >= 3 and 3 <= d <= 60 and time.monotonic() < deadline:
        best = _grow(d, D, seed, best, deadline)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
