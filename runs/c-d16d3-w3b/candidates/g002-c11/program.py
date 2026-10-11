import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C search engine.
#
# Input: a valid bipartite graph (sides are recomputed by BFS colouring).
# Moves, all keeping the graph valid with max degree d and diameter <= D:
#   1. insert: add a vertex on a random side whose neighbourhood is a greedy
#      cover of the opposite side's vertices (spare-degree vertices only).
#      Only BFS from the new vertex is needed, since old distances can only
#      shrink when a vertex is added.
#   2. edge move: replace an edge (x,y) by (x,w), w a spare vertex on the other
#      side. This moves spare capacity around the graph, which creates new
#      insertion opportunities (the new idea: spare-capacity migration).
#   3. double swap: plateau move (a,b),(c,e) -> (a,e),(c,b), degrees preserved.
# Every accepted move is verified with a full all-pairs BFS (or a single BFS
# for insertions). The largest valid graph seen is printed.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

static int d_, D_, n, cap;
static int *deg, *adj, *side, *vis, *qbuf, *cov, *cand, *sp0, *sp1;
static int *bdeg, *badj, bestn;
static int stamp = 0;
static int tbuf[1024];
static unsigned long long rs = 88172645463325252ULL;

static unsigned long long rnd(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs;
}
static int rint_(int m) { return m <= 0 ? 0 : (int)(rnd() % (unsigned long long)m); }

static int has_edge(int a, int b) {
    for (int k = 0; k < deg[a]; k++) if (adj[a * d_ + k] == b) return 1;
    return 0;
}
static void add_edge(int a, int b) {
    adj[a * d_ + deg[a]++] = b;
    adj[b * d_ + deg[b]++] = a;
}
static void del_half(int a, int b) {
    for (int k = 0; k < deg[a]; k++) {
        if (adj[a * d_ + k] == b) {
            adj[a * d_ + k] = adj[a * d_ + deg[a] - 1];
            deg[a]--;
            return;
        }
    }
}
static void del_edge(int a, int b) { del_half(a, b); del_half(b, a); }

/* BFS from s up to depth D_; returns 1 if every vertex is reached. */
static int check_from(int s) {
    stamp++;
    if (stamp == 2000000000) {
        memset(vis, 0, sizeof(int) * (size_t)cap);
        stamp = 1;
    }
    int head = 0, tail = 0, lvl = 0;
    vis[s] = stamp;
    qbuf[tail++] = s;
    int levelEnd = tail;
    while (head < tail && lvl < D_) {
        while (head < levelEnd) {
            int u = qbuf[head++];
            for (int k = 0; k < deg[u]; k++) {
                int v = adj[u * d_ + k];
                if (vis[v] != stamp) { vis[v] = stamp; qbuf[tail++] = v; }
            }
        }
        levelEnd = tail;
        lvl++;
    }
    return tail == n;
}

static int check_all(void) {
    for (int s = 0; s < n; s++) if (!check_from(s)) return 0;
    return 1;
}

/* 2-colour the graph into side[]; returns 0 if not bipartite. */
static int colour(void) {
    for (int v = 0; v < n; v++) side[v] = -1;
    for (int s = 0; s < n; s++) {
        if (side[s] != -1) continue;
        side[s] = 0;
        int head = 0, tail = 0;
        qbuf[tail++] = s;
        while (head < tail) {
            int u = qbuf[head++];
            for (int k = 0; k < deg[u]; k++) {
                int v = adj[u * d_ + k];
                if (side[v] == -1) { side[v] = 1 - side[u]; qbuf[tail++] = v; }
                else if (side[v] == side[u]) return 0;
            }
        }
    }
    return 1;
}

static void snapshot(void) {
    bestn = n;
    memcpy(bdeg, deg, sizeof(int) * (size_t)n);
    memcpy(badj, adj, sizeof(int) * (size_t)n * d_);
}

/* Insert a vertex on a random side, adjacent to a greedy cover of the other side. */
static int try_insert(void) {
    if (n >= cap) return 0;
    int s = rint_(2);
    int ncand = 0, uncovered = 0;
    for (int v = 0; v < n; v++) {
        if (side[v] == s) { cov[v] = 0; uncovered++; }
        else if (deg[v] < d_) cand[ncand++] = v;
    }
    int nT = 0;
    while (nT < d_ && uncovered > 0) {
        int best = -1, bestg = 0, ties = 0;
        for (int i = 0; i < ncand; i++) {
            int c = cand[i];
            int g = 0;
            for (int k = 0; k < deg[c]; k++) if (!cov[adj[c * d_ + k]]) g++;
            if (g > bestg) { bestg = g; best = c; ties = 1; }
            else if (g == bestg && g > 0) { ties++; if (rint_(ties) == 0) best = c; }
        }
        if (best < 0) break;
        tbuf[nT++] = best;
        for (int k = 0; k < deg[best]; k++) {
            int u = adj[best * d_ + k];
            if (!cov[u]) { cov[u] = 1; uncovered--; }
        }
    }
    if (nT == 0) return 0;
    if (uncovered > 0 && D_ <= 3) return 0;
    int x = n;
    side[x] = s;
    deg[x] = 0;
    n++;
    for (int i = 0; i < nT; i++) add_edge(x, tbuf[i]);
    if (check_from(x)) return 1;
    for (int i = 0; i < nT; i++) del_edge(x, tbuf[i]);
    n--;
    return 0;
}

/* Random vertex on the given side with positive degree, or -1. */
static int pick_side(int want) {
    for (int t = 0; t < 64; t++) {
        int v = rint_(n);
        if (side[v] == want && deg[v] > 0) return v;
    }
    return -1;
}

/* Spare-capacity migration: edge (x,y) -> (x,w) with w spare on the other side. */
static int edge_move(int ns0, int ns1) {
    int want = rint_(2);  /* side of the spare vertex w */
    int cnt = want ? ns1 : ns0;
    if (cnt == 0) return 0;
    int w = (want ? sp1 : sp0)[rint_(cnt)];
    int x = pick_side(1 - want);
    if (x < 0) return 0;
    int y = adj[x * d_ + rint_(deg[x])];
    if (y == w || has_edge(x, w)) return 0;
    del_edge(x, y);
    add_edge(x, w);
    if (check_all()) return 1;
    del_edge(x, w);
    add_edge(x, y);
    return 0;
}

/* Plateau move: (a,b),(c,e) -> (a,e),(c,b) with a,c on side 0. */
static int dswap(void) {
    int a = pick_side(0);
    int c = pick_side(0);
    if (a < 0 || c < 0 || a == c) return 0;
    int b = adj[a * d_ + rint_(deg[a])];
    int e = adj[c * d_ + rint_(deg[c])];
    if (b == e || has_edge(a, e) || has_edge(c, b)) return 0;
    del_edge(a, b);
    del_edge(c, e);
    add_edge(a, e);
    add_edge(c, b);
    if (check_all()) return 1;
    del_edge(a, e);
    del_edge(c, b);
    add_edge(a, b);
    add_edge(c, e);
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed budget_seconds\n");
        return 1;
    }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs = seed * 2654435761ULL + 88172645463325252ULL;
    if (rs == 0) rs = 1;

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 <= 0 || d_ < 1 || d_ > 1024 || D_ < 2) {
        printf("0 0\n");
        return 0;
    }
    cap = n0 + 3000;
    deg = calloc((size_t)cap, sizeof(int));
    side = calloc((size_t)cap, sizeof(int));
    vis = calloc((size_t)cap, sizeof(int));
    qbuf = calloc((size_t)cap, sizeof(int));
    cov = calloc((size_t)cap, sizeof(int));
    cand = calloc((size_t)cap, sizeof(int));
    sp0 = calloc((size_t)cap, sizeof(int));
    sp1 = calloc((size_t)cap, sizeof(int));
    bdeg = calloc((size_t)cap, sizeof(int));
    adj = calloc((size_t)cap * d_, sizeof(int));
    badj = calloc((size_t)cap * d_, sizeof(int));
    if (!deg || !side || !vis || !qbuf || !cov || !cand || !sp0 || !sp1 || !bdeg || !adj || !badj) {
        printf("0 0\n");
        return 0;
    }

    n = n0;
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { printf("0 0\n"); return 0; }
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) { printf("0 0\n"); return 0; }
        if (has_edge(u, v)) continue;
        if (deg[u] >= d_ || deg[v] >= d_) { printf("0 0\n"); return 0; }
        add_edge(u, v);
    }
    if (!colour() || !check_all()) {
        printf("0 0\n");
        return 0;
    }
    snapshot();

    clock_t t0 = clock();
    long long it = 0;
    for (;;) {
        if ((double)(clock() - t0) / CLOCKS_PER_SEC >= budget) break;
        it++;
        int ns0 = 0, ns1 = 0;
        for (int v = 0; v < n; v++) {
            if (deg[v] < d_) {
                if (side[v] == 0) sp0[ns0++] = v;
                else sp1[ns1++] = v;
            }
        }
        if (ns0 == 0 && ns1 == 0) break;
        int r = rint_(100);
        if (r < 40) {
            if (try_insert()) snapshot();
        } else if (r < 75) {
            edge_move(ns0, ns1);
        } else {
            dswap();
        }
    }

    int m = 0;
    for (int v = 0; v < bestn; v++)
        for (int k = 0; k < bdeg[v]; k++)
            if (badj[v * d_ + k] > v) m++;
    printf("%d %d\n", bestn, m);
    for (int v = 0; v < bestn; v++)
        for (int k = 0; k < bdeg[v]; k++) {
            int u = badj[v * d_ + k];
            if (u > v) printf("%d %d\n", v, u);
        }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q). Each old vertex has degree q+1,
# so with d >= q+1 it has spare capacity s = d - q - 1. Choose a point set S
# with every line holding <= s points of S and every point on <= s lines of S.
# Add an A-vertex for each P in S (joined to the lines through P) and a
# B-vertex for each j in S (joined to the points of line j).
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
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, S, line_points):
    """Build the extended graph: old PG incidence plus a new A and a new B vertex per element of S."""
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
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        cands = []
        if s >= 1:
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 40, deadline))
        if s >= 2:
            F = lib.GF(q)
            cs = _conic_set(q, index, F)
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len, default=[])
        if not _loads_ok(S, s, m, point_lines, line_points):
            continue
        n_c, e_c = _arc_graph(m, edges, point_lines, S, line_points)
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
# Glue.
# ----------------------------------------------------------------------------

def _run_engine(n, edges, d, D, seed, budget):
    """Run the C spare-migration / insertion search from a valid start graph."""
    text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                     stdin_graph=(n, edges), timeout=budget + 20.0)
    return lib.parse_graph_text(text)


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        cands = _arc_extensions(d, t0 + 0.2 * time_limit, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, e_c in cands:
            consider(n_c, e_c)

    if D >= 4 and time.monotonic() - t0 < 0.3 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # C engine: insertion + spare migration + plateau swaps from the best graph.
    deg = [0] * best_n
    for u, v in best[1]:
        deg[u] += 1
        deg[v] += 1
    has_spare = any(x < d for x in deg)
    if has_spare:
        remaining = 0.85 * time_limit - (time.monotonic() - t0) - 3.0
        if remaining > 1.0:
            try:
                n2, e2 = _run_engine(best_n, best[1], d, D, seed, remaining)
                consider(n2, e2)
            except (RuntimeError, ValueError):
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
