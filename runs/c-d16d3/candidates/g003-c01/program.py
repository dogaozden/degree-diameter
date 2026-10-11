import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C search engine: bipartite vertex growth by annealed edge rewiring.
#
# Input: a bipartite graph with max degree d (side 0 / side 1 found by BFS).
# Cost = number of ordered vertex pairs at distance > D, computed exactly with
# bitsets. Moves keep bipartiteness and never exceed degree d:
#   swap     : 2-switch (a-b, c-e) -> (a-e, c-b), degrees unchanged
#   endpoint : move one end of an edge to a side-0 vertex with spare degree
#   fill     : add an edge between spare-degree vertices (never raises cost)
# Whenever cost reaches 0 the graph is a valid snapshot; the engine then adds
# one new vertex (on either side, using spare degree) and anneals again.
# It prints the largest valid snapshot found before the time budget ends.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXV 1200
#define MAXW ((MAXV + 63) / 64)
#define MAXDEG 128
#define SNAPCAP (MAXV * MAXDEG / 2)

static int n, d, D;
static int deg[MAXV];
static int nb[MAXV][MAXDEG];
static unsigned char adjm[MAXV][MAXV];
static int side[MAXV];
static uint64_t bufA[MAXV][MAXW];
static uint64_t bufB[MAXV][MAXW];

static int snap_n, snap_m, snap_valid;
static int snap_u[SNAPCAP], snap_v[SNAPCAP];
static int eu[SNAPCAP], ev[SNAPCAP];
static int bq[MAXV];

static uint64_t rs;
static double budget_end;
static const double TSTART = 6.0;
static const double TEND = 0.3;

static int mv_kind, mv_a, mv_b, mv_c, mv_e;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }

static double rnd01(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}

static double now_sec(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static long long eval_cost(void) {
    int W = (n + 63) / 64;
    uint64_t (*cur)[MAXW] = bufA;
    uint64_t (*nxt)[MAXW] = bufB;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) cur[v][w] = 0;
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int k = 0; k < D; k++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < W; w++) nxt[v][w] = cur[v][w];
            for (int i = 0; i < deg[v]; i++) {
                int u = nb[v][i];
                for (int w = 0; w < W; w++) nxt[v][w] |= cur[u][w];
            }
        }
        uint64_t (*t)[MAXW] = cur;
        cur = nxt;
        nxt = t;
    }
    long long cost = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(cur[v][w]);
        cost += n - c;
    }
    return cost;
}

static void add_edge(int a, int b) {
    adjm[a][b] = 1;
    adjm[b][a] = 1;
    nb[a][deg[a]++] = b;
    nb[b][deg[b]++] = a;
}

static void del_nb(int a, int b) {
    for (int i = 0; i < deg[a]; i++) {
        if (nb[a][i] == b) {
            nb[a][i] = nb[a][deg[a] - 1];
            deg[a]--;
            return;
        }
    }
}

static void remove_edge(int a, int b) {
    adjm[a][b] = 0;
    adjm[b][a] = 0;
    del_nb(a, b);
    del_nb(b, a);
}

static void take_snapshot(void) {
    snap_n = n;
    snap_m = 0;
    for (int v = 0; v < n; v++) {
        for (int i = 0; i < deg[v]; i++) {
            int u = nb[v][i];
            if (u > v) {
                snap_u[snap_m] = v;
                snap_v[snap_m] = u;
                snap_m++;
            }
        }
    }
}

static void restore_snapshot(void) {
    for (int v = 0; v < n; v++) {
        for (int i = 0; i < deg[v]; i++) adjm[v][nb[v][i]] = 0;
        deg[v] = 0;
    }
    n = snap_n;
    for (int i = 0; i < snap_m; i++) add_edge(snap_u[i], snap_v[i]);
}

static void add_vertex(int s) {
    side[n] = s;
    deg[n] = 0;
    n++;
}

static int fill_one(void) {
    for (int t = 0; t < 40; t++) {
        int a = rndint(n);
        if (side[a] != 0 || deg[a] >= d) continue;
        int b = rndint(n);
        if (side[b] != 1 || deg[b] >= d || adjm[a][b]) continue;
        add_edge(a, b);
        return 1;
    }
    return 0;
}

static int pick_edge(int *pa, int *pb) {
    for (int t = 0; t < 64; t++) {
        int a = rndint(n);
        if (side[a] != 0 || deg[a] == 0) continue;
        *pa = a;
        *pb = nb[a][rndint(deg[a])];
        return 1;
    }
    return 0;
}

static int propose_swap(void) {
    int a, b, c, e;
    if (!pick_edge(&a, &b)) return 0;
    if (!pick_edge(&c, &e)) return 0;
    if (a == c || b == e || adjm[a][e] || adjm[c][b]) return 0;
    remove_edge(a, b);
    remove_edge(c, e);
    add_edge(a, e);
    add_edge(c, b);
    mv_kind = 0;
    mv_a = a; mv_b = b; mv_c = c; mv_e = e;
    return 1;
}

static int propose_endpoint(void) {
    int a, b, c = -1;
    if (!pick_edge(&a, &b)) return 0;
    for (int t = 0; t < 40; t++) {
        int x = rndint(n);
        if (side[x] == 0 && x != a && deg[x] < d && !adjm[x][b]) {
            c = x;
            break;
        }
    }
    if (c < 0) return 0;
    remove_edge(a, b);
    add_edge(c, b);
    mv_kind = 1;
    mv_a = a; mv_b = b; mv_c = c;
    return 1;
}

static void undo_move(void) {
    if (mv_kind == 0) {
        remove_edge(mv_a, mv_e);
        remove_edge(mv_c, mv_b);
        add_edge(mv_a, mv_b);
        add_edge(mv_c, mv_e);
    } else {
        remove_edge(mv_c, mv_b);
        add_edge(mv_a, mv_b);
    }
}

/* Anneal at the current size. Returns 1 when cost reaches 0 (valid graph). */
static int anneal(double limit) {
    double t0 = now_sec();
    double span = limit > 1e-6 ? limit : 1e-6;
    long long cost = eval_cost();
    double T = TSTART;
    long long it = 0;
    while (cost > 0) {
        if ((it & 15) == 0) {
            double t = now_sec();
            if (t - t0 >= limit || t >= budget_end) break;
            double f = (t - t0) / span;
            T = TSTART * pow(TEND / TSTART, f);
        }
        it++;
        int r = rndint(100);
        if (r < 10) {
            if (fill_one()) cost = eval_cost();
            continue;
        }
        int ok = (r < 30) ? propose_endpoint() : propose_swap();
        if (!ok) continue;
        long long c2 = eval_cost();
        long long delta = c2 - cost;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cost = c2;
        } else {
            undo_move();
        }
    }
    return cost == 0;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x1234567ULL;
    if (rs == 0) rs = 1;
    budget_end = now_sec() + tl;
    if (d < 1 || d >= MAXDEG || D < 1) {
        printf("0 0\n");
        return 0;
    }

    int in_n, in_m;
    if (scanf("%d %d", &in_n, &in_m) != 2 || in_n < 1 || in_n > MAXV - 64 ||
        in_m < 0 || in_m > SNAPCAP) {
        printf("0 0\n");
        return 0;
    }
    for (int i = 0; i < in_m; i++) {
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) {
            printf("0 0\n");
            return 0;
        }
    }
    n = in_n;
    for (int i = 0; i < in_m; i++) {
        int u = eu[i], v = ev[i];
        if (u < 0 || u >= n || v < 0 || v >= n || u == v || adjm[u][v] ||
            deg[u] >= d || deg[v] >= d) {
            printf("0 0\n");
            return 0;
        }
        add_edge(u, v);
    }

    /* Bipartition by BFS; the engine keeps every edge between side 0 and side 1. */
    for (int i = 0; i < n; i++) side[i] = -1;
    for (int s = 0; s < n; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int h = 0, t = 0;
        bq[t++] = s;
        while (h < t) {
            int v = bq[h++];
            for (int i = 0; i < deg[v]; i++) {
                int u = nb[v][i];
                if (side[u] < 0) {
                    side[u] = 1 - side[v];
                    bq[t++] = u;
                } else if (side[u] == side[v]) {
                    printf("0 0\n");
                    return 0;
                }
            }
        }
    }

    take_snapshot();
    snap_valid = 0;
    if (eval_cost() == 0) {
        snap_valid = 1;
    } else if (anneal(budget_end - now_sec())) {
        take_snapshot();
        snap_valid = 1;
    }

    if (snap_valid) {
        while (now_sec() < budget_end - 0.2 && n < MAXV - 1) {
            int s0 = rndint(2);
            int grown = 0;
            for (int k = 0; k < 2 && !grown; k++) {
                double remain = budget_end - now_sec();
                if (remain < 0.5) break;
                double lim = remain * 0.4;
                if (lim < 1.0) lim = 1.0;
                restore_snapshot();
                add_vertex(k == 0 ? s0 : 1 - s0);
                if (anneal(lim)) {
                    take_snapshot();
                    grown = 1;
                }
            }
            if (!grown) break;
        }
    }

    printf("%d %d\n", snap_n, snap_m);
    for (int i = 0; i < snap_m; i++) printf("%d %d\n", snap_u[i], snap_v[i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Constructions.
# ----------------------------------------------------------------------------

def _spare(n, edges, d):
    """Total unused degree capacity: sum of (d - deg) over all vertices."""
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
    return sum(max(0, d - x) for x in deg)


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
    """Conic (plus nucleus for even q): an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    """PG(2,q) incidence plus a new A-vertex per point of S and a new B-vertex per line indexed by S."""
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


def _arc_extensions(d, deadline, rng):
    """Return (n, edges) candidates for each prime power q with q + 1 <= d (diameter 3)."""
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
            cs = _conic_set(q, index, lib.GF(q))
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len, default=[])
        if not _loads_ok(S, s, m, point_lines, line_points):
            S = []
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
    """W(q) for the largest prime power q <= min(d-1, 7)."""
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Build: best construction, then C growth from it.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d} has diameter 2, so it is valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    moore = lib.moore_bound(d, D)

    def consider(n_c, e_c):
        nonlocal best, best_n
        if n_c > best_n and lib.is_valid(n_c, e_c, d, D):
            best, best_n = (n_c, e_c), n_c

    if D >= 3 and best_n < moore:
        for n_c, e_c in _arc_extensions(d, t0 + 0.2 * time_limit,
                                        random.Random(seed * 7919 + d)):
            consider(n_c, e_c)

    if D >= 4 and best_n < moore and time.monotonic() < t0 + 0.25 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Growth phase: anneal new vertices into the spare capacity of the best graph.
    if best_n < moore and _spare(best[0], best[1], d) >= 2:
        budget = min(0.8 * time_limit, time_limit - 8.0) - (time.monotonic() - t0)
        if budget >= 2.0:
            try:
                text = lib.run_c(C_SOURCE,
                                 [d, D, abs(int(seed)) % 2147483647, round(budget, 2)],
                                 stdin_graph=best, timeout=budget + 5.0)
                consider(*lib.parse_graph_text(text))
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
