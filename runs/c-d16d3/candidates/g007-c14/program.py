import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Stage 1: arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q). Every old vertex has degree q+1,
# so with d >= q+1 it has spare capacity s = d - q - 1. Choose a point set S
# such that every line holds at most s points of S and every point lies on at
# most s lines indexed by S. For each P in S add a new A-vertex joined to the
# q+1 lines through P; for each j in S add a new B-vertex joined to the q+1
# points on line j. The diameter stays 3.
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


def _arc_graph(m, edges, point_lines, line_points, S):
    """Old PG incidence plus a new A and a new B vertex per element of S."""
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):  # S is also a set of line indices (same vectors)
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
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
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
# Stage 2: C local search that grows a valid graph one vertex at a time.
#
# State: a bipartite graph with N vertices, max degree d, and a cost equal to
# the number of unordered pairs at distance > D. Moves: add edge, remove edge,
# rewire one endpoint, and degree-preserving swap. Simulated annealing on the
# cost. Whenever the cost reaches 0, the graph is saved and a new isolated
# vertex is added. The best valid graph is printed when time runs out.
# Distances are computed with bitsets over all vertices.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1100
#define MAXW ((MAXN + 63) / 64)
#define MAXD 64
#define ITER_LIMIT 30000
#define T0 3.0
#define T1 0.05

static int Dg, Dd, N;
static int deg[MAXN];
static int adj[MAXN][MAXD];
static int side[MAXN];
static uint64_t RA[MAXN][MAXW];
static uint64_t RB[MAXN][MAXW];

static int BN, BM;
static int BU[MAXN * MAXD];
static int BV[MAXN * MAXD];

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rint_(int k) { return (int)(rnd() % (uint64_t)k); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static clock_t t0c;
static double budget;
static double elapsed(void) { return (double)(clock() - t0c) / CLOCKS_PER_SEC; }

static int has_edge(int u, int v) {
    for (int i = 0; i < deg[u]; i++)
        if (adj[u][i] == v) return 1;
    return 0;
}

static void remove_from(int u, int v) {
    for (int i = 0; i < deg[u]; i++) {
        if (adj[u][i] == v) {
            adj[u][i] = adj[u][--deg[u]];
            return;
        }
    }
}

static void add_edge(int u, int v) {
    adj[u][deg[u]++] = v;
    adj[v][deg[v]++] = u;
}

static void del_edge(int u, int v) {
    remove_from(u, v);
    remove_from(v, u);
}

static int popc(uint64_t x) {
    int c = 0;
    while (x) {
        x &= x - 1;
        c++;
    }
    return c;
}

/* Number of unordered pairs at distance > Dd (0 means valid). */
static long long evaluate(void) {
    int w = (N + 63) / 64;
    for (int v = 0; v < N; v++) {
        memset(RA[v], 0, (size_t)w * sizeof(uint64_t));
        RA[v][v >> 6] |= 1ULL << (v & 63);
    }
    uint64_t (*src)[MAXW] = RA;
    uint64_t (*dst)[MAXW] = RB;
    for (int step = 0; step < Dd; step++) {
        for (int v = 0; v < N; v++) {
            for (int k = 0; k < w; k++) dst[v][k] = src[v][k];
            for (int i = 0; i < deg[v]; i++) {
                int u = adj[v][i];
                for (int k = 0; k < w; k++) dst[v][k] |= src[u][k];
            }
        }
        uint64_t (*t)[MAXW] = src;
        src = dst;
        dst = t;
    }
    long long bad = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int k = 0; k < w; k++) c += popc(src[v][k]);
        bad += N - c;
    }
    return bad / 2;
}

static void add_vertex(void) {
    deg[N] = 0;
    side[N] = rint_(2);
    N++;
}

static int pick_deg(void) {
    for (int t = 0; t < 200; t++) {
        int v = rint_(N);
        if (deg[v] > 0) return v;
    }
    return -1;
}

static void save_best(void) {
    BN = N;
    BM = 0;
    for (int u = 0; u < N; u++) {
        for (int i = 0; i < deg[u]; i++) {
            int v = adj[u][i];
            if (u < v) {
                BU[BM] = u;
                BV[BM] = v;
                BM++;
            }
        }
    }
}

static int accept(long long cand, long long cur, double T) {
    if (cand <= cur) return 1;
    return rdbl() < exp(-(double)(cand - cur) / T);
}

static int assign_sides(void) {
    static int col[MAXN];
    static int q[MAXN];
    for (int v = 0; v < N; v++) col[v] = -1;
    for (int s = 0; s < N; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int qh = 0, qt = 0;
        q[qt++] = s;
        while (qh < qt) {
            int x = q[qh++];
            for (int i = 0; i < deg[x]; i++) {
                int w = adj[x][i];
                if (col[w] < 0) {
                    col[w] = 1 - col[x];
                    q[qt++] = w;
                } else if (col[w] == col[x]) {
                    return 0;
                }
            }
        }
    }
    for (int v = 0; v < N; v++) side[v] = col[v];
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    Dg = atoi(argv[1]);
    Dd = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    budget = atof(argv[4]);
    t0c = clock();
    for (int i = 0; i < 20; i++) rnd();
    BN = 0;
    BM = 0;
    if (Dg < 1 || Dg >= MAXD || Dd < 1) {
        printf("0 0\n");
        return 0;
    }

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) {
        n = 0;
        m = 0;
    }
    if (n <= 0) {
        N = 2;
        deg[0] = deg[1] = 0;
        side[0] = 0;
        side[1] = 1;
        add_edge(0, 1);
    } else {
        if (n >= MAXN - 1) {
            printf("0 0\n");
            return 0;
        }
        N = n;
        for (int i = 0; i < m; i++) {
            int u, v;
            if (scanf("%d %d", &u, &v) != 2) break;
            if (u < 0 || u >= N || v < 0 || v >= N || u == v) continue;
            if (deg[u] >= Dg || deg[v] >= Dg || has_edge(u, v)) continue;
            add_edge(u, v);
        }
        if (!assign_sides()) {
            printf("0 0\n");
            return 0;
        }
    }

    long long cost_now = evaluate();
    if (cost_now == 0) save_best();

    int stop = 0;
    while (!stop && N < MAXN - 1) {
        if (cost_now == 0) {
            save_best();
            add_vertex();
            cost_now = evaluate();
            continue;
        }
        for (long long it = 0; it < ITER_LIMIT && cost_now != 0; it++) {
            if ((it & 63) == 0 && elapsed() > budget) {
                stop = 1;
                break;
            }
            double T = T0 * pow(T1 / T0, (double)it / (double)ITER_LIMIT);
            int r = rint_(100);
            long long cand;
            if (r < 30) {
                int u = rint_(N), v = rint_(N);
                if (u == v || side[u] == side[v] || deg[u] >= Dg || deg[v] >= Dg || has_edge(u, v))
                    continue;
                add_edge(u, v);
                cand = evaluate();
                if (accept(cand, cost_now, T)) cost_now = cand;
                else del_edge(u, v);
            } else if (r < 40) {
                int u = pick_deg();
                if (u < 0) continue;
                int v = adj[u][rint_(deg[u])];
                del_edge(u, v);
                cand = evaluate();
                if (accept(cand, cost_now, T)) cost_now = cand;
                else add_edge(u, v);
            } else if (r < 65) {
                int a = pick_deg();
                if (a < 0) continue;
                int b = adj[a][rint_(deg[a])];
                int x = rint_(N);
                if (side[x] == side[a] || x == b || deg[x] >= Dg || has_edge(a, x)) continue;
                del_edge(a, b);
                add_edge(a, x);
                cand = evaluate();
                if (accept(cand, cost_now, T)) cost_now = cand;
                else {
                    del_edge(a, x);
                    add_edge(a, b);
                }
            } else {
                int a = pick_deg();
                if (a < 0) continue;
                int b = adj[a][rint_(deg[a])];
                int c = rint_(N);
                if (c == a || side[c] != side[a] || deg[c] == 0) continue;
                int e = adj[c][rint_(deg[c])];
                if (b == e || has_edge(a, e) || has_edge(c, b)) continue;
                del_edge(a, b);
                del_edge(c, e);
                add_edge(a, e);
                add_edge(c, b);
                cand = evaluate();
                if (accept(cand, cost_now, T)) cost_now = cand;
                else {
                    del_edge(a, e);
                    del_edge(c, b);
                    add_edge(a, b);
                    add_edge(c, e);
                }
            }
        }
    }

    if (BN == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", BN, BM);
    for (int i = 0; i < BM; i++) printf("%d %d\n", BU[i], BV[i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t_start = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(cand):
        nonlocal best
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Constructions (fast): arc-extended PG(2,q) for D >= 3, W(q) for D >= 4.
    if D >= 3:
        for cand in _arc_extensions(d, t_start + 0.3 * time_limit, random.Random(seed * 7919 + d)):
            consider(cand)
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq)

    # Main search: C local search grows the best construction by one vertex at a time.
    remaining = 0.8 * time_limit - (time.monotonic() - t_start) - 2.0
    if remaining > 1.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, round(remaining, 2)],
                            stdin_graph=best, timeout=remaining + 5.0)
            consider(lib.parse_graph_text(out))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
