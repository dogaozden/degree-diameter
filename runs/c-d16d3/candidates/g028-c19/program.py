import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C search engine (bold change: local search over bipartite graphs).
#
# Starts from the Python construction and keeps a valid state. It adds vertices
# (a pair, or one vertex on a side), fills spare degree greedily, then runs
# simulated annealing over degree-preserving swaps and edge shifts. The cost is
# the number of ordered vertex pairs at distance > D. A state with cost 0 is
# recorded as the new best, and growth continues from there.
# Output: the best valid graph found, or "0 0" if the input is not valid.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#define _POSIX_C_SOURCE 200809L
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>

#define MAXN 1100
#define MAXD 48
#define STAGE_ITERS 2500

typedef struct { int n; int adj[MAXN][MAXD]; int dg[MAXN]; } G;

static G cur, sv, best;
static int side[MAXN];
static int DEG, DIAM;
static uint64_t rs = 88172645463325252ULL;
static uint32_t stamp[MAXN];
static uint32_t curstamp = 0;
static int qbuf[MAXN], lvl[MAXN];
static struct timespec t_start;

static double elapsed(void) {
    struct timespec t;
    clock_gettime(CLOCK_MONOTONIC, &t);
    return (double)(t.tv_sec - t_start.tv_sec) + 1e-9 * (double)(t.tv_nsec - t_start.tv_nsec);
}

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndi(int k) { return (int)(rnd() % (uint64_t)k); }

static double rndd(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static void shuffle(int *a, int k) {
    for (int i = k - 1; i > 0; i--) {
        int j = rndi(i + 1);
        int t = a[i];
        a[i] = a[j];
        a[j] = t;
    }
}

static int has_edge(const G *g, int a, int b) {
    for (int k = 0; k < g->dg[a]; k++)
        if (g->adj[a][k] == b) return 1;
    return 0;
}

static void add_edge(G *g, int a, int b) {
    g->adj[a][g->dg[a]++] = b;
    g->adj[b][g->dg[b]++] = a;
}

static void rem_from(G *g, int a, int b) {
    for (int k = 0; k < g->dg[a]; k++) {
        if (g->adj[a][k] == b) {
            g->adj[a][k] = g->adj[a][--g->dg[a]];
            return;
        }
    }
}

static void rem_edge(G *g, int a, int b) {
    rem_from(g, a, b);
    rem_from(g, b, a);
}

/* Total number of ordered pairs at distance > DIAM (disconnected counts too). */
static long long cost_of(const G *g) {
    long long total = 0;
    int n = g->n;
    for (int s = 0; s < n; s++) {
        curstamp++;
        if (curstamp == 0) {
            memset(stamp, 0, sizeof(stamp));
            curstamp = 1;
        }
        int head = 0, tail = 0;
        qbuf[tail++] = s;
        stamp[s] = curstamp;
        lvl[s] = 0;
        while (head < tail) {
            int u = qbuf[head++];
            if (lvl[u] >= DIAM) continue;
            int du = g->dg[u];
            for (int k = 0; k < du; k++) {
                int v = g->adj[u][k];
                if (stamp[v] != curstamp) {
                    stamp[v] = curstamp;
                    lvl[v] = lvl[u] + 1;
                    qbuf[tail++] = v;
                }
            }
        }
        total += n - tail;
    }
    return total;
}

/* 2-colour the graph; returns 0 if it is not bipartite. */
static int color_graph(const G *g) {
    int n = g->n;
    for (int i = 0; i < n; i++) side[i] = -1;
    for (int s = 0; s < n; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int head = 0, tail = 0;
        qbuf[tail++] = s;
        while (head < tail) {
            int u = qbuf[head++];
            for (int k = 0; k < g->dg[u]; k++) {
                int v = g->adj[u][k];
                if (side[v] < 0) {
                    side[v] = 1 - side[u];
                    qbuf[tail++] = v;
                } else if (side[v] == side[u]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

static int read_input(void) {
    int n, m;
    if (scanf("%d %d", &n, &m) != 2) return 0;
    if (n <= 0 || n > MAXN - 8 || m < 0) return 0;
    memset(&cur, 0, sizeof(G));
    cur.n = n;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return 0;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) return 0;
        if (cur.dg[u] >= DEG || cur.dg[v] >= DEG) return 0;
        if (has_edge(&cur, u, v)) return 0;
        add_edge(&cur, u, v);
    }
    return 1;
}

/* Swap: a-b and c-e (a,c on side 0) become a-e and c-b. Degrees are preserved. */
static int move_swap(void) {
    int n = cur.n;
    int a = -1, c = -1;
    for (int t = 0; t < 200 && a < 0; t++) {
        int v = rndi(n);
        if (side[v] == 0 && cur.dg[v] > 0) a = v;
    }
    for (int t = 0; t < 200 && c < 0; t++) {
        int v = rndi(n);
        if (side[v] == 0 && cur.dg[v] > 0 && v != a) c = v;
    }
    if (a < 0 || c < 0) return 0;
    int b = cur.adj[a][rndi(cur.dg[a])];
    int e = cur.adj[c][rndi(cur.dg[c])];
    if (b == e) return 0;
    if (has_edge(&cur, a, e) || has_edge(&cur, c, b)) return 0;
    rem_edge(&cur, a, b);
    rem_edge(&cur, c, e);
    add_edge(&cur, a, e);
    add_edge(&cur, c, b);
    return 1;
}

/* Shift: give a spare vertex x (side s) an edge to y (other side). If y is full,
   first drop one of y's edges, which frees capacity on that neighbour. */
static int move_shift(void) {
    int n = cur.n;
    int s = rndi(2);
    int x = -1;
    for (int t = 0; t < 300 && x < 0; t++) {
        int v = rndi(n);
        if (side[v] == s && cur.dg[v] < DEG) x = v;
    }
    if (x < 0) return 0;
    int y = -1;
    for (int t = 0; t < 300 && y < 0; t++) {
        int v = rndi(n);
        if (side[v] == 1 - s && !has_edge(&cur, x, v)) y = v;
    }
    if (y < 0) return 0;
    if (cur.dg[y] < DEG) {
        add_edge(&cur, x, y);
        return 1;
    }
    int z = cur.adj[y][rndi(cur.dg[y])];
    rem_edge(&cur, y, z);
    add_edge(&cur, x, y);
    return 1;
}

/* Add cross-side edges between spare vertices (never increases the cost). */
static void fill_greedy(void) {
    int n = cur.n;
    static int idx0[MAXN], idx1[MAXN];
    int c0 = 0, c1 = 0;
    for (int v = 0; v < n; v++) {
        if (cur.dg[v] < DEG) {
            if (side[v] == 0) idx0[c0++] = v;
            else idx1[c1++] = v;
        }
    }
    shuffle(idx0, c0);
    shuffle(idx1, c1);
    for (int i = 0; i < c0; i++) {
        int a = idx0[i];
        for (int j = 0; j < c1 && cur.dg[a] < DEG; j++) {
            int b = idx1[j];
            if (cur.dg[b] < DEG && !has_edge(&cur, a, b)) add_edge(&cur, a, b);
        }
    }
}

/* kind 0: add one vertex per side; kind 1: side 0 only; kind 2: side 1 only. */
static int grow(int kind) {
    if (kind == 0) {
        if (cur.n + 2 > MAXN) return 0;
        int a = cur.n++;
        int b = cur.n++;
        side[a] = 0;
        side[b] = 1;
        cur.dg[a] = 0;
        cur.dg[b] = 0;
    } else {
        if (cur.n + 1 > MAXN) return 0;
        int a = cur.n++;
        side[a] = kind - 1;
        cur.dg[a] = 0;
    }
    fill_greedy();
    return 1;
}

int main(int argc, char **argv) {
    clock_gettime(CLOCK_MONOTONIC, &t_start);
    if (argc < 5) {
        printf("0 0\n");
        return 0;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t seed = (uint64_t)strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs ^= (seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    if (DEG < 1 || DEG > MAXD || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    if (!read_input()) {
        printf("0 0\n");
        return 0;
    }
    if (!color_graph(&cur) || cost_of(&cur) != 0) {
        printf("0 0\n");
        return 0;
    }
    best = cur;

    while (elapsed() < budget) {
        int kind = (rndd() < 0.6) ? 0 : 1 + rndi(2);
        cur = best;
        if (!grow(kind)) break;
        long long c = cost_of(&cur);
        int ok = (c == 0);
        double T = 1.0;
        for (int it = 0; it < STAGE_ITERS && !ok; it++) {
            if ((it & 15) == 0 && elapsed() >= budget) break;
            sv = cur;
            int mv = (rndd() < 0.5) ? move_swap() : move_shift();
            if (!mv) continue;
            long long c2 = cost_of(&cur);
            long long delta = c2 - c;
            if (delta <= 0 || rndd() < exp(-(double)delta / T)) {
                c = c2;
            } else {
                cur = sv;
            }
            if (c == 0) ok = 1;
            T *= 0.999;
            if (T < 0.15) T = 0.15;
        }
        if (ok) best = cur;
    }

    int m = 0;
    for (int v = 0; v < best.n; v++)
        for (int k = 0; k < best.dg[v]; k++)
            if (best.adj[v][k] > v) m++;
    printf("%d %d\n", best.n, m);
    for (int v = 0; v < best.n; v++)
        for (int k = 0; k < best.dg[v]; k++)
            if (best.adj[v][k] > v) printf("%d %d\n", v, best.adj[v][k]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions: arc-extended projective plane incidence graphs (D = 3)
# and the generalized quadrangle W(q) (D = 4). These form the start graph.
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
    """Old PG incidence plus a new A vertex per P in S (joined to lines through P)
    and a new B vertex per j in S (joined to points on line j). Diameter 3."""
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
    """Return a list of (n, edges) candidates, one per prime power q with q + 1 <= d."""
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
        cands = [[]]
        if s >= 1:
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 40, deadline))
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
    """W(q) for the largest prime power q <= min(d - 1, 7), for speed."""
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()

    def left():
        return time_limit - (time.monotonic() - t0)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    if not lib.is_valid(best[0], best[1], d, D):
        best = (1, [])

    def consider(cand):
        nonlocal best
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        rng = random.Random(seed * 7919 + d)
        for cand in _arc_extensions(d, t0 + 0.25 * time_limit, rng):
            consider(cand)

    if D >= 4 and left() > 0.4 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq)

    # Local search in C, started from the best valid graph found so far.
    remaining = left() - 4.0  # margin for compilation and process start-up
    if remaining >= 2.0:
        budget = max(0.5, 0.85 * remaining)
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                            stdin_graph=best, timeout=remaining)
            consider(lib.parse_graph_text(out))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = (1, [])
    return best
