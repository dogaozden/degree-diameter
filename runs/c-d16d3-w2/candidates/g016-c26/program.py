import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q). Each old vertex has degree q+1,
# so with d >= q+1 it has spare capacity s = d - q - 1. Choose a point set S
# with every line holding <= s points of S and every point on <= s lines
# indexed by S. For each P in S add a new A-vertex joined to the q+1 lines
# through P; for each j in S add a new B-vertex joined to the q+1 points on j.
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
# C engine: growth annealing on bipartite graphs with exact diameter cost.
#
# State: a bipartite graph on N vertices with max degree d. Cost = number of
# unordered vertex pairs at distance > D (bitset BFS). Moves keep the bipartition
# and the degree cap: 2-switch, endpoint rewire, add, and rare remove. Annealing
# with cyclic temperature. Whenever cost hits 0 the graph is recorded and a new
# isolated vertex is appended, so the search keeps pushing the order upward.
# The output is the largest zero-cost graph seen, or the input if none is better.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1200
#define MAXW ((MAXN + 63) / 64)

static int d_, D_, N, W;
static int *adj, *deg;
static unsigned char *adjm;
static int side_[MAXN];
static uint64_t bufA[MAXN][MAXW];
static uint64_t bufB[MAXN][MAXW];
static uint64_t rs;
static int opk[8], opu[8], opv[8], nops;
static int *bestE;
static int bestNv = -1, bestM = 0;

static uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void remove_nb(int u, int v) {
    int *a = adj + (size_t)u * d_;
    for (int k = 0; k < deg[u]; k++) {
        if (a[k] == v) {
            a[k] = a[deg[u] - 1];
            deg[u]--;
            return;
        }
    }
}

static void edge_add(int u, int v) {
    adj[(size_t)u * d_ + deg[u]++] = v;
    adj[(size_t)v * d_ + deg[v]++] = u;
    adjm[u * MAXN + v] = 1;
    adjm[v * MAXN + u] = 1;
}

static void edge_del(int u, int v) {
    remove_nb(u, v);
    remove_nb(v, u);
    adjm[u * MAXN + v] = 0;
    adjm[v * MAXN + u] = 0;
}

static void do_op(int kind, int u, int v) {
    opk[nops] = kind; opu[nops] = u; opv[nops] = v; nops++;
    if (kind == 0) edge_add(u, v); else edge_del(u, v);
}

static void undo_ops(void) {
    while (nops > 0) {
        nops--;
        if (opk[nops] == 0) edge_del(opu[nops], opv[nops]);
        else edge_add(opu[nops], opv[nops]);
    }
}

static long eval_cost(void) {
    W = (N + 63) / 64;
    uint64_t (*cur)[MAXW] = bufA;
    uint64_t (*nxt)[MAXW] = bufB;
    for (int v = 0; v < N; v++) {
        for (int k = 0; k < W; k++) cur[v][k] = 0;
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int s = 0; s < D_; s++) {
        for (int v = 0; v < N; v++) {
            for (int k = 0; k < W; k++) nxt[v][k] = cur[v][k];
            const int *a = adj + (size_t)v * d_;
            for (int i = 0; i < deg[v]; i++) {
                const uint64_t *src = cur[a[i]];
                for (int k = 0; k < W; k++) nxt[v][k] |= src[k];
            }
        }
        uint64_t (*t)[MAXW] = cur;
        cur = nxt;
        nxt = t;
    }
    long bad = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int k = 0; k < W; k++) c += popc64(cur[v][k]);
        bad += N - c;
    }
    return bad / 2;
}

static void record(void) {
    int m = 0;
    for (int u = 0; u < N; u++) {
        for (int k = 0; k < deg[u]; k++) {
            int v = adj[(size_t)u * d_ + k];
            if (u < v) {
                bestE[2 * m] = u;
                bestE[2 * m + 1] = v;
                m++;
            }
        }
    }
    bestNv = N;
    bestM = m;
}

static void grow(void) {
    int c0 = 0;
    for (int v = 0; v < N; v++) if (side_[v] == 0) c0++;
    side_[N] = (c0 <= N - c0) ? 0 : 1;
    deg[N] = 0;
    N++;
}

static int pick_edge(int *a, int *b) {
    for (int t = 0; t < 64; t++) {
        int u = rndint(N);
        if (deg[u] == 0) continue;
        int v = adj[(size_t)u * d_ + rndint(deg[u])];
        if (side_[u] == 0) { *a = u; *b = v; }
        else { *a = v; *b = u; }
        return 1;
    }
    return 0;
}

/* a in side 0, b in side 1 for every pick. */
static int mv_swap(void) {
    int a, b, c, e;
    if (!pick_edge(&a, &b) || !pick_edge(&c, &e)) return 0;
    if (a == c || b == e) return 0;
    if (adjm[a * MAXN + e] || adjm[c * MAXN + b]) return 0;
    do_op(1, a, b);
    do_op(1, c, e);
    do_op(0, a, e);
    do_op(0, c, b);
    return 1;
}

static int mv_rewire(void) {
    int a, b;
    if (!pick_edge(&a, &b)) return 0;
    if (rnd64() & 1ULL) {
        int x = -1;
        for (int t = 0; t < 32; t++) {
            int c = rndint(N);
            if (side_[c] == 1 && c != b && deg[c] < d_ && !adjm[a * MAXN + c]) { x = c; break; }
        }
        if (x < 0) return 0;
        do_op(1, a, b);
        do_op(0, a, x);
    } else {
        int y = -1;
        for (int t = 0; t < 32; t++) {
            int c = rndint(N);
            if (side_[c] == 0 && c != a && deg[c] < d_ && !adjm[c * MAXN + b]) { y = c; break; }
        }
        if (y < 0) return 0;
        do_op(1, a, b);
        do_op(0, y, b);
    }
    return 1;
}

static int mv_add(void) {
    int u = -1, v = -1;
    for (int t = 0; t < 64; t++) {
        int c = rndint(N), e = rndint(N);
        if (side_[c] == 0 && side_[e] == 1 && deg[c] < d_ && deg[e] < d_ && !adjm[c * MAXN + e]) {
            u = c; v = e; break;
        }
    }
    if (u < 0) return 0;
    do_op(0, u, v);
    return 1;
}

static int mv_remove(void) {
    int a, b;
    if (!pick_edge(&a, &b)) return 0;
    do_op(1, a, b);
    return 1;
}

static void print_raw(int n0, int m0, const int *eu, const int *ev) {
    printf("%d %d\n", n0, m0);
    for (int i = 0; i < m0; i++) printf("%d %d\n", eu[i], ev[i]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (rs == 0) rs = 1;
    clock_t c0 = clock();
    time_t t0 = time(NULL);

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { n0 = 0; m0 = 0; }
    if (m0 < 0) m0 = 0;
    int cap = m0 > 1 ? m0 : 1;
    int *eu = malloc(sizeof(int) * cap);
    int *ev = malloc(sizeof(int) * cap);
    int rd = 0;
    for (int i = 0; i < m0; i++) {
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) break;
        rd++;
    }
    m0 = rd;
    if (n0 <= 0 || m0 == 0) {
        n0 = 2; m0 = 1; eu[0] = 0; ev[0] = 1;
    }
    if (d_ < 1 || D_ < 1 || n0 > MAXN - 8) {
        print_raw(n0, m0, eu, ev);
        return 0;
    }
    for (int i = 0; i < m0; i++) {
        if (eu[i] < 0 || ev[i] < 0 || eu[i] >= n0 || ev[i] >= n0) {
            print_raw(n0, m0, eu, ev);
            return 0;
        }
    }

    adj = malloc(sizeof(int) * (size_t)MAXN * d_);
    deg = calloc(MAXN, sizeof(int));
    adjm = calloc((size_t)MAXN * MAXN, 1);
    bestE = malloc(sizeof(int) * 2 * (size_t)MAXN * d_);

    /* 2-colour the input (propagation over edge passes). */
    int *col = malloc(sizeof(int) * n0);
    for (int i = 0; i < n0; i++) col[i] = -1;
    for (int s = 0; s < n0; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int changed = 1;
        while (changed) {
            changed = 0;
            for (int i = 0; i < m0; i++) {
                int u = eu[i], v = ev[i];
                if (col[u] >= 0 && col[v] < 0) { col[v] = 1 - col[u]; changed = 1; }
                else if (col[v] >= 0 && col[u] < 0) { col[u] = 1 - col[v]; changed = 1; }
            }
        }
    }
    int good = 1;
    for (int i = 0; i < m0 && good; i++) {
        int u = eu[i], v = ev[i];
        if (u == v || col[u] == col[v] || adjm[u * MAXN + v] || deg[u] >= d_ || deg[v] >= d_) {
            good = 0;
            break;
        }
        edge_add(u, v);
    }
    if (!good) {
        print_raw(n0, m0, eu, ev);
        return 0;
    }
    N = n0;
    for (int v = 0; v < N; v++) side_[v] = col[v] < 0 ? 0 : col[v];

    long cur = eval_cost();
    if (cur == 0) record();

    long iter = 0;
    const long CYC = 50000;
    const double T0 = 1.5, T1 = 0.2;
    while (1) {
        if ((iter & 15) == 0) {
            double ce = (double)(clock() - c0) / CLOCKS_PER_SEC;
            double we = difftime(time(NULL), t0);
            if (ce >= budget || we >= budget) break;
        }
        iter++;
        double ph = (double)(iter % CYC) / (double)CYC;
        double T = T0 * pow(T1 / T0, ph);

        nops = 0;
        int r = rndint(100);
        int moved;
        if (r < 40) moved = mv_swap();
        else if (r < 70) moved = mv_rewire();
        else if (r < 95) moved = mv_add();
        else moved = mv_remove();
        if (!moved) {
            undo_ops();
            continue;
        }
        long nc = eval_cost();
        long delta = nc - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cur = nc;
            nops = 0;
            if (cur == 0) {
                if (N > bestNv) record();
                if (N < MAXN - 1) {
                    grow();
                    cur = eval_cost();
                }
            }
        } else {
            undo_ops();
        }
    }

    if (bestNv >= 1) {
        printf("%d %d\n", bestNv, bestM);
        for (int i = 0; i < bestM; i++) printf("%d %d\n", bestE[2 * i], bestE[2 * i + 1]);
    } else {
        print_raw(n0, m0, eu, ev);
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t_start = time.monotonic()
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

    # Arc-extended projective plane graphs (diameter 3).
    if D >= 3:
        cands = _arc_extensions(d, t_start + 0.15 * time_limit, random.Random(seed * 7919 + d))
        for n_c, e_c in sorted(cands, key=lambda t: -t[0]):
            consider(n_c, e_c)

    # Generalized quadrangle baseline (diameter 4).
    if D >= 4 and time.monotonic() < t_start + 0.2 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Moore bound reached: nothing larger is possible.
    if best_n >= lib.moore_bound(d, D):
        return best

    # Main search: C growth annealing from the best start, using most of the budget.
    budget = time_limit * 0.95 - (time.monotonic() - t_start) - 4.0
    if budget >= 1.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                            stdin_graph=best, timeout=budget + 6.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
