import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q) (points 0..m-1, lines m..2m-1).
# Every old vertex has degree q+1, so with d >= q+1 it has spare capacity
# s = d - q - 1. Choose a point set S such that every line contains at most s
# points of S and every point lies on at most s lines indexed by S. For each P
# in S add a new A-vertex joined to the q+1 lines through P; for each j in S add
# a new B-vertex joined to the q+1 points on line j. The order is 2(q^2+q+1)+2|S|
# and the diameter stays 3.
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
    """Build the extended graph: old PG incidence plus a new A and a new B vertex per element of S."""
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
# C engine: simulated annealing that grows a valid bipartite graph.
#
# Starting from a valid input graph, it repeatedly adds one vertex on the
# opposite side of its neighbours, then anneals degree-preserving 2-switches,
# edge additions and edge removals to drive the number of pairs at distance
# greater than D to zero. Every time it reaches zero it records the graph and
# adds another vertex. The best valid graph is printed.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

static int d_, D_;
static int N, NMAX, W;
static int *deg, *adj, *col;
static int *bdeg, *badj, bestN;
static uint64_t *rA, *rB;
static uint64_t rs = 88172645463325252ULL;

#define ADJ(v, k) adj[(size_t)(v) * (size_t)d_ + (size_t)(k)]

static uint64_t rnd(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndi(int n) { return (int)(rnd() % (uint64_t)n); }
static double rndu(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Number of unordered pairs at distance > D_ (unreachable counts). Zero means valid. */
static long long cost(void) {
    int n = N, w = W;
    uint64_t *cur = rA, *nx = rB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * (size_t)w);
    for (int v = 0; v < n; v++)
        cur[(size_t)v * w + (size_t)(v >> 6)] |= 1ULL << (v & 63);
    for (int r = 0; r < D_; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *o = nx + (size_t)v * w;
            memcpy(o, cur + (size_t)v * w, sizeof(uint64_t) * (size_t)w);
            for (int k = 0; k < deg[v]; k++) {
                const uint64_t *t = cur + (size_t)ADJ(v, k) * w;
                for (int i = 0; i < w; i++) o[i] |= t[i];
            }
        }
        uint64_t *tmp = cur; cur = nx; nx = tmp;
    }
    long long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int i = 0; i < w; i++) c += popc(cur[(size_t)v * w + i]);
        bad += n - c;
    }
    return bad / 2;
}

static int has_edge(int a, int b) {
    for (int k = 0; k < deg[a]; k++)
        if (ADJ(a, k) == b) return 1;
    return 0;
}

static void del_arc(int a, int b) {
    for (int k = 0; k < deg[a]; k++) {
        if (ADJ(a, k) == b) {
            ADJ(a, k) = ADJ(a, deg[a] - 1);
            deg[a]--;
            return;
        }
    }
}

static void add_edge(int a, int b) {
    ADJ(a, deg[a]) = b; deg[a]++;
    ADJ(b, deg[b]) = a; deg[b]++;
}

static void del_edge(int a, int b) {
    del_arc(a, b);
    del_arc(b, a);
}

static int rand_edge(int *pa, int *pb) {
    for (int t = 0; t < 1000; t++) {
        int v = rndi(N);
        if (deg[v] > 0) {
            *pa = v;
            *pb = ADJ(v, rndi(deg[v]));
            return 1;
        }
    }
    return 0;
}

typedef struct { int type, a, b, c, e; } Move;

/* type 0: degree-preserving 2-switch; type 1: add edge; type 2: remove edge. */
static int apply_move(Move *mv, int type) {
    if (type == 0) {
        int a, b, c, e;
        if (!rand_edge(&a, &b)) return 0;
        c = rndi(N);
        if (c == a || col[c] != col[a] || deg[c] == 0) return 0;
        e = ADJ(c, rndi(deg[c]));
        if (has_edge(a, e) || has_edge(c, b)) return 0;
        del_edge(a, b);
        del_edge(c, e);
        add_edge(a, e);
        add_edge(c, b);
        mv->type = 0; mv->a = a; mv->b = b; mv->c = c; mv->e = e;
        return 1;
    }
    if (type == 1) {
        int a = -1, b = -1;
        for (int t = 0; t < 200; t++) {
            int x = rndi(N);
            if (deg[x] >= d_) continue;
            int y = rndi(N);
            if (y == x || col[y] == col[x] || deg[y] >= d_ || has_edge(x, y)) continue;
            a = x; b = y;
            break;
        }
        if (a < 0) return 0;
        add_edge(a, b);
        mv->type = 1; mv->a = a; mv->b = b;
        return 1;
    }
    {
        int a, b;
        if (!rand_edge(&a, &b)) return 0;
        del_edge(a, b);
        mv->type = 2; mv->a = a; mv->b = b;
        return 1;
    }
}

static void undo_move(const Move *mv) {
    if (mv->type == 0) {
        del_edge(mv->a, mv->e);
        del_edge(mv->c, mv->b);
        add_edge(mv->a, mv->b);
        add_edge(mv->c, mv->e);
    } else if (mv->type == 1) {
        del_edge(mv->a, mv->b);
    } else {
        add_edge(mv->a, mv->b);
    }
}

static void add_vertex(void) {
    int x = N;
    N++;
    W = (N + 63) / 64;
    deg[x] = 0;
    col[x] = rndi(2);
    for (int tries = 0; deg[x] < d_ && tries < 50 * N; tries++) {
        int y = rndi(x);
        if (col[y] == col[x] || deg[y] >= d_ || has_edge(x, y)) continue;
        add_edge(x, y);
    }
}

static void record_best(void) {
    bestN = N;
    memcpy(bdeg, deg, sizeof(int) * (size_t)N);
    memcpy(badj, adj, sizeof(int) * (size_t)N * (size_t)d_);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    rs = (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) n0 = 0;
    if (n0 <= 0 || d_ < 1) {
        printf("0 0\n");
        return 0;
    }
    NMAX = n0 + 256;
    int WM = (NMAX + 63) / 64;
    deg = calloc((size_t)NMAX, sizeof(int));
    col = calloc((size_t)NMAX, sizeof(int));
    adj = calloc((size_t)NMAX * (size_t)d_, sizeof(int));
    bdeg = calloc((size_t)NMAX, sizeof(int));
    badj = calloc((size_t)NMAX * (size_t)d_, sizeof(int));
    rA = calloc((size_t)NMAX * (size_t)WM, sizeof(uint64_t));
    rB = calloc((size_t)NMAX * (size_t)WM, sizeof(uint64_t));
    int *q = calloc((size_t)NMAX, sizeof(int));

    N = n0;
    W = (N + 63) / 64;
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= n0 || v >= n0 || u == v) continue;
        if (deg[u] >= d_ || deg[v] >= d_ || has_edge(u, v)) continue;
        add_edge(u, v);
    }

    for (int v = 0; v < n0; v++) col[v] = -1;
    for (int s = 0; s < n0; s++) {
        if (col[s] != -1) continue;
        col[s] = 0;
        int h = 0, t = 0;
        q[t++] = s;
        while (h < t) {
            int v = q[h++];
            for (int k = 0; k < deg[v]; k++) {
                int u = ADJ(v, k);
                if (col[u] == -1) {
                    col[u] = 1 - col[v];
                    q[t++] = u;
                }
            }
        }
    }
    free(q);

    record_best();
    long long cur = cost();
    double T0 = 1.2, T = T0;
    clock_t t0 = clock();
    long long step = 0;
    for (;;) {
        if ((step++ & 63) == 0) {
            double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
            if (el >= tl) break;
        }
        if (cur == 0) {
            if (N > bestN) record_best();
            if (N >= NMAX) break;
            add_vertex();
            cur = cost();
            T = T0;
            continue;
        }
        double r = rndu();
        int type = r < 0.6 ? 0 : (r < 0.85 ? 1 : 2);
        Move mv;
        if (!apply_move(&mv, type)) continue;
        long long nc = cost();
        long long delta = nc - cur;
        if (delta <= 0 || rndu() < exp(-(double)delta / T)) {
            cur = nc;
        } else {
            undo_move(&mv);
        }
        T *= 0.9995;
        if (T < 0.05) T = T0;
    }
    if (cur == 0 && N > bestN) record_best();

    long long m2 = 0;
    for (int v = 0; v < bestN; v++) m2 += bdeg[v];
    printf("%d %lld\n", bestN, m2 / 2);
    for (int v = 0; v < bestN; v++) {
        for (int k = 0; k < bdeg[v]; k++) {
            int u = badj[(size_t)v * (size_t)d_ + (size_t)k];
            if (v < u) printf("%d %d\n", v, u);
        }
    }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Build.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()

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

    constructive_deadline = start + 0.3 * time_limit

    # Constructions: arc-extended projective planes (D >= 3) and W(q) (D >= 4).
    if D >= 3:
        import random
        cands = _arc_extensions(d, constructive_deadline, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, e_c in cands:
            consider(n_c, e_c)

    if D >= 4 and time.monotonic() < constructive_deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Search: C annealing grows the best valid graph by adding vertices.
    elapsed = time.monotonic() - start
    budget = 0.8 * time_limit - elapsed
    remaining = time_limit - elapsed
    if budget >= 1.0 and best_n >= 1:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             stdin_graph=best, timeout=max(1.0, remaining - 2.0))
            n2, e2 = lib.parse_graph_text(text)
            consider(n2, e2)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
