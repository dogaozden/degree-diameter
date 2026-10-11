import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bitset-ball annealing repair (NEW in this version).
#
# The C program takes a valid bipartite graph and repeatedly tries to add one
# more vertex. The new vertex is attached greedily to opposite-side vertices
# that have spare degree, maximising new distance-2 coverage. Then simulated
# annealing repairs the graph with two degree-preserving moves:
#   swap:   (a,b),(a2,b2) -> (a,b2),(a2,b)   (same side pattern, degrees kept)
#   rewire: (a,b) -> (a,b2) with b2 on b's side and spare degree
# Bipartiteness is preserved by construction. The cost is the number of ordered
# vertex pairs at distance > D, computed exactly with radius-D bitset balls.
# On cost 0 the state is saved; otherwise the best saved state is restored.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define NMAX 1536
#define WMAX 24
#define DMAX 64
#define ATTEMPT_ITERS 4000

static int N = 0, DEG_MAX = 3, RAD = 3;
static int adj[NMAX][DMAX];
static int deg[NMAX];
static int side[NMAX];

static int best_N = 0;
static int best_adj[NMAX][DMAX];
static int best_deg[NMAX];
static int best_side[NMAX];

static int snap_adj[NMAX][DMAX];
static int snap_deg[NMAX];

static int covered[NMAX];
static uint64_t ballA[NMAX * WMAX];
static uint64_t ballB[NMAX * WMAX];

static uint64_t rng_state = 88172645463325252ULL;
static double t_begin = 0.0, t_limit = 1.0;

static double now_sec(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int out_of_time(void) {
    return (now_sec() - t_begin) >= t_limit;
}

static uint64_t rnd64(void) {
    rng_state ^= rng_state >> 12;
    rng_state ^= rng_state << 25;
    rng_state ^= rng_state >> 27;
    return rng_state * 2685821657736338717ULL;
}

static int rndint(int k) {
    return (int)(rnd64() % (uint64_t)k);
}

static double rnd01(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}

static int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int a, int b) {
    for (int k = 0; k < deg[a]; k++)
        if (adj[a][k] == b) return 1;
    return 0;
}

static void add_adj(int a, int b) {
    adj[a][deg[a]++] = b;
}

static void del_adj(int a, int b) {
    for (int k = 0; k < deg[a]; k++) {
        if (adj[a][k] == b) {
            adj[a][k] = adj[a][deg[a] - 1];
            deg[a]--;
            return;
        }
    }
}

/* Replace edge (x,y) by (x,y2). Requires (x,y) present and (x,y2) absent. */
static void relink(int x, int y, int y2) {
    del_adj(x, y);
    add_adj(x, y2);
    del_adj(y, x);
    add_adj(y2, x);
}

/* Number of ordered pairs (v,w) with dist(v,w) > RAD. Zero means valid. */
static long long eval_cost(void) {
    int W = (N + 63) / 64;
    uint64_t *cur = ballA, *nxt = ballB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)N * (size_t)W);
    for (int v = 0; v < N; v++)
        cur[(size_t)v * W + (size_t)(v / 64)] |= 1ULL << (v % 64);
    for (int r = 0; r < RAD; r++) {
        for (int v = 0; v < N; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            memcpy(dst, cur + (size_t)v * W, sizeof(uint64_t) * (size_t)W);
            for (int k = 0; k < deg[v]; k++) {
                const uint64_t *src = cur + (size_t)adj[v][k] * W;
                for (int w = 0; w < W; w++) dst[w] |= src[w];
            }
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
    }
    long long bad = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < W; w++)
            c += popc64(cur[(size_t)v * W + w]);
        bad += N - c;
    }
    return bad;
}

static void save_state(void) {
    memcpy(snap_adj, adj, sizeof(adj[0]) * (size_t)N);
    memcpy(snap_deg, deg, sizeof(int) * (size_t)N);
}

static void restore_state(void) {
    memcpy(adj, snap_adj, sizeof(adj[0]) * (size_t)N);
    memcpy(deg, snap_deg, sizeof(int) * (size_t)N);
}

static void save_best(void) {
    best_N = N;
    memcpy(best_adj, adj, sizeof(adj[0]) * (size_t)N);
    memcpy(best_deg, deg, sizeof(int) * (size_t)N);
    memcpy(best_side, side, sizeof(int) * (size_t)N);
}

static void restore_best(void) {
    N = best_N;
    memcpy(adj, best_adj, sizeof(adj[0]) * (size_t)N);
    memcpy(deg, best_deg, sizeof(int) * (size_t)N);
    memcpy(side, best_side, sizeof(int) * (size_t)N);
}

/* Random vertex: side_req (-1 any), mode 1 needs deg>0, mode 2 needs spare degree. */
static int pick_vertex(int side_req, int mode) {
    for (int t = 0; t < 200; t++) {
        int v = rndint(N);
        if (side_req >= 0 && side[v] != side_req) continue;
        if (mode == 1 && deg[v] == 0) continue;
        if (mode == 2 && deg[v] >= DEG_MAX) continue;
        return v;
    }
    return -1;
}

static long long anneal(long long cost, int iters, double T0, double T1) {
    double factor = pow(T1 / T0, 1.0 / (iters > 1 ? iters : 2));
    double T = T0;
    for (int it = 0; it < iters && cost > 0; it++) {
        T *= factor;
        if ((it & 63) == 0 && out_of_time()) break;
        int a = pick_vertex(-1, 1);
        if (a < 0) break;
        int b = adj[a][rndint(deg[a])];
        save_state();
        if (rnd01() < 0.5) {
            int a2 = pick_vertex(side[a], 1);
            if (a2 < 0 || a2 == a) continue;
            int b2 = adj[a2][rndint(deg[a2])];
            if (b2 == b || has_edge(a, b2) || has_edge(a2, b)) continue;
            relink(a, b, b2);
            relink(a2, b2, b);
        } else {
            int b2 = pick_vertex(1 - side[a], 2);
            if (b2 < 0 || b2 == b || has_edge(a, b2)) continue;
            relink(a, b, b2);
        }
        long long c2 = eval_cost();
        long long delta = c2 - cost;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cost = c2;
        } else {
            restore_state();
        }
    }
    return cost;
}

/* Greedy attachment of new vertex x: maximise newly covered same-side vertices. */
static void attach_new(int x) {
    int c = side[x];
    for (int v = 0; v < N; v++) covered[v] = 0;
    covered[x] = 1;
    int chosen = 0;
    while (chosen < DEG_MAX) {
        int bv = -1, bg = 0, ties = 0;
        for (int v = 0; v < N; v++) {
            if (side[v] == c || deg[v] >= DEG_MAX) continue;
            int g = 0;
            for (int k = 0; k < deg[v]; k++)
                if (!covered[adj[v][k]]) g++;
            if (g > bg) {
                bg = g;
                bv = v;
                ties = 1;
            } else if (g == bg && g > 0) {
                ties++;
                if (rndint(ties) == 0) bv = v;
            }
        }
        if (bv < 0) break;
        add_adj(x, bv);
        add_adj(bv, x);
        for (int k = 0; k < deg[bv]; k++)
            covered[adj[bv][k]] = 1;
        chosen++;
    }
}

static int add_vertex(void) {
    if (N + 1 > NMAX) return 0;
    int spare[2] = {0, 0};
    for (int v = 0; v < N; v++)
        if (deg[v] < DEG_MAX) spare[side[v]]++;
    int c = rndint(2);
    if (spare[1 - c] == 0) c = 1 - c;
    if (spare[1 - c] == 0) return 0;
    int x = N;
    N++;
    side[x] = c;
    deg[x] = 0;
    attach_new(x);
    return 1;
}

static int colour_graph(void) {
    static int queue[NMAX];
    for (int v = 0; v < N; v++) side[v] = -1;
    for (int s = 0; s < N; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int qh = 0, qt = 0;
        queue[qt++] = s;
        while (qh < qt) {
            int v = queue[qh++];
            for (int k = 0; k < deg[v]; k++) {
                int u = adj[v][k];
                if (side[u] < 0) {
                    side[u] = 1 - side[v];
                    queue[qt++] = u;
                } else if (side[u] == side[v]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        printf("0 0\n");
        return 0;
    }
    int d = atoi(argv[1]);
    RAD = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    t_limit = atof(argv[4]);
    DEG_MAX = d;
    if (DEG_MAX > DMAX - 2) DEG_MAX = DMAX - 2;
    if (RAD < 1) RAD = 1;
    rng_state = (uint64_t)seed * 2654435761ULL + 0x9E3779B97F4A7C15ULL;
    if (rng_state == 0) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd64();
    t_begin = now_sec();

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) {
        n = 0;
        m = 0;
    }
    if (n < 0 || n > NMAX) {
        printf("0 0\n");
        return 0;
    }
    N = n;
    for (int v = 0; v < N; v++) deg[v] = 0;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= N || v >= N || u == v) continue;
        if (deg[u] >= DEG_MAX || deg[v] >= DEG_MAX || has_edge(u, v)) continue;
        add_adj(u, v);
        add_adj(v, u);
    }
    if (N == 0 || !colour_graph()) {
        printf("0 0\n");
        return 0;
    }

    long long cost = eval_cost();
    if (cost > 0) cost = anneal(cost, 20000, 2.0, 0.1);
    if (cost > 0) {
        printf("0 0\n");
        return 0;
    }
    save_best();

    while (!out_of_time()) {
        if (!add_vertex()) break;
        cost = eval_cost();
        cost = anneal(cost, ATTEMPT_ITERS, 3.0, 0.15);
        if (cost == 0)
            save_best();
        else
            restore_best();
    }
    restore_best();

    int total = 0;
    for (int v = 0; v < N; v++) total += deg[v];
    printf("%d %d\n", N, total / 2);
    for (int v = 0; v < N; v++)
        for (int k = 0; k < deg[v]; k++)
            if (adj[v][k] > v)
                printf("%d %d\n", v, adj[v][k]);
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
# Spare-capacity fill (diameter 3), Python side.
# ----------------------------------------------------------------------------

def _bipartition(n, adj):
    """2-colouring of a bipartite graph given by adjacency lists."""
    col = [-1] * n
    for s in range(n):
        if col[s] != -1:
            continue
        col[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if col[v] == -1:
                    col[v] = 1 - col[u]
                    stack.append(v)
    return col


def _fill(n, edges, d, D, deadline, rng):
    """Greedily add vertices whose neighbourhoods cover the opposite side; return (n, edges)."""
    edges = list(edges)
    fails = 0
    while time.monotonic() < deadline and fails < 400:
        adj = [[] for _ in range(n)]
        for u, v in edges:
            adj[u].append(v)
            adj[v].append(u)
        deg = [len(a) for a in adj]
        col = _bipartition(n, adj)
        c = rng.randrange(2)
        uncovered = {v for v in range(n) if col[v] == 1 - c}
        cand = [v for v in range(n) if col[v] == c and deg[v] < d]
        chosen = []
        chosen_set = set()
        while uncovered and len(chosen) < d:
            best_v = None
            best_key = None
            for v in cand:
                if v in chosen_set:
                    continue
                g = 0
                for u in adj[v]:
                    if u in uncovered:
                        g += 1
                if g == 0:
                    continue
                key = (g, rng.random())
                if best_key is None or key > best_key:
                    best_key = key
                    best_v = v
            if best_v is None:
                break
            chosen.append(best_v)
            chosen_set.add(best_v)
            for u in adj[best_v]:
                uncovered.discard(u)
        if uncovered:
            fails += 1
            continue
        new_edges = edges + [(v, n) for v in chosen]
        if lib.is_valid(n + 1, new_edges, d, D):
            edges = new_edges
            n += 1
            fails = 0
        else:
            fails += 1
    return n, edges


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
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
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
        for n_c, e_c in _arc_extensions(d, t0 + 0.15 * time_limit,
                                        random.Random(seed * 7919 + d)):
            consider(n_c, e_c)

    if D >= 3 and best_n > 2:
        n_f, e_f = _fill(best_n, best[1], d, D, t0 + 0.25 * time_limit,
                         random.Random(seed * 104729 + d))
        consider(n_f, e_f)

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # New: C bitset-annealing repair that adds vertices to the best graph.
    if d <= 60:
        elapsed = time.monotonic() - t0
        budget = 0.8 * time_limit - elapsed - 1.0
        if budget > 1.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                                stdin_graph=best, timeout=0.92 * time_limit - elapsed)
                n_c, e_c = lib.parse_graph_text(out)
                consider(n_c, e_c)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
