import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: insertion-repair annealing with bitset distance certificates.
#
# The graph is kept bipartite and valid at every accepted step. Distances are
# checked exactly with bitsets: ball_k(v) is the set of vertices within
# distance k of v, and the cost is the number of ordered pairs at distance > D.
# A new vertex is inserted on the smaller colour class, joined to d vertices of
# the other class (saturated ones lose one random edge). Simulated annealing
# with degree-preserving 2-switches and "slide" moves (which move spare degree
# around) then tries to restore cost 0. Successful insertions are kept, failed
# attempts are rolled back to the last valid snapshot.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1200
#define MAXD 64
#define WMAX 19
#define LOGMAX 200000
#define ITERS 2500

typedef uint64_t row_t[WMAX];
typedef struct { int type; int u; int v; } op_t;

static int dmax = 0;
static int DIAM = 0;
static int n = 0;
static int adj[MAXN][MAXD];
static int deg[MAXN];
static int side[MAXN];

static int snap_n = 0;
static int snap_adj[MAXN][MAXD];
static int snap_deg[MAXN];
static int snap_side[MAXN];

static row_t BA[MAXN];
static row_t BB[MAXN];

static op_t oplog[LOGMAX];
static int logn = 0;

static long long cur_cost = 0;
static double temp = 1.0;
static double deadline = 1.0;
static clock_t t_begin;

static uint64_t rng_state = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return rng_state;
}
static int rnd(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double elapsed(void) { return (double)(clock() - t_begin) / CLOCKS_PER_SEC; }

static int has_edge(int u, int v) {
    for (int i = 0; i < deg[u]; i++) if (adj[u][i] == v) return 1;
    return 0;
}

static void raw_rem1(int u, int v) {
    for (int i = 0; i < deg[u]; i++) {
        if (adj[u][i] == v) { adj[u][i] = adj[u][deg[u] - 1]; deg[u]--; return; }
    }
}
static void raw_add(int u, int v) {
    adj[u][deg[u]++] = v;
    adj[v][deg[v]++] = u;
}
static void raw_rem(int u, int v) { raw_rem1(u, v); raw_rem1(v, u); }

static void log_op(int type, int u, int v) {
    if (logn < LOGMAX) { oplog[logn].type = type; oplog[logn].u = u; oplog[logn].v = v; }
    logn++;
}
static void do_add(int u, int v) { raw_add(u, v); log_op(1, u, v); }
static void do_rem(int u, int v) { raw_rem(u, v); log_op(0, u, v); }

static void undo_all(void) {
    while (logn > 0) {
        logn--;
        op_t o = oplog[logn];
        if (o.type == 1) raw_rem(o.u, o.v); else raw_add(o.u, o.v);
    }
}

static int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Number of ordered pairs (v,x) with dist(v,x) > DIAM. Zero means valid. */
static long long cost_fn(void) {
    int nw = (n + 63) >> 6;
    row_t *cu = BA, *nx = BB;
    for (int v = 0; v < n; v++) {
        memset(cu[v], 0, sizeof(row_t));
        cu[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int step = 0; step < DIAM; step++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nx[v];
            memcpy(dst, cu[v], sizeof(uint64_t) * (size_t)nw);
            for (int i = 0; i < deg[v]; i++) {
                const uint64_t *src = cu[adj[v][i]];
                for (int k = 0; k < nw; k++) dst[k] |= src[k];
            }
        }
        row_t *t = cu; cu = nx; nx = t;
    }
    long long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int k = 0; k < nw; k++) c += popc64(cu[v][k]);
        bad += n - c;
    }
    return bad;
}

/* Add cross edges between spare-capacity vertices of opposite sides (never hurts validity). */
static void fill_pass(void) {
    static int A[MAXN], B[MAXN];
    int na = 0, nb = 0;
    for (int v = 0; v < n; v++) {
        if (deg[v] < dmax) { if (side[v] == 0) A[na++] = v; else B[nb++] = v; }
    }
    if (na == 0 || nb == 0) return;
    if ((long long)na * nb > 40000) return;
    for (int i = 0; i < na; i++) {
        int a = A[i];
        for (int j = 0; j < nb && deg[a] < dmax; j++) {
            int b = B[j];
            if (deg[b] < dmax && !has_edge(a, b) && logn < LOGMAX - 1000) do_add(a, b);
        }
    }
}

static int rand_edge(int *ra, int *rb) {
    for (int t = 0; t < 64; t++) {
        int v = rnd(n);
        if (deg[v] == 0) continue;
        int u = adj[v][rnd(deg[v])];
        if (side[v] == 0) { *ra = v; *rb = u; } else { *ra = u; *rb = v; }
        return 1;
    }
    return 0;
}

/* Degree-preserving 2-switch: (a,b),(c,e) -> (a,e),(c,b), a,c on side 0. */
static int propose_switch(void) {
    int a, b, c, e;
    if (!rand_edge(&a, &b)) return 0;
    if (!rand_edge(&c, &e)) return 0;
    if (a == c || b == e) return 0;
    if (has_edge(a, e) || has_edge(c, b)) return 0;
    do_rem(a, b);
    do_rem(c, e);
    do_add(a, e);
    do_add(c, b);
    return 1;
}

/* Slide: a spare-capacity vertex x takes an edge from a neighbour c (same side), so spare moves to c. */
static int propose_slide(void) {
    int x = -1;
    for (int t = 0; t < 64 && x < 0; t++) {
        int v = rnd(n);
        if (deg[v] < dmax) x = v;
    }
    if (x < 0) return 0;
    int s = side[x];
    for (int t = 0; t < 64; t++) {
        int a, b;
        if (!rand_edge(&a, &b)) return 0;
        int c = (s == 0) ? a : b;
        int e = (s == 0) ? b : a;
        if (c == x || has_edge(x, e)) continue;
        do_rem(c, e);
        do_add(x, e);
        return 1;
    }
    return 0;
}

static void sa_step(void) {
    logn = 0;
    int ok;
    if (rnd(2) == 0) {
        ok = propose_switch();
    } else {
        ok = propose_slide();
        if (!ok) ok = propose_switch();
    }
    if (!ok) { logn = 0; return; }
    fill_pass();
    long long c2 = cost_fn();
    long long delta = c2 - cur_cost;
    if (delta <= 0 || rnd01() < exp(-(double)delta / temp)) {
        cur_cost = c2;
        logn = 0;
    } else {
        undo_all();
    }
}

static void anneal(int iters, double t0, double t1) {
    for (int it = 0; it < iters && cur_cost > 0; it++) {
        if ((it & 31) == 0 && elapsed() > deadline) break;
        temp = t0 * pow(t1 / t0, (double)it / (double)iters);
        sa_step();
    }
}

static void save_snapshot(void) {
    snap_n = n;
    for (int v = 0; v < n; v++) {
        snap_deg[v] = deg[v];
        snap_side[v] = side[v];
        memcpy(snap_adj[v], adj[v], sizeof(int) * (size_t)deg[v]);
    }
}

static void restore_snapshot(void) {
    n = snap_n;
    for (int v = 0; v < n; v++) {
        deg[v] = snap_deg[v];
        side[v] = snap_side[v];
        memcpy(adj[v], snap_adj[v], sizeof(int) * (size_t)deg[v]);
    }
    cur_cost = 0;
}

/* Insert a vertex on the smaller side, joined to dmax vertices of the other side. */
static int grow_once(void) {
    if (n + 2 >= MAXN) return 0;
    int c0 = 0, c1 = 0;
    for (int v = 0; v < n; v++) { if (side[v] == 0) c0++; else c1++; }
    int s;
    if (c0 < c1) s = 0;
    else if (c1 < c0) s = 1;
    else s = rnd(2);
    int opp = 1 - s;
    static int O[MAXN], ord[MAXN];
    int no = 0;
    for (int v = 0; v < n; v++) if (side[v] == opp) O[no++] = v;
    if (no < dmax) return 0;
    for (int i = no - 1; i > 0; i--) {
        int j = rnd(i + 1);
        int t = O[i]; O[i] = O[j]; O[j] = t;
    }
    int k = 0;
    for (int i = 0; i < no; i++) if (deg[O[i]] < dmax) ord[k++] = O[i];
    for (int i = 0; i < no; i++) if (deg[O[i]] >= dmax) ord[k++] = O[i];
    int w = n;
    n++;
    side[w] = s;
    deg[w] = 0;
    for (int i = 0; i < dmax; i++) {
        int b = ord[i];
        if (deg[b] >= dmax) {
            int a = adj[b][rnd(deg[b])];
            raw_rem(a, b);
        }
        raw_add(w, b);
    }
    return 1;
}

static int read_input(void) {
    int nn = 0, mm = 0;
    if (scanf("%d %d", &nn, &mm) != 2) return 0;
    if (nn <= 0 || nn >= MAXN - 4 || mm < 0) return 0;
    n = nn;
    for (int v = 0; v < n; v++) deg[v] = 0;
    for (int i = 0; i < mm; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return 0;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) return 0;
        if (deg[u] >= dmax || deg[v] >= dmax) return 0;
        if (has_edge(u, v)) return 0;
        raw_add(u, v);
    }
    static int queue[MAXN];
    for (int v = 0; v < n; v++) side[v] = -1;
    for (int s = 0; s < n; s++) {
        if (side[s] != -1) continue;
        side[s] = 0;
        int qh = 0, qt = 0;
        queue[qt++] = s;
        while (qh < qt) {
            int u = queue[qh++];
            for (int i = 0; i < deg[u]; i++) {
                int w = adj[u][i];
                if (side[w] == -1) { side[w] = 1 - side[u]; queue[qt++] = w; }
                else if (side[w] == side[u]) return 0;
            }
        }
    }
    return 1;
}

static void build_kdd(void) {
    n = 2 * dmax;
    for (int v = 0; v < n; v++) { deg[v] = 0; side[v] = (v < dmax) ? 0 : 1; }
    for (int i = 0; i < dmax; i++)
        for (int j = 0; j < dmax; j++) raw_add(i, dmax + j);
}

static void print_graph(void) {
    long long m = 0;
    for (int v = 0; v < n; v++)
        for (int i = 0; i < deg[v]; i++) if (adj[v][i] > v) m++;
    printf("%d %lld\n", n, m);
    for (int v = 0; v < n; v++)
        for (int i = 0; i < deg[v]; i++)
            if (adj[v][i] > v) printf("%d %d\n", v, adj[v][i]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 0;
    dmax = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = (uint64_t)atoll(argv[3]);
    rng_state ^= (sd + 1) * 0x9E3779B97F4A7C15ULL;
    if (rng_state == 0) rng_state = 1;
    double budget = atof(argv[4]);
    t_begin = clock();
    deadline = budget * 0.9 - 0.15;
    if (deadline < 0.2) deadline = 0.2;
    if (dmax < 1 || dmax > MAXD || DIAM < 2) { printf("0 0\n"); return 0; }

    if (!read_input()) build_kdd();
    cur_cost = cost_fn();
    if (cur_cost != 0) {
        anneal(20000, 2.0, 0.2);
        if (cur_cost != 0) { build_kdd(); cur_cost = cost_fn(); }
    }
    save_snapshot();

    while (elapsed() < deadline) {
        if (!grow_once()) break;
        cur_cost = cost_fn();
        anneal(ITERS, 2.0, 0.2);
        if (cur_cost == 0) save_snapshot();
        else restore_snapshot();
    }
    if (cur_cost != 0) restore_snapshot();
    print_graph();
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q) (points 0..m-1, lines m..2m-1).
# Every old vertex has degree q+1, so with d >= q+1 it has spare capacity
# s = d - q - 1. Choose a point set S such that every line contains at most s
# points of S and every point lies on at most s lines indexed by S. For each
# P in S add a new A-vertex joined to the q+1 lines through P; for each j in S
# add a new B-vertex joined to the q+1 points on line j.
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
# Greedy vertex insertion with ball-cover certificates (Python, quick pass).
# ----------------------------------------------------------------------------

def _side_colors(n, adj):
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
    return color


def _ball_masks(n, adj, R):
    """Bitmask of all vertices within distance R of each vertex."""
    reach = [1 << v for v in range(n)]
    for _ in range(R):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return reach


def _augment(n, edges, d, D, rng, deadline, max_fails=60):
    """Greedily insert vertices whose neighbourhoods cover the graph within D. Returns (n, edges)."""
    if n == 0 or D < 2:
        return n, list(edges)
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    color = _side_colors(n, adj)
    R = D - 1
    fails = 0
    while time.monotonic() < deadline and fails < max_fails:
        balls = _ball_masks(n, adj, R)
        full = (1 << n) - 1
        added = False
        sides = [0, 1]
        rng.shuffle(sides)
        for side in sides:
            base_cand = [u for u in range(n) if color[u] == 1 - side and len(adj[u]) < d]
            if not base_cand:
                continue
            for _attempt in range(4):
                cand = base_cand[:]
                rng.shuffle(cand)
                covered = 0
                chosen = []
                pool = cand
                while covered != full and len(chosen) < d and pool:
                    best_gain, bu, bi = 0, None, -1
                    for i, u in enumerate(pool):
                        g = (balls[u] & ~covered).bit_count()
                        if g > best_gain:
                            best_gain, bu, bi = g, u, i
                    if bu is None:
                        break
                    chosen.append(bu)
                    covered |= balls[bu]
                    pool = pool[:bi] + pool[bi + 1:]
                if covered == full:
                    w = n
                    n += 1
                    adj.append(set())
                    color.append(side)
                    for u in chosen:
                        adj[u].add(w)
                        adj[w].add(u)
                    added = True
                    break
            if added:
                break
        if added:
            fails = 0
            continue
        fails += 1
        spare_a = [u for u in range(n) if len(adj[u]) < d and color[u] == 0]
        spare_b = [u for u in range(n) if len(adj[u]) < d and color[u] == 1]
        if spare_a and spare_b:
            for _ in range(20):
                u = rng.choice(spare_a)
                v = rng.choice(spare_b)
                if u != v and v not in adj[u]:
                    adj[u].add(v)
                    adj[v].add(u)
                    break
    out = [(u, v) for u in range(n) for v in adj[u] if u < v]
    return n, out


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
# Simulated annealing over bi-Cayley voltage lifts (used for D != 3).
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    for _ in range(80):
        k2 = rng.choice([1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12])
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in rng.sample(range(1, m), min(m - 1, 60))
                     if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def _right_perm(mul, G, s):
    """Permutation g -> mul(g, s) of the group."""
    return [mul(g, s) for g in range(G)]


def _cost(k, G, D, darts, perms):
    """Number of (representative, vertex) pairs not reached within distance D. Zero means valid."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        base_a = i * G
        base_b = (k + j) * G
        for g in range(G):
            a = base_a + g
            b = base_b + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in reps:
        seen = [False] * N
        seen[src] = True
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = True
                        nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - count
    return total


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    """Simulated annealing over voltages and per-layer B-assignments."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

    T = 1.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.997)

        if rng.random() < 0.7 or k == 1:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_perm = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = _right_perm(mul, G, new_s)
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_perm
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _edges(k, G, darts, perms)
    return None


def _c_refine(d, D, seed, graph, budget):
    """Run the C insertion-repair engine from `graph` for about `budget` seconds."""
    out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"], stdin_graph=graph,
                    timeout=budget + 1.0)
    return lib.parse_graph_text(out)


def build(d, D, seed, time_limit):
    start = time.monotonic()
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

    # Arc-extended projective plane graphs (diameter 3), then a quick greedy insertion.
    if D >= 3:
        arcs = _arc_extensions(d, start + 0.08 * time_limit, random.Random(seed * 7919 + d))
        arcs.sort(key=lambda t: -t[0])
        for n_c, e_c in arcs[:3]:
            consider(n_c, e_c)
        if arcs:
            n_a, e_a = arcs[0]
            n2, e2 = _augment(n_a, e_a, d, D, rng, start + 0.15 * time_limit)
            consider(n2, e2)

    if D >= 4 and time.monotonic() < start + 0.20 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Annealed group voltage lifts, for cases other than D = 3.
    if D != 3:
        search_end = start + 0.40 * time_limit
        ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
        while time.monotonic() < search_end:
            k = rng.choice(ks)
            base = best_n // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, search_end, iters=400)
            if res is not None:
                consider(res[0], res[1])

    # C insertion-repair search from the best valid graph found so far.
    if D >= 2:
        c_budget = start + 0.80 * time_limit - time.monotonic() - 1.0  # margin for compilation
        if c_budget > 1.0:
            try:
                n_c, e_c = _c_refine(d, D, seed, best, c_budget)
                consider(n_c, e_c)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
