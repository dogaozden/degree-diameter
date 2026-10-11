import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bold change: a C annealing engine that tries to grow a valid graph.
#
# Start: the best construction found in Python. For d=16, D=3 this is the
# arc-extended PG(2,13) graph with 394 vertices. Note that the conic is already
# the largest set S allowed by the load condition when s = d-q-1 = 2 (an arc),
# so this Python family cannot exceed 394 for d=16. Records beyond it need a
# different structure, so the C engine searches for one directly.
#
# C engine: keep a valid graph, add a few vertices, and run simulated annealing
# with moves that keep bipartiteness and max degree d (2-switches, edge
# insertions, endpoint transfers). Cost = number of vertex pairs at distance > D,
# computed by bitset BFS. Whenever cost reaches 0 the graph is saved and grown
# again. Otherwise the best saved graph is restored and a new attempt starts.
# Python validates the output and keeps the best valid graph as the fallback.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1024
#define MAXW 16
#define MAXD 64
#define MAXE 32768
#define PHASE 80000

typedef uint64_t u64;

static int d, D, N, W;
static int nb[MAXN][MAXD];
static int deg[MAXN];
static u64 adjb[MAXN][MAXW];
static int side[MAXN];
static u64 RA[MAXN][MAXW], RB[MAXN][MAXW];
static u64 rs = 88172645463325252ULL;
static clock_t T_START;

static int BE[MAXE][2];
static int bm = 0, BN = 0;
static int BS[MAXN];

typedef struct { int t, u, v; } Op;
static Op lg[8];
static int nlg = 0;

static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int n) { return (int)(rnd() % (u64)n); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double elapsed_s(void) { return (double)(clock() - T_START) / (double)CLOCKS_PER_SEC; }

static int isadj(int u, int v) { return (int)((adjb[u][v >> 6] >> (v & 63)) & 1ULL); }

static void add_edge(int u, int v) {
    nb[u][deg[u]++] = v;
    nb[v][deg[v]++] = u;
    adjb[u][v >> 6] |= 1ULL << (v & 63);
    adjb[v][u >> 6] |= 1ULL << (u & 63);
}

static void rm_from(int u, int v) {
    for (int i = 0; i < deg[u]; i++) {
        if (nb[u][i] == v) { nb[u][i] = nb[u][--deg[u]]; return; }
    }
}

static void del_edge(int u, int v) {
    rm_from(u, v);
    rm_from(v, u);
    adjb[u][v >> 6] &= ~(1ULL << (v & 63));
    adjb[v][u >> 6] &= ~(1ULL << (u & 63));
}

static void do_add(int u, int v) { add_edge(u, v); lg[nlg].t = 0; lg[nlg].u = u; lg[nlg].v = v; nlg++; }
static void do_del(int u, int v) { del_edge(u, v); lg[nlg].t = 1; lg[nlg].u = u; lg[nlg].v = v; nlg++; }

static void undo_all(void) {
    while (nlg > 0) {
        Op o = lg[--nlg];
        if (o.t == 0) del_edge(o.u, o.v);
        else add_edge(o.u, o.v);
    }
}

static int popc(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Number of unordered pairs at distance > D (including unreachable pairs). */
static long long bad_cost(void) {
    u64 (*cur)[MAXW] = RA;
    u64 (*nxt)[MAXW] = RB;
    int w = W;
    for (int v = 0; v < N; v++) {
        for (int k = 0; k < w; k++) cur[v][k] = 0;
        cur[v][v >> 6] |= 1ULL << (v & 63);
        for (int i = 0; i < deg[v]; i++) {
            int u = nb[v][i];
            cur[v][u >> 6] |= 1ULL << (u & 63);
        }
    }
    for (int r = 2; r <= D; r++) {
        for (int v = 0; v < N; v++) {
            for (int k = 0; k < w; k++) nxt[v][k] = cur[v][k];
            for (int i = 0; i < deg[v]; i++) {
                int u = nb[v][i];
                for (int k = 0; k < w; k++) nxt[v][k] |= cur[u][k];
            }
        }
        u64 (*t)[MAXW] = cur;
        cur = nxt;
        nxt = t;
    }
    long long miss = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int k = 0; k < w; k++) c += popc(cur[v][k]);
        miss += N - c;
    }
    return miss / 2;
}

static int pick_def(int s) {
    int cnt = 0, pick = -1;
    for (int v = 0; v < N; v++) {
        if (side[v] == s && deg[v] < d) {
            cnt++;
            if (rndint(cnt) == 0) pick = v;
        }
    }
    return pick;
}

static int rand_vertex_with_edge(void) {
    for (int t = 0; t < 50; t++) {
        int v = rndint(N);
        if (deg[v] > 0) return v;
    }
    return -1;
}

/* Degree-preserving 2-switch between side-0 vertex x and side-1 y, and p and q. */
static int move_2switch(void) {
    int a = rand_vertex_with_edge();
    if (a < 0) return 0;
    int b = nb[a][rndint(deg[a])];
    int c = rand_vertex_with_edge();
    if (c < 0) return 0;
    int e = nb[c][rndint(deg[c])];
    int x, y, p, q;
    if (side[a] == 0) { x = a; y = b; } else { x = b; y = a; }
    if (side[c] == 0) { p = c; q = e; } else { p = e; q = c; }
    if (x == p || y == q) return 0;
    if (isadj(x, q) || isadj(p, y)) return 0;
    do_del(x, y);
    do_del(p, q);
    do_add(x, q);
    do_add(p, y);
    return 1;
}

/* Move one endpoint of an edge onto a deficient vertex on the same side. */
static int move_transfer(void) {
    int x = rand_vertex_with_edge();
    if (x < 0) return 0;
    int y = nb[x][rndint(deg[x])];
    int x0 = (side[x] == 0) ? x : y;
    int y1 = (side[x] == 0) ? y : x;
    if (rndint(2) == 0) {
        int a = pick_def(0);
        if (a < 0 || a == x0 || isadj(a, y1)) return 0;
        do_del(x0, y1);
        do_add(a, y1);
    } else {
        int b = pick_def(1);
        if (b < 0 || b == y1 || isadj(x0, b)) return 0;
        do_del(x0, y1);
        do_add(x0, b);
    }
    return 1;
}

/* Insert a new edge between deficient vertices of opposite sides. */
static int move_add(void) {
    for (int t = 0; t < 5; t++) {
        int a = pick_def(0), b = pick_def(1);
        if (a < 0 || b < 0) return 0;
        if (!isadj(a, b)) { do_add(a, b); return 1; }
    }
    return 0;
}

static void grow2(void) {
    for (int t = 0; t < 2; t++) {
        int v = N;
        side[v] = t;
        deg[v] = 0;
        memset(adjb[v], 0, sizeof adjb[v]);
        N++;
    }
    W = (N + 63) / 64;
}

static void snapshot(void) {
    bm = 0;
    for (int v = 0; v < N; v++) {
        for (int i = 0; i < deg[v]; i++) {
            int u = nb[v][i];
            if (u > v && bm < MAXE) { BE[bm][0] = v; BE[bm][1] = u; bm++; }
        }
    }
    BN = N;
    for (int v = 0; v < N; v++) BS[v] = side[v];
}

static void restore(void) {
    for (int v = 0; v < N; v++) {
        deg[v] = 0;
        memset(adjb[v], 0, sizeof adjb[v]);
    }
    N = BN;
    W = (N + 63) / 64;
    for (int v = 0; v < N; v++) side[v] = BS[v];
    for (int i = 0; i < bm; i++) add_edge(BE[i][0], BE[i][1]);
}

int main(int argc, char **argv) {
    static int eu[MAXE], ev[MAXE];
    static int qu[MAXN];
    T_START = clock();
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    double tl = atof(argv[4]);

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2 || n < 1 || n > MAXN - 2 || m < 0 || m > MAXE) {
        printf("0 0\n");
        return 0;
    }
    for (int i = 0; i < m; i++) {
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) { printf("0 0\n"); return 0; }
    }

    int ok = (d >= 1 && d < MAXD && D >= 1);
    N = n;
    W = (N + 63) / 64;
    for (int v = 0; v < N; v++) {
        deg[v] = 0;
        memset(adjb[v], 0, sizeof adjb[v]);
        side[v] = -1;
    }
    for (int i = 0; ok && i < m; i++) {
        int u = eu[i], v = ev[i];
        if (u < 0 || u >= N || v < 0 || v >= N || u == v) ok = 0;
        else if (isadj(u, v) || deg[u] >= d || deg[v] >= d) ok = 0;
        else add_edge(u, v);
    }
    for (int s = 0; ok && s < N; s++) {
        if (side[s] != -1) continue;
        side[s] = 0;
        int h = 0, t = 0;
        qu[t++] = s;
        while (h < t && ok) {
            int v = qu[h++];
            for (int i = 0; i < deg[v]; i++) {
                int u = nb[v][i];
                if (side[u] == -1) { side[u] = 1 - side[v]; qu[t++] = u; }
                else if (side[u] == side[v]) { ok = 0; break; }
            }
        }
    }
    if (ok && bad_cost() != 0) ok = 0;

    if (!ok) {
        printf("%d %d\n", n, m);
        for (int i = 0; i < m; i++) printf("%d %d\n", eu[i], ev[i]);
        return 0;
    }

    snapshot();
    double budget = tl * 0.92 - 0.2;
    const double T0 = 1.5, Tmin = 0.08;

    while (elapsed_s() < budget && N + 2 <= MAXN) {
        grow2();
        long long cost = bad_cost();
        int solved = 0;
        for (int it = 0; it < PHASE; it++) {
            if ((it & 127) == 0 && elapsed_s() >= budget) break;
            double frac = 1.0 - (double)it / (double)PHASE;
            double T = Tmin + (T0 - Tmin) * frac * frac;
            nlg = 0;
            double r = rnd01();
            int applied;
            if (r < 0.5) applied = move_2switch();
            else if (r < 0.8) applied = move_transfer();
            else applied = move_add();
            if (!applied) continue;
            long long c2 = bad_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                undo_all();
            }
            nlg = 0;
            if (cost == 0) { solved = 1; break; }
        }
        if (solved) snapshot();
        else restore();
    }

    printf("%d %d\n", BN, bm);
    for (int i = 0; i < bm; i++) printf("%d %d\n", BE[i][0], BE[i][1]);
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
    """Conic (plus nucleus for even q) as a point-index set."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    """PG incidence plus a new point-side vertex and a new line-side vertex per element of S."""
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


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(cand):
        nonlocal best
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    rng = random.Random(seed * 7919 + d)
    if D >= 3:
        for cand in _arc_extensions(d, t0 + 0.3 * time_limit, rng):
            consider(cand)
    if D >= 4 and time.monotonic() - t0 < 0.3 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq)

    # Bold step: C annealing that tries to grow a valid graph past the Python construction.
    remaining = 0.8 * time_limit - (time.monotonic() - t0)
    if (remaining > 3 and d <= 63 and best[0] <= 900
            and best[0] < lib.moore_bound(d, D)):
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, round(remaining - 1.0, 2)],
                            stdin_graph=best, timeout=remaining + 4)
            consider(lib.parse_graph_text(out))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
