"""Diameter-D bipartite graph search: arc-extended projective planes, then C vertex insertion.

Pipeline:
1. Python builds the best construction it can: arc-extended PG(2, q) incidence graphs
   (D >= 3), and the generalized quadrangle W(q) (D >= 4). K_{d,d} is the fallback.
2. A C engine grows the best graph one vertex at a time. Each new vertex is joined to
   up to d opposite-side vertices with spare capacity. A simulated-annealing search over
   edge rewires and additions then drives the number of bad pairs (distance > D) to zero.
   Edge additions never increase distances, so they are always kept when they do not
   worsen the cost. A failed attempt restores the last valid graph.
"""
import itertools
import random
import time

import lib


C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 2048
#define MAXW (MAXN / 64)
#define MAXDEG 128
#define MAXE (MAXN * MAXDEG / 2)
#define ITERS 8000
#define TSTART 2.0
#define TEND 0.05

static int N = 0, DIAM = 3, DEGCAP = 3;
static int col[MAXN];
static int deg[MAXN];
static int nb[MAXN][MAXDEG];
static unsigned char A[MAXN][MAXN];
static uint64_t RA[MAXN][MAXW];
static uint64_t RB[MAXN][MAXW];
static uint64_t rs = 88172645463325252ULL;
static int stk[MAXN];
static int cand[MAXN];
static int snapN = 0, snapM = 0;
static int snapU[MAXE], snapV[MAXE];
static clock_t T_END;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndi(int n) { return (int)(rnd64() % (uint64_t)n); }

static double rndu(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void add_edge(int u, int v) {
    A[u][v] = 1;
    A[v][u] = 1;
    nb[u][deg[u]++] = v;
    nb[v][deg[v]++] = u;
}

static void drop_nb(int u, int v) {
    for (int k = 0; k < deg[u]; k++) {
        if (nb[u][k] == v) {
            nb[u][k] = nb[u][deg[u] - 1];
            deg[u]--;
            return;
        }
    }
}

static void del_edge(int u, int v) {
    A[u][v] = 0;
    A[v][u] = 0;
    drop_nb(u, v);
    drop_nb(v, u);
}

static void clear_graph(void) {
    for (int v = 0; v < N; v++) {
        for (int k = 0; k < deg[v]; k++) A[v][nb[v][k]] = 0;
        deg[v] = 0;
    }
}

static int take_snapshot(int *U, int *V) {
    int m = 0;
    for (int v = 0; v < N; v++) {
        for (int k = 0; k < deg[v]; k++) {
            int u = nb[v][k];
            if (v < u && m < MAXE) {
                U[m] = v;
                V[m] = u;
                m++;
            }
        }
    }
    return m;
}

static void load_edges(int n, const int *U, const int *V, int m) {
    clear_graph();
    N = n;
    for (int v = 0; v < N; v++) deg[v] = 0;
    for (int i = 0; i < m; i++) add_edge(U[i], V[i]);
}

/* Number of unordered pairs at distance > DIAM (unreachable pairs included). */
static long long bad_pairs(void) {
    int W = (N + 63) / 64;
    uint64_t (*cur)[MAXW] = RA;
    uint64_t (*nxt)[MAXW] = RB;
    uint64_t (*tmp)[MAXW];
    for (int v = 0; v < N; v++) {
        for (int w = 0; w < W; w++) cur[v][w] = 0;
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < DIAM; r++) {
        for (int v = 0; v < N; v++) {
            for (int w = 0; w < W; w++) nxt[v][w] = cur[v][w];
            for (int k = 0; k < deg[v]; k++) {
                int u = nb[v][k];
                for (int w = 0; w < W; w++) nxt[v][w] |= cur[u][w];
            }
        }
        tmp = cur;
        cur = nxt;
        nxt = tmp;
    }
    long long tot = 0;
    for (int v = 0; v < N; v++) {
        int cnt = 0;
        for (int w = 0; w < W; w++) cnt += pc64(cur[v][w]);
        tot += N - cnt;
    }
    return tot / 2;
}

/* Insert one vertex on a random side, then anneal until the graph is valid again. */
static int try_grow(void) {
    if (N >= MAXN - 1) return 0;
    int side = rndi(2);
    int nc = 0;
    for (int v = 0; v < N; v++) {
        if (col[v] != side && deg[v] < DEGCAP) cand[nc++] = v;
    }
    if (nc == 0) return 0;
    for (int i = nc - 1; i > 0; i--) {
        int j = rndi(i + 1);
        int t = cand[i];
        cand[i] = cand[j];
        cand[j] = t;
    }
    int w = N;
    N++;
    col[w] = side;
    deg[w] = 0;
    int take = nc < DEGCAP ? nc : DEGCAP;
    for (int i = 0; i < take; i++) add_edge(w, cand[i]);

    long long cost = bad_pairs();
    double fac = pow(TEND / TSTART, 1.0 / ITERS);
    double T = TSTART;
    for (int it = 0; it < ITERS && cost > 0; it++) {
        T *= fac;
        if ((it & 255) == 0 && clock() > T_END) break;
        int mv = rndi(10);
        if (mv < 3) {
            /* Addition: never increases the cost, kept whenever it does not worsen it. */
            int x = rndi(N);
            int z = rndi(N);
            if (col[x] == col[z] || deg[x] >= DEGCAP || deg[z] >= DEGCAP || A[x][z]) continue;
            add_edge(x, z);
            long long c2 = bad_pairs();
            if (c2 <= cost) cost = c2;
            else del_edge(x, z);
        } else {
            /* Rewire: move one end of edge (x,y) to a new partner z on the other side. */
            int x = rndi(N);
            if (deg[x] == 0) continue;
            int y = nb[x][rndi(deg[x])];
            int z = rndi(N);
            if (col[z] == col[x] || z == y || deg[z] >= DEGCAP || A[x][z]) continue;
            del_edge(x, y);
            add_edge(x, z);
            long long c2 = bad_pairs();
            long long dl = c2 - cost;
            if (dl <= 0 || rndu() < exp(-(double)dl / T)) {
                cost = c2;
            } else {
                del_edge(x, z);
                add_edge(x, y);
            }
        }
    }
    return cost == 0;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed budget\n");
        return 1;
    }
    DEGCAP = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    if (DEGCAP < 1) DEGCAP = 1;
    if (DEGCAP > MAXDEG) DEGCAP = MAXDEG;
    if (DIAM < 1) DIAM = 1;
    rs = seed * 2654435761ULL + 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 10; i++) rnd64();

    clock_t t0 = clock();
    T_END = t0 + (clock_t)(budget * CLOCKS_PER_SEC);

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) {
        n = 0;
        m = 0;
    }
    if (n < 1 || n > MAXN - 2 || m < 0) {
        printf("0 0\n");
        return 0;
    }
    N = n;
    for (int i = 0; i < n; i++) {
        deg[i] = 0;
        col[i] = -1;
    }
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || u >= n || v < 0 || v >= n || u == v) continue;
        if (A[u][v] || deg[u] >= DEGCAP || deg[v] >= DEGCAP) continue;
        add_edge(u, v);
    }

    /* The start graph must be bipartite and valid, otherwise there is nothing to grow. */
    int bip = 1;
    for (int s = 0; s < N && bip; s++) {
        if (col[s] != -1) continue;
        col[s] = 0;
        int sp = 0;
        stk[sp++] = s;
        while (sp > 0) {
            int u = stk[--sp];
            for (int k = 0; k < deg[u]; k++) {
                int v = nb[u][k];
                if (col[v] == -1) {
                    col[v] = 1 - col[u];
                    stk[sp++] = v;
                } else if (col[v] == col[u]) {
                    bip = 0;
                }
            }
        }
    }
    if (!bip || bad_pairs() != 0) {
        printf("0 0\n");
        return 0;
    }

    snapM = take_snapshot(snapU, snapV);
    snapN = N;
    while (clock() < T_END && N < MAXN - 2) {
        if (try_grow()) {
            snapM = take_snapshot(snapU, snapV);
            snapN = N;
        } else {
            load_edges(snapN, snapU, snapV, snapM);
        }
    }

    printf("%d %d\n", snapN, snapM);
    for (int i = 0; i < snapM; i++) printf("%d %d\n", snapU[i], snapV[i]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q). Each old vertex has degree q+1,
# so with d >= q+1 it has spare capacity s = d - q - 1. Choose a point set S
# such that every line contains at most s points of S and every point lies on
# at most s lines indexed by S. For each P in S add a new A-vertex joined to
# the q+1 lines through P; for each j in S add a new B-vertex joined to the
# q+1 points on line j.
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
# Glue: run the C vertex-insertion engine on the best construction.
# ----------------------------------------------------------------------------

def _grow_in_c(d, D, seed, graph, end, hard):
    """Run the C engine from `graph` until time `end`; return parsed (n, edges) or None."""
    now = time.monotonic()
    budget = end - now
    if budget < 0.5 or d > 120 or graph[0] > 1900:
        return None
    out = lib.run_c(C_SOURCE, [d, D, abs(int(seed)), f"{budget:.2f}"], stdin_graph=graph,
                    timeout=max(1.0, hard - now))
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

    # Constructions: arc-extended projective planes (diameter 3), W(q) for D >= 4.
    if D >= 3:
        arcs = _arc_extensions(d, start + 0.05 * time_limit, random.Random(seed * 7919 + d))
        arcs.sort(key=lambda t: -t[0])
        for n_c, e_c in arcs[:3]:
            consider(n_c, e_c)
    if D >= 4 and time.monotonic() < start + 0.15 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # C vertex insertion with annealing on the bad-pair count. Skipped for d <= 3, D <= 3,
    # where the calibration construction already meets the ceiling.
    if not (d <= 3 and D <= 3):
        try:
            res = _grow_in_c(d, D, seed, best, start + 0.80 * time_limit, start + 0.92 * time_limit)
        except Exception:
            res = None
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
