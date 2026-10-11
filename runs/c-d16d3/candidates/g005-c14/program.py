import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Constructions that give valid starting graphs (diameter <= 3 or 4).
#
# Arc-extended projective plane (D = 3): start from PG(2, q). Every vertex has
# degree q+1, so with degree cap d it has spare capacity s = d - q - 1. Pick a
# point set S with every line holding <= s points of S and every point lying on
# <= s lines of S. Add an A-vertex for each P in S (joined to the q+1 lines
# through P) and a B-vertex for each j in S (joined to the q+1 points on j).
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
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) (D = 4), small q only for speed.
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
    """W(q) for the largest prime power q <= 5 with q + 1 <= d (kept small for speed)."""
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# C engine: bitset-based simulated annealing that grows a valid graph.
#
# Starting from the given graph, the state is a bipartite graph with max degree d
# on N vertices. Cost = number of unordered pairs at distance > D (computed with
# bitset BFS). Moves: add an edge between free vertices, remove an edge, or a
# 2-switch across the bipartition. When cost reaches 0 the graph is recorded,
# one isolated vertex is added on the smaller side, and the search continues.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1100
#define MAXDEG 64
#define MAXW ((MAXN + 63) / 64)
#define MAXE (MAXN * MAXDEG)

static int Dd, Dg, N;
static int deg[MAXN];
static int adj[MAXN][MAXDEG];
static unsigned char mat[MAXN][MAXN];
static int side[MAXN];
static int cnt_side[2];
static uint64_t RA[MAXN][MAXW], RB[MAXN][MAXW];

static int bu[MAXE], bv[MAXE], best_m = 0, best_n = -1;
static int su[MAXE], sv[MAXE], start_m = 0, start_n = 0;

static uint64_t rs = 88172645463325252ULL;

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

/* Number of unordered vertex pairs at distance > Dg. */
static long cost_eval(void) {
    int W = (N + 63) / 64;
    for (int v = 0; v < N; v++) {
        for (int w = 0; w < W; w++) RA[v][w] = 0;
        RA[v][v >> 6] |= (uint64_t)1 << (v & 63);
    }
    for (int r = 0; r < Dg; r++) {
        for (int v = 0; v < N; v++) {
            for (int w = 0; w < W; w++) RB[v][w] = RA[v][w];
            for (int k = 0; k < deg[v]; k++) {
                const uint64_t *src = RA[adj[v][k]];
                for (int w = 0; w < W; w++) RB[v][w] |= src[w];
            }
        }
        for (int v = 0; v < N; v++)
            for (int w = 0; w < W; w++) RA[v][w] = RB[v][w];
    }
    long miss = 0;
    for (int v = 0; v < N; v++) {
        int p = 0;
        for (int w = 0; w < W; w++) p += popc64(RA[v][w]);
        miss += N - p;
    }
    return miss / 2;
}

static int add_edge(int a, int b) {
    if (a == b || mat[a][b] || deg[a] >= Dd || deg[b] >= Dd) return 0;
    mat[a][b] = mat[b][a] = 1;
    adj[a][deg[a]++] = b;
    adj[b][deg[b]++] = a;
    return 1;
}

static void del_edge(int a, int b) {
    mat[a][b] = mat[b][a] = 0;
    for (int i = 0; i < deg[a]; i++)
        if (adj[a][i] == b) { adj[a][i] = adj[a][--deg[a]]; break; }
    for (int i = 0; i < deg[b]; i++)
        if (adj[b][i] == a) { adj[b][i] = adj[b][--deg[b]]; break; }
}

/* Random vertex on side s (s = -1: any side); need_free: deg < Dd, else deg > 0. */
static int rand_vertex(int s, int need_free) {
    for (int t = 0; t < 2000; t++) {
        int v = rndint(N);
        if (s >= 0 && side[v] != s) continue;
        if (need_free) { if (deg[v] < Dd) return v; }
        else if (deg[v] > 0) return v;
    }
    return -1;
}

static int dump(int *eu, int *ev) {
    int m = 0;
    for (int v = 0; v < N; v++)
        for (int k = 0; k < deg[v]; k++) {
            int u = adj[v][k];
            if (u > v) { eu[m] = v; ev[m] = u; m++; }
        }
    return m;
}

static void reset_complete(void) {
    memset(mat, 0, sizeof(mat));
    for (int v = 0; v < MAXN; v++) deg[v] = 0;
    N = 2 * Dd;
    cnt_side[0] = cnt_side[1] = 0;
    for (int v = 0; v < N; v++) {
        side[v] = (v < Dd) ? 0 : 1;
        cnt_side[side[v]]++;
    }
    for (int a = 0; a < Dd; a++)
        for (int b = Dd; b < N; b++)
            add_edge(a, b);
}

static void grow(void) {
    int s = (cnt_side[0] <= cnt_side[1]) ? 0 : 1;
    side[N] = s;
    cnt_side[s]++;
    deg[N] = 0;
    N++;
}

static int accept(long nc, long cur, double T) {
    if (nc <= cur) return 1;
    return rnd01() < exp(-(double)(nc - cur) / T);
}

static int qbuf[MAXN];

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]), D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    if (d < 1 || d > MAXDEG || D < 1) { printf("0 0\n"); return 0; }
    Dd = d; Dg = D;
    rs = rs ^ (seed * 0x9E3779B97F4A7C15ULL + 12345ULL);
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) rnd64();

    clock_t t0 = clock();
    double limit = tl * (double)CLOCKS_PER_SEC;

    int n = 0, m = 0, bad = 0;
    if (scanf("%d %d", &n, &m) != 2) { n = 0; m = 0; }
    if (n > 0 && n <= MAXN && m >= 0) {
        N = n;
        for (int i = 0; i < m && !bad; i++) {
            int u, v;
            if (scanf("%d %d", &u, &v) != 2) { bad = 1; break; }
            if (u < 0 || v < 0 || u >= N || v >= N || u == v ||
                mat[u][v] || deg[u] >= Dd || deg[v] >= Dd) { bad = 1; break; }
            add_edge(u, v);
        }
    } else {
        bad = 1;
    }

    if (!bad) {
        for (int v = 0; v < N; v++) side[v] = -1;
        for (int s = 0; s < N && !bad; s++) {
            if (side[s] != -1) continue;
            side[s] = 0;
            int qh = 0, qt = 0;
            qbuf[qt++] = s;
            while (qh < qt && !bad) {
                int x = qbuf[qh++];
                for (int k = 0; k < deg[x]; k++) {
                    int y = adj[x][k];
                    if (side[y] == -1) { side[y] = 1 - side[x]; qbuf[qt++] = y; }
                    else if (side[y] == side[x]) { bad = 1; break; }
                }
            }
        }
        if (!bad) {
            cnt_side[0] = cnt_side[1] = 0;
            for (int v = 0; v < N; v++) cnt_side[side[v]]++;
        }
    }
    if (bad) reset_complete();

    start_n = N;
    start_m = dump(su, sv);

    long cur = cost_eval();
    if (cur == 0) { best_m = dump(bu, bv); best_n = N; }

    double T = 1.0;
    unsigned long long it = 0;
    for (;;) {
        if ((it & 127) == 0 && (double)(clock() - t0) >= limit) break;
        it++;

        if (cur == 0) {
            if (N > best_n) { best_m = dump(bu, bv); best_n = N; }
            if (N >= MAXN - 1) break;
            grow();
            cur = cost_eval();
            T = 1.0;
            continue;
        }

        T *= 0.99998;
        if (T < 0.25) T = 0.25;
        if (it % 500000ULL == 0) T = 1.0;

        double r = rnd01();
        if (r < 0.40) {
            int a = rand_vertex(0, 1), b = rand_vertex(1, 1);
            if (a < 0 || b < 0 || mat[a][b]) continue;
            add_edge(a, b);
            long nc = cost_eval();
            if (accept(nc, cur, T)) cur = nc;
            else del_edge(a, b);
        } else if (r < 0.50) {
            int v = rand_vertex(-1, 0);
            if (v < 0) continue;
            int u = adj[v][rndint(deg[v])];
            del_edge(v, u);
            long nc = cost_eval();
            if (accept(nc, cur, T)) cur = nc;
            else add_edge(v, u);
        } else {
            int a1 = rand_vertex(0, 0), b2 = rand_vertex(1, 0);
            if (a1 < 0 || b2 < 0) continue;
            int b1 = adj[a1][rndint(deg[a1])];
            int a2 = adj[b2][rndint(deg[b2])];
            if (a1 == a2 || b1 == b2 || mat[a1][b2] || mat[a2][b1]) continue;
            del_edge(a1, b1);
            del_edge(a2, b2);
            add_edge(a1, b2);
            add_edge(a2, b1);
            long nc = cost_eval();
            if (accept(nc, cur, T)) cur = nc;
            else {
                del_edge(a1, b2);
                del_edge(a2, b1);
                add_edge(a1, b1);
                add_edge(a2, b2);
            }
        }
    }

    if (cur == 0 && N > best_n) { best_m = dump(bu, bv); best_n = N; }

    int on, om;
    int *ou, *ov;
    if (best_n >= 0) { on = best_n; om = best_m; ou = bu; ov = bv; }
    else { on = start_n; om = start_m; ou = su; ov = sv; }

    printf("%d %d\n", on, om);
    for (int i = 0; i < om; i++) printf("%d %d\n", ou[i], ov[i]);
    return 0;
}
"""


def _c_improve(d, D, start, seed, budget):
    """Run the C annealer from `start`; return (n, edges) of its best valid graph."""
    text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                     stdin_graph=start, timeout=budget + 6.0)
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

    # Structured starts.
    if D >= 3:
        rng = random.Random(seed * 7919 + d)
        for n_c, e_c in sorted(_arc_extensions(d, t0 + 0.2 * time_limit, rng), key=lambda t: -t[0]):
            consider(n_c, e_c)
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Main search: C annealer grows the best structured graph.
    if D >= 2 and 1 <= d <= 60:
        elapsed = time.monotonic() - t0
        budget = min(0.85 * time_limit, 0.93 * time_limit - elapsed - 3.0)
        if budget >= 1.0:
            try:
                n2, e2 = _c_improve(d, D, best, seed, budget)
                consider(n2, e2)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
