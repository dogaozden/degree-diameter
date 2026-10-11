import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3), as a start point.
#
# Start from the incidence graph of PG(2, q) (points 0..m-1, lines m..2m-1).
# Each old vertex has degree q+1, so with d >= q+1 it has spare capacity
# s = d - q - 1. Choose a point set S with every line holding <= s points of S
# and every point lying on <= s lines indexed by S. For each P in S add a new
# A-vertex joined to the q+1 lines through P; for each j in S add a new B-vertex
# joined to the q+1 points on line j. Diameter stays 3.
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
            cs = _conic_set(q, index, lib.GF(q))
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
# C search: simulated annealing on bipartite graphs with bounded degree.
#
# Input: a valid start graph on stdin. The search keeps a bipartition fixed,
# grows the vertex count by appending vertices, and minimises the number of
# vertex pairs at distance > D. Moves: endpoint shift, 2-switch, and adding a
# spare edge. Every time the cost reaches 0 the graph is saved and one more
# vertex is added. Output is the largest valid graph seen (or "0 0").
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1200
#define MAXDEG 40
#define WMAX ((MAXN + 63) / 64)
#define MAXE (MAXN * MAXDEG / 2 + 16)
#define STALL 20000

static int N, DMAX, DIAM;
static int side[MAXN];
static int deg[MAXN];
static int nb[MAXN][MAXDEG];
static unsigned char adjm[MAXN][MAXN];
static uint64_t bufA[MAXN * WMAX], bufB[MAXN * WMAX];
static int bestN = 0, bestM = 0;
static int bestE[MAXE][2];
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndint(int n) { return (int)(rnd() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void add_edge(int a, int b) {
    adjm[a][b] = 1; adjm[b][a] = 1;
    nb[a][deg[a]++] = b;
    nb[b][deg[b]++] = a;
}

static void rm_from(int a, int b) {
    for (int i = 0; i < deg[a]; i++) {
        if (nb[a][i] == b) { nb[a][i] = nb[a][--deg[a]]; return; }
    }
}

static void del_edge(int a, int b) {
    adjm[a][b] = 0; adjm[b][a] = 0;
    rm_from(a, b); rm_from(b, a);
}

/* Number of unordered pairs at distance > DIAM (0 means valid). */
static long cost(void) {
    int W = (N + 63) / 64;
    uint64_t *cur = bufA, *nxt = bufB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)N * W);
    for (int v = 0; v < N; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int it = 0; it < DIAM; it++) {
        for (int v = 0; v < N; v++) {
            uint64_t *o = nxt + (size_t)v * W;
            const uint64_t *c = cur + (size_t)v * W;
            for (int w = 0; w < W; w++) o[w] = c[w];
            for (int k = 0; k < deg[v]; k++) {
                const uint64_t *c2 = cur + (size_t)nb[v][k] * W;
                for (int w = 0; w < W; w++) o[w] |= c2[w];
            }
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
    }
    long bad = 0;
    for (int v = 0; v < N; v++) {
        int pc = 0;
        const uint64_t *c = cur + (size_t)v * W;
        for (int w = 0; w < W; w++) pc += popc(c[w]);
        bad += N - pc;
    }
    return bad / 2;
}

/* Random vertex on the opposite side of x with spare degree and no edge to x. */
static int spare_partner(int x) {
    for (int t = 0; t < 40; t++) {
        int y = rndint(N);
        if (side[y] != side[x] && deg[y] < DMAX && !adjm[x][y]) return y;
    }
    int s = rndint(N);
    for (int t = 0; t < N; t++) {
        int y = (s + t) % N;
        if (side[y] != side[x] && deg[y] < DMAX && !adjm[x][y]) return y;
    }
    return -1;
}

/* Add spare edges between random A and B vertices. Never increases the cost. */
static void fill(int tries) {
    for (int t = 0; t < tries; t++) {
        int a = rndint(N);
        if (side[a] != 0 || deg[a] >= DMAX) continue;
        int b = spare_partner(a);
        if (b >= 0) add_edge(a, b);
    }
}

/* Random edge, returned with a on side 0 and b on side 1. */
static int rand_edge(int *a, int *b) {
    for (int t = 0; t < 200; t++) {
        int v = rndint(N);
        if (deg[v] == 0) continue;
        int u = nb[v][rndint(deg[v])];
        if (side[v] == 0) { *a = v; *b = u; } else { *a = u; *b = v; }
        return 1;
    }
    return 0;
}

typedef struct {
    int nr, na;
    int ra[2], rb[2], aa[2], ab[2];
} Move;

static void apply_move(const Move *m) {
    for (int i = 0; i < m->nr; i++) del_edge(m->ra[i], m->rb[i]);
    for (int i = 0; i < m->na; i++) add_edge(m->aa[i], m->ab[i]);
}

static void undo_move(const Move *m) {
    for (int i = 0; i < m->na; i++) del_edge(m->aa[i], m->ab[i]);
    for (int i = 0; i < m->nr; i++) add_edge(m->ra[i], m->rb[i]);
}

static void save_best(void) {
    bestN = N;
    bestM = 0;
    for (int v = 0; v < N; v++) {
        for (int k = 0; k < deg[v]; k++) {
            if (nb[v][k] > v && bestM < MAXE) {
                bestE[bestM][0] = v;
                bestE[bestM][1] = nb[v][k];
                bestM++;
            }
        }
    }
}

static void restore_best(void) {
    for (int v = 0; v < N; v++) {
        for (int k = 0; k < deg[v]; k++) adjm[v][nb[v][k]] = 0;
        deg[v] = 0;
    }
    N = bestN;
    for (int i = 0; i < bestM; i++) add_edge(bestE[i][0], bestE[i][1]);
}

static int add_vertex(void) {
    if (N >= MAXN - 1) return 0;
    side[N] = rndint(2);
    deg[N] = 0;
    N++;
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    DMAX = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    rs ^= strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    double budget = atof(argv[4]);
    for (int i = 0; i < 10; i++) rnd();

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { n0 = 0; m0 = 0; }
    if (DMAX < 1 || DMAX > 32 || DIAM < 1 || n0 < 1 || n0 > MAXN - 200 || m0 < 0 || m0 > MAXE) {
        printf("0 0\n");
        return 0;
    }
    N = n0;
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { printf("0 0\n"); return 0; }
        if (u < 0 || v < 0 || u >= N || v >= N || u == v || adjm[u][v] ||
            deg[u] >= DMAX || deg[v] >= DMAX) {
            printf("0 0\n");
            return 0;
        }
        add_edge(u, v);
    }

    /* Bipartition by BFS; reject non-bipartite input. */
    static int queue[MAXN];
    for (int v = 0; v < N; v++) side[v] = -1;
    for (int s = 0; s < N; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int h = 0, t = 0;
        queue[t++] = s;
        while (h < t) {
            int x = queue[h++];
            for (int k = 0; k < deg[x]; k++) {
                int y = nb[x][k];
                if (side[y] < 0) { side[y] = 1 - side[x]; queue[t++] = y; }
                else if (side[y] == side[x]) { printf("0 0\n"); return 0; }
            }
        }
    }

    if (cost() != 0) { printf("0 0\n"); return 0; }
    save_best();

    double t0 = (double)clock() / CLOCKS_PER_SEC;
    double tend = t0 + budget;
    const double T0 = 2.0, T1 = 0.05;
    long cur = 0, minc = 0;
    int stall = 0;

    while (1) {
        double now = (double)clock() / CLOCKS_PER_SEC;
        if (now >= tend) break;

        if (cur == 0) {
            if (N > bestN) save_best();
            if (!add_vertex()) break;
            fill(3 * N);
            cur = cost();
            minc = cur;
            stall = 0;
            continue;
        }

        double f = (now - t0) / (budget > 1e-9 ? budget : 1.0);
        if (f > 1.0) f = 1.0;
        double T = T0 * pow(T1 / T0, f);

        Move mv;
        mv.nr = 0; mv.na = 0;
        int type = rndint(4);
        if (type <= 1) {
            int a, b;
            if (!rand_edge(&a, &b)) continue;
            if (rnd() & 1) {
                int y = spare_partner(a);
                if (y < 0) continue;
                mv.nr = 1; mv.ra[0] = a; mv.rb[0] = b;
                mv.na = 1; mv.aa[0] = a; mv.ab[0] = y;
            } else {
                int y = spare_partner(b);
                if (y < 0) continue;
                mv.nr = 1; mv.ra[0] = a; mv.rb[0] = b;
                mv.na = 1; mv.aa[0] = y; mv.ab[0] = b;
            }
        } else if (type == 2) {
            int a1, b1, a2, b2;
            if (!rand_edge(&a1, &b1) || !rand_edge(&a2, &b2)) continue;
            if (a1 == a2 || b1 == b2 || adjm[a1][b2] || adjm[a2][b1]) continue;
            mv.nr = 2;
            mv.ra[0] = a1; mv.rb[0] = b1;
            mv.ra[1] = a2; mv.rb[1] = b2;
            mv.na = 2;
            mv.aa[0] = a1; mv.ab[0] = b2;
            mv.aa[1] = a2; mv.ab[1] = b1;
        } else {
            int a = rndint(N);
            if (side[a] != 0 || deg[a] >= DMAX) continue;
            int b = spare_partner(a);
            if (b < 0) continue;
            mv.na = 1; mv.aa[0] = a; mv.ab[0] = b;
        }

        apply_move(&mv);
        long c2 = cost();
        int acc = (c2 <= cur) || (rnd01() < exp(-(double)(c2 - cur) / T));
        if (acc) cur = c2;
        else undo_move(&mv);

        if (cur < minc) { minc = cur; stall = 0; }
        else stall++;

        if (stall > STALL) {
            restore_best();
            if (!add_vertex()) break;
            fill(3 * N);
            cur = cost();
            minc = cur;
            stall = 0;
        }
    }

    if (bestN == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", bestN, bestM);
    for (int i = 0; i < bestM; i++) printf("%d %d\n", bestE[i][0], bestE[i][1]);
    return 0;
}
"""


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

    # Constructions: arc-extended projective plane graphs (D >= 3).
    if D >= 3:
        cands = _arc_extensions(d, t_start + 0.15 * time_limit, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, e_c in cands:
            consider(n_c, e_c)

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Main search: C annealing that grows the best valid construction.
    budget = 0.8 * time_limit - (time.monotonic() - t_start) - 1.0
    if budget >= 1.0 and d <= 32:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                            stdin_graph=best, timeout=time_limit * 0.92)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
