import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: insertion + annealed repair on the bipartite graph.
#
# The state is a bipartite graph kept valid (degree <= d, bipartite). Inserting a
# vertex w on a side is valid iff every vertex is within distance D-1 of some
# neighbour of w, so a greedy ball-cover picks the neighbours. Whatever remains
# uncovered is repaired by simulated annealing over degree-preserving edge
# switches (plus spare-capacity edge additions, which never hurt), with the cost
# = number of vertex pairs at distance > D. When the cost reaches 0 the graph is
# saved and another vertex is inserted. A failed attempt rolls back to the best
# valid graph and retries with new random tie-breaks.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1200
#define MAXDEG 48
#define MAXW ((MAXN + 63) / 64)
#define MAXE (MAXN * MAXDEG / 2)
#define ATT_ITERS 30000
#define T_START 1.2
#define T_END 0.15

static int d_, D_;
static int n, W;
static int col[MAXN];
static int deg[MAXN];
static int adj[MAXN][MAXDEG];
static unsigned char A[MAXN][MAXN];
static int side_list[2][MAXN];
static int side_cnt[2];
static uint64_t Rb[MAXN * MAXW];
static uint64_t Tb[MAXN * MAXW];
static int inU[MAXE], inV[MAXE];

static int bestN = 0, bestM = 0;
static int bestCol[MAXN];
static int bestEU[MAXE], bestEV[MAXE];
static int have_best = 0;

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static clock_t t0;
static double elapsed(void) { return (double)(clock() - t0) / (double)CLOCKS_PER_SEC; }

static void add_edge(int u, int v) {
    A[u][v] = 1;
    A[v][u] = 1;
    adj[u][deg[u]++] = v;
    adj[v][deg[v]++] = u;
}

static void drop_nb(int u, int v) {
    for (int i = 0; i < deg[u]; i++) {
        if (adj[u][i] == v) {
            adj[u][i] = adj[u][--deg[u]];
            return;
        }
    }
}

static void rem_edge(int u, int v) {
    A[u][v] = 0;
    A[v][u] = 0;
    drop_nb(u, v);
    drop_nb(v, u);
}

static void rebuild_sides(void) {
    side_cnt[0] = 0;
    side_cnt[1] = 0;
    for (int v = 0; v < n; v++) side_list[col[v]][side_cnt[col[v]]++] = v;
}

static void clear_graph(void) {
    for (int v = 0; v < n; v++) {
        for (int i = 0; i < deg[v]; i++) A[v][adj[v][i]] = 0;
        deg[v] = 0;
    }
}

static int color_graph(void) {
    static int queue[MAXN];
    for (int v = 0; v < n; v++) col[v] = -1;
    for (int s = 0; s < n; s++) {
        if (col[s] != -1) continue;
        col[s] = 0;
        int qh = 0, qt = 0;
        queue[qt++] = s;
        while (qh < qt) {
            int u = queue[qh++];
            for (int i = 0; i < deg[u]; i++) {
                int v = adj[u][i];
                if (col[v] == -1) {
                    col[v] = 1 - col[u];
                    queue[qt++] = v;
                } else if (col[v] == col[u]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

/* R[v] = set of vertices within distance r of v, stride W. */
static void compute_balls(int r, uint64_t *R) {
    int N = n;
    memset(R, 0, sizeof(uint64_t) * (size_t)N * W);
    for (int v = 0; v < N; v++) R[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int t = 0; t < r; t++) {
        for (int v = 0; v < N; v++) {
            uint64_t *dst = Tb + (size_t)v * W;
            const uint64_t *src = R + (size_t)v * W;
            memcpy(dst, src, sizeof(uint64_t) * W);
            for (int i = 0; i < deg[v]; i++) {
                const uint64_t *nb = R + (size_t)adj[v][i] * W;
                for (int k = 0; k < W; k++) dst[k] |= nb[k];
            }
        }
        memcpy(R, Tb, sizeof(uint64_t) * (size_t)N * W);
    }
}

/* Number of unordered pairs at distance > D_. */
static int bad_pairs(void) {
    compute_balls(D_, Rb);
    long long tot = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        const uint64_t *row = Rb + (size_t)v * W;
        for (int k = 0; k < W; k++) c += __builtin_popcountll(row[k]);
        tot += n - c;
    }
    return (int)(tot / 2);
}

static char used_buf[MAXN];

/* Insert a vertex on the smaller side, joined to a greedy ball cover. */
static void insert_vertex(void) {
    int side;
    if (side_cnt[0] < side_cnt[1]) side = 0;
    else if (side_cnt[1] < side_cnt[0]) side = 1;
    else side = rndint(2);

    compute_balls(D_ - 1, Rb);
    int N0 = n;
    uint64_t cov[MAXW];
    memset(cov, 0, sizeof(uint64_t) * W);

    static int cand[MAXN];
    int nc = 0;
    for (int v = 0; v < N0; v++)
        if (col[v] == 1 - side && deg[v] < d_) cand[nc++] = v;
    for (int i = nc - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = cand[i];
        cand[i] = cand[j];
        cand[j] = t;
    }
    memset(used_buf, 0, (size_t)N0);

    int chosen[MAXDEG];
    int nch = 0;
    while (nch < d_) {
        int bi = -1, bg = 0;
        for (int i = 0; i < nc; i++) {
            int u = cand[i];
            if (used_buf[u]) continue;
            const uint64_t *b = Rb + (size_t)u * W;
            int g = 0;
            for (int k = 0; k < W; k++) g += __builtin_popcountll(b[k] & ~cov[k]);
            if (g > bg) {
                bg = g;
                bi = i;
            }
        }
        if (bi < 0) break;
        int u = cand[bi];
        used_buf[u] = 1;
        chosen[nch++] = u;
        const uint64_t *b = Rb + (size_t)u * W;
        for (int k = 0; k < W; k++) cov[k] |= b[k];
    }

    int w = N0;
    n = N0 + 1;
    W = (n + 63) >> 6;
    for (int i = 0; i < n; i++) {
        A[i][w] = 0;
        A[w][i] = 0;
    }
    deg[w] = 0;
    col[w] = side;
    for (int i = 0; i < nch; i++) add_edge(w, chosen[i]);
    rebuild_sides();
}

static int pick_vertex(int side, int need_spare) {
    if (side_cnt[side] == 0) return -1;
    for (int t = 0; t < 40; t++) {
        int v = side_list[side][rndint(side_cnt[side])];
        if (!need_spare || deg[v] < d_) return v;
    }
    return -1;
}

/* One annealing move. Returns 1 if accepted. */
static int sa_step(int *cost, double T) {
    if (rnd01() < 0.1) {
        int a = pick_vertex(0, 1), b = pick_vertex(1, 1);
        if (a < 0 || b < 0 || A[a][b]) return 0;
        add_edge(a, b);
        *cost = bad_pairs();  /* adding an edge never increases the cost */
        return 1;
    }
    int a = pick_vertex(0, 0), c = pick_vertex(0, 0);
    if (a < 0 || c < 0 || a == c || deg[a] == 0 || deg[c] == 0) return 0;
    int b = adj[a][rndint(deg[a])];
    int dd = adj[c][rndint(deg[c])];
    if (b == dd || A[a][dd] || A[c][b]) return 0;
    rem_edge(a, b);
    rem_edge(c, dd);
    add_edge(a, dd);
    add_edge(c, b);
    int c2 = bad_pairs();
    int delta = c2 - *cost;
    if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
        *cost = c2;
        return 1;
    }
    rem_edge(a, dd);
    rem_edge(c, b);
    add_edge(a, b);
    add_edge(c, dd);
    return 0;
}

static void save_best(void) {
    bestN = n;
    bestM = 0;
    for (int u = 0; u < n; u++) {
        bestCol[u] = col[u];
        for (int i = 0; i < deg[u]; i++) {
            int v = adj[u][i];
            if (u < v && bestM < MAXE) {
                bestEU[bestM] = u;
                bestEV[bestM] = v;
                bestM++;
            }
        }
    }
    have_best = 1;
}

static void load_best(void) {
    clear_graph();
    n = bestN;
    W = (n + 63) >> 6;
    for (int v = 0; v < n; v++) {
        col[v] = bestCol[v];
        deg[v] = 0;
    }
    for (int i = 0; i < bestM; i++) add_edge(bestEU[i], bestEV[i]);
    rebuild_sides();
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (rs == 0) rs = 1;
    t0 = clock();

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) n0 = 0;
    int ok = (n0 >= 1 && n0 <= MAXN - 2 && m0 >= 0 && m0 <= MAXE &&
              d_ >= 1 && d_ < MAXDEG - 1 && D_ >= 2);
    if (ok) {
        for (int i = 0; i < m0; i++) {
            if (scanf("%d %d", &inU[i], &inV[i]) != 2) {
                ok = 0;
                break;
            }
        }
    }
    n = n0;
    W = (n + 63) >> 6;
    if (!ok) {
        printf("0 0\n");
        return 0;
    }
    for (int i = 0; i < m0 && ok; i++) {
        int u = inU[i], v = inV[i];
        if (u < 0 || v < 0 || u >= n || v >= n || u == v || A[u][v] ||
            deg[u] >= d_ || deg[v] >= d_) {
            ok = 0;
            break;
        }
        add_edge(u, v);
    }
    if (!ok || !color_graph()) {
        printf("0 0\n");
        return 0;
    }
    rebuild_sides();

    int cost = bad_pairs();
    int need_insert = 0;
    if (cost == 0) {
        save_best();
        need_insert = 1;
    }
    int attempt = 0;
    while (elapsed() < budget) {
        if (need_insert) {
            if (n >= MAXN - 2) break;
            insert_vertex();
            cost = bad_pairs();
            need_insert = 0;
            attempt = 0;
            if (cost == 0) {
                save_best();
                need_insert = 1;
                continue;
            }
        }
        double frac = (double)attempt / (double)ATT_ITERS;
        double T = T_START * pow(T_END / T_START, frac);
        sa_step(&cost, T);
        attempt++;
        if (cost == 0) {
            save_best();
            need_insert = 1;
            continue;
        }
        if (attempt >= ATT_ITERS) {
            attempt = 0;
            if (have_best) {
                load_best();
                cost = bad_pairs();
                need_insert = 1;
            }
        }
    }

    printf("%d %d\n", bestN, bestM);
    for (int i = 0; i < bestM; i++) printf("%d %d\n", bestEU[i], bestEV[i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from PG(2, q). Every old vertex has degree q+1, so with d >= q+1 the
# spare capacity is s = d - q - 1. A point set S with at most s points on every
# line gives a new A-vertex per point of S (joined to the lines through it) and
# a new B-vertex per point of S (joined to the points of the line with that
# index). The conic plus nucleus is such a set for s = 2.
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
# Build: best algebraic start, then the C insertion + annealing engine.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        arcs = _arc_extensions(d, start + 0.08 * time_limit, random.Random(seed * 7919 + d))
        arcs.sort(key=lambda t: -t[0])
        for n_c, e_c in arcs[:3]:
            consider(n_c, e_c)

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Hand the best valid graph to the C engine and let it insert and repair.
    hard_end = start + 0.90 * time_limit - 1.5
    remaining = hard_end - time.monotonic()
    if d >= 6 and D >= 2 and remaining > 3:
        cbudget = remaining - 1.5
        try:
            text = lib.run_c(C_SOURCE, [d, D, int(seed), f"{cbudget:.2f}"],
                             stdin_graph=best, timeout=remaining + 0.5)
            n_c, e_c = lib.parse_graph_text(text)
            consider(n_c, e_c)
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
