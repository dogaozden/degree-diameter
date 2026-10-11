import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: grow-and-repair search that keeps the graph bipartite, with max
# degree d and diameter <= D.
#
# State: a valid bipartite graph on N vertices (side 0 / side 1).
# Cost: number of unordered vertex pairs at distance > D, computed exactly with
# bitset ball expansion (DD rounds of OR over neighbour balls).
# Loop:
#   * cost 0: record the graph if it is the largest valid one so far, snapshot
#     it, then insert a new vertex on a random side. The new vertex takes d
#     opposite-side neighbours; if a neighbour is full, one of its edges is
#     removed first, which frees capacity for repair.
#   * cost > 0: simulated annealing on degree-respecting moves (add edge,
#     remove edge, degree-preserving 2-switch, move one endpoint onto a spare
#     vertex). Moves are undone when rejected. After PL moves without repair,
#     restore the last valid snapshot and try a different insertion.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define NMAX 1024
#define WMAX (NMAX / 64)
#define MAXD 64
#define T0 2.0
#define TMIN 0.12
#define DECAY 0.9993
#define PL 4000

typedef struct {
    int N;
    int side[NMAX];
    int deg[NMAX];
    int nb[NMAX][MAXD];
    unsigned char has[NMAX][NMAX];
} State;

typedef struct {
    int nr, na;
    int ra[2], rb[2], aa[2], ab[2];
} Move;

static State S, SNAP;
static int dd, DD;
static uint64_t rs = 88172645463325252ULL;
static uint64_t RB[2][NMAX][WMAX];
static int bestN = 0, bestM = 0;
static int bestA[NMAX * MAXD / 2 + 4], bestB[NMAX * MAXD / 2 + 4];

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int n) { return (int)(rnd() % (uint64_t)n); }

static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static void add_edge(int a, int b) {
    S.has[a][b] = 1;
    S.has[b][a] = 1;
    S.nb[a][S.deg[a]++] = b;
    S.nb[b][S.deg[b]++] = a;
}

static void del_one(int v, int u) {
    int k;
    for (k = 0; k < S.deg[v]; k++) {
        if (S.nb[v][k] == u) {
            S.nb[v][k] = S.nb[v][--S.deg[v]];
            return;
        }
    }
}

static void rem_edge(int a, int b) {
    S.has[a][b] = 0;
    S.has[b][a] = 0;
    del_one(a, b);
    del_one(b, a);
}

static int pick_side(int s) {
    int v;
    do {
        v = rndint(S.N);
    } while (S.side[v] != s);
    return v;
}

static int pop64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Number of unordered pairs at distance > DD. Zero means the graph is valid. */
static long long cost_eval(void) {
    int n = S.N, W = (n + 63) >> 6, v, u, k, w, it, cur = 0, nx;
    long long bad = 0;
    for (v = 0; v < n; v++) {
        for (w = 0; w < W; w++) RB[0][v][w] = 0;
        RB[0][v][v >> 6] |= 1ULL << (v & 63);
    }
    for (it = 0; it < DD; it++) {
        nx = cur ^ 1;
        for (v = 0; v < n; v++) {
            for (w = 0; w < W; w++) RB[nx][v][w] = RB[cur][v][w];
            for (k = 0; k < S.deg[v]; k++) {
                u = S.nb[v][k];
                for (w = 0; w < W; w++) RB[nx][v][w] |= RB[cur][u][w];
            }
        }
        cur = nx;
    }
    for (v = 0; v < n; v++) {
        int c = 0;
        for (w = 0; w < W; w++) c += pop64(RB[cur][v][w]);
        bad += n - c;
    }
    return bad / 2;
}

static void save_best(void) {
    int v, k, m = 0;
    for (v = 0; v < S.N; v++) {
        if (S.side[v] != 0) continue;
        for (k = 0; k < S.deg[v]; k++) {
            bestA[m] = v;
            bestB[m] = S.nb[v][k];
            m++;
        }
    }
    bestN = S.N;
    bestM = m;
}

static int propose(Move *mv) {
    int t = rndint(100), a, b, a2, b2;
    mv->nr = 0;
    mv->na = 0;
    if (t < 30) {                       /* add an edge between two spare vertices */
        a = pick_side(0);
        b = pick_side(1);
        if (S.deg[a] >= dd || S.deg[b] >= dd || S.has[a][b]) return 0;
        mv->na = 1;
        mv->aa[0] = a;
        mv->ab[0] = b;
        return 1;
    }
    if (t < 40) {                       /* remove an edge */
        a = pick_side(0);
        if (S.deg[a] == 0) return 0;
        b = S.nb[a][rndint(S.deg[a])];
        mv->nr = 1;
        mv->ra[0] = a;
        mv->rb[0] = b;
        return 1;
    }
    if (t < 75) {                       /* degree-preserving 2-switch */
        a = pick_side(0);
        if (S.deg[a] == 0) return 0;
        b = S.nb[a][rndint(S.deg[a])];
        a2 = pick_side(0);
        if (S.deg[a2] == 0) return 0;
        b2 = S.nb[a2][rndint(S.deg[a2])];
        if (a == a2 || b == b2 || S.has[a][b2] || S.has[a2][b]) return 0;
        mv->nr = 2;
        mv->ra[0] = a;  mv->rb[0] = b;
        mv->ra[1] = a2; mv->rb[1] = b2;
        mv->na = 2;
        mv->aa[0] = a;  mv->ab[0] = b2;
        mv->aa[1] = a2; mv->ab[1] = b;
        return 1;
    }
    /* move one endpoint of an edge onto a spare vertex */
    a = pick_side(0);
    if (S.deg[a] == 0) return 0;
    b = S.nb[a][rndint(S.deg[a])];
    if (rnd() & 1) {
        b2 = pick_side(1);
        if (b2 == b || S.deg[b2] >= dd || S.has[a][b2]) return 0;
        mv->nr = 1; mv->ra[0] = a; mv->rb[0] = b;
        mv->na = 1; mv->aa[0] = a; mv->ab[0] = b2;
    } else {
        a2 = pick_side(0);
        if (a2 == a || S.deg[a2] >= dd || S.has[a2][b]) return 0;
        mv->nr = 1; mv->ra[0] = a; mv->rb[0] = b;
        mv->na = 1; mv->aa[0] = a2; mv->ab[0] = b;
    }
    return 1;
}

static void apply_move(const Move *mv) {
    int i;
    for (i = 0; i < mv->nr; i++) rem_edge(mv->ra[i], mv->rb[i]);
    for (i = 0; i < mv->na; i++) add_edge(mv->aa[i], mv->ab[i]);
}

static void undo_move(const Move *mv) {
    int i;
    for (i = 0; i < mv->na; i++) rem_edge(mv->aa[i], mv->ab[i]);
    for (i = 0; i < mv->nr; i++) add_edge(mv->ra[i], mv->rb[i]);
}

static void insert_vertex(void) {
    int s = rndint(2), v = S.N, k, u, x;
    S.N++;
    S.side[v] = s;
    S.deg[v] = 0;
    for (k = 0; k < S.N; k++) {
        S.has[v][k] = 0;
        S.has[k][v] = 0;
    }
    for (k = 0; k < dd; k++) {
        u = pick_side(1 - s);
        if (S.has[v][u]) continue;
        if (S.deg[u] >= dd) {
            x = S.nb[u][rndint(S.deg[u])];
            rem_edge(u, x);
        }
        add_edge(v, u);
    }
}

int main(int argc, char **argv) {
    int n = 0, m = 0, i, a, b, ok = 1, k;
    double tl;
    clock_t t0;
    long long cost, c2, delta;
    double T = T0;
    int phase = 0, hasSnap = 0;
    static int colr[NMAX], qbuf[NMAX];

    if (argc < 5) return 1;
    dd = atoi(argv[1]);
    DD = atoi(argv[2]);
    if (dd < 1) dd = 1;
    if (dd > MAXD) dd = MAXD;
    if (DD < 1) DD = 1;
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    tl = atof(argv[4]);
    t0 = clock();

    if (scanf("%d %d", &n, &m) != 2) { n = 0; m = 0; }
    if (n < 0 || n > NMAX - 4 || m < 0) { printf("0 0\n"); return 0; }
    S.N = n;
    for (i = 0; i < m; i++) {
        if (scanf("%d %d", &a, &b) != 2) { ok = 0; break; }
        if (a < 0 || b < 0 || a >= n || b >= n || a == b ||
            S.has[a][b] || S.deg[a] >= dd || S.deg[b] >= dd) {
            ok = 0;
            break;
        }
        add_edge(a, b);
    }
    if (!ok) { printf("0 0\n"); return 0; }

    if (n == 0) {
        S.N = 2;
        S.side[0] = 0;
        S.side[1] = 1;
        add_edge(0, 1);
    } else {
        for (i = 0; i < n; i++) colr[i] = -1;
        for (i = 0; i < n && ok; i++) {
            int head = 0, tail = 0;
            if (colr[i] >= 0) continue;
            colr[i] = 0;
            qbuf[tail++] = i;
            while (head < tail && ok) {
                int v = qbuf[head++];
                for (k = 0; k < S.deg[v]; k++) {
                    int u = S.nb[v][k];
                    if (colr[u] < 0) {
                        colr[u] = 1 - colr[v];
                        qbuf[tail++] = u;
                    } else if (colr[u] == colr[v]) {
                        ok = 0;
                        break;
                    }
                }
            }
        }
        if (!ok) { printf("0 0\n"); return 0; }
        for (i = 0; i < n; i++) S.side[i] = colr[i];
    }

    cost = cost_eval();
    if (cost == 0) save_best();

    while ((double)(clock() - t0) / CLOCKS_PER_SEC < tl) {
        if (cost == 0) {
            if (S.N > bestN) save_best();
            if (S.N >= NMAX - 2) break;
            memcpy(&SNAP, &S, sizeof(State));
            hasSnap = 1;
            insert_vertex();
            cost = cost_eval();
            T = T0;
            phase = 0;
            continue;
        }
        {
            Move mv;
            if (!propose(&mv)) {
                phase++;
            } else {
                apply_move(&mv);
                c2 = cost_eval();
                delta = c2 - cost;
                if (delta <= 0 || rnd01() < exp(-(double)delta / T)) cost = c2;
                else undo_move(&mv);
            }
        }
        T *= DECAY;
        if (T < TMIN) T = TMIN;
        if (++phase > PL) {
            if (hasSnap) {
                memcpy(&S, &SNAP, sizeof(State));
                cost = cost_eval();
            }
            T = T0;
            phase = 0;
        }
    }
    if (cost == 0 && S.N > bestN) save_best();

    if (bestN > 0) {
        printf("%d %d\n", bestN, bestM);
        for (i = 0; i < bestM; i++) printf("%d %d\n", bestA[i], bestB[i]);
    } else {
        printf("0 0\n");
    }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python construction: arc-extended projective plane incidence graphs (D = 3).
#
# Start from the incidence graph of PG(2, q). Each old vertex has degree q+1,
# so with d >= q+1 it has spare capacity s = d - q - 1. Choose a point set S
# with every line containing <= s points of S and every point lying on <= s
# lines indexed by S. For each P in S add an A-vertex joined to the q+1 lines
# through P; for each j in S add a B-vertex joined to the q+1 points on j.
# ----------------------------------------------------------------------------

def _pg_data(q):
    """Return (m, edges, point_lines, line_points, index, pts) for PG(2, q)."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    pts = lib.projective_points(q)
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
    for t, j in enumerate(S):  # line j uses the same vector as point j
        b = 2 * m + k + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _arc_extensions(d, deadline, rng):
    """Return (n, edges) candidates for each prime power q with q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q) or time.monotonic() > deadline:
            continue
        s = d - q - 1
        m, edges, point_lines, line_points, index, _ = _pg_data(q)
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
        rng = random.Random(seed * 7919 + d)
        for n_c, e_c in _arc_extensions(d, t0 + 0.1 * time_limit, rng):
            consider(n_c, e_c)

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Grow and repair in C from the best construction. Skip when the start is
    # already at the Moore bound (calibration cases return instantly).
    if D >= 3 and best_n < lib.moore_bound(d, D) and best_n <= 1000:
        left = time_limit - (time.monotonic() - t0) - 6.0
        if left > 3.0:
            try:
                txt = lib.run_c(C_SOURCE, [d, D, seed, round(left - 1.0, 2)],
                                stdin_graph=best, timeout=left + 2.0)
                n, e = lib.parse_graph_text(txt)
                consider(n, e)
            except (RuntimeError, ValueError):
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
