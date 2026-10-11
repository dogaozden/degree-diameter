import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Native search engine (C11). Input: a valid start graph on stdin. Output: the
# largest valid graph it reached. Only valid states are kept, and every move
# checks the diameter with bitset BFS. Two insertion moves:
#   * twin:  a copy of an existing vertex's neighbourhood (diameter preserved
#            automatically, since the copy is at distance 2 from its original);
#   * pool:  a new vertex joined to a random subset of free-slot vertices that
#            lie within distance 2 of a seed (checked explicitly).
# Vertices keep their sides, so the graph stays bipartite.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXV 1400
#define MAXD 64
#define MAXW 22

static int N, DEG_MAX, DIA;
static int deg[MAXV];
static int adj[MAXV][MAXD];
static int side[MAXV];
static uint64_t RB[2][MAXV][MAXW];
static uint64_t rs = 88172645463325252ULL;
static int stamp[MAXV];
static int stampv = 0;
static int pool[MAXV];

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int n) {
    return (int)(rnd64() % (uint64_t)n);
}

static int adjacent(int u, int v) {
    for (int i = 0; i < deg[u]; i++) if (adj[u][i] == v) return 1;
    return 0;
}

static void link(int u, int v) {
    adj[u][deg[u]++] = v;
    adj[v][deg[v]++] = u;
}

/* Returns 1 iff every pair of the N vertices is within distance DIA. */
static int diam_ok(void) {
    int W = (N + 63) >> 6;
    int cur = 0, nx = 1;
    for (int v = 0; v < N; v++) {
        for (int w = 0; w < W; w++) RB[cur][v][w] = 0;
        RB[cur][v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < DIA; r++) {
        for (int v = 0; v < N; v++) {
            for (int w = 0; w < W; w++) RB[nx][v][w] = RB[cur][v][w];
            for (int i = 0; i < deg[v]; i++) {
                int u = adj[v][i];
                for (int w = 0; w < W; w++) RB[nx][v][w] |= RB[cur][u][w];
            }
        }
        int t = cur; cur = nx; nx = t;
    }
    int rem = N - 64 * (W - 1);
    uint64_t last = (rem == 64) ? ~0ULL : ((1ULL << rem) - 1);
    for (int v = 0; v < N; v++) {
        for (int w = 0; w < W - 1; w++) if (RB[cur][v][w] != ~0ULL) return 0;
        if (RB[cur][v][W - 1] != last) return 0;
    }
    return 1;
}

/* Remove the most recently added vertex x = N-1 whose neighbours are nb[0..k-1]. */
static void undo_vertex(int x, int k, const int *nb) {
    for (int i = 0; i < k; i++) deg[nb[i]]--;
    deg[x] = 0;
    N--;
}

/* Add a vertex on side s joined to nb[0..k-1] (all on side 1-s); keep it only if valid. */
static int try_new(int s, int k, const int *nb) {
    if (k < 1 || N >= MAXV - 1) return 0;
    int x = N;
    N++;
    side[x] = s;
    deg[x] = 0;
    for (int i = 0; i < k; i++) link(x, nb[i]);
    if (diam_ok()) return 1;
    undo_vertex(x, k, nb);
    return 0;
}

static int twin_move(void) {
    int P = rndint(N);
    int k = deg[P];
    if (k < 1 || k > DEG_MAX) return 0;
    int nb[MAXD];
    for (int i = 0; i < k; i++) {
        int w = adj[P][i];
        if (deg[w] >= DEG_MAX) return 0;
        nb[i] = w;
    }
    return try_new(side[P], k, nb);
}

static int pool_move(void) {
    int s = rndint(2);
    int c0 = -1;
    for (int t = 0; t < 64; t++) {
        int v = rndint(N);
        if (side[v] == 1 - s && deg[v] < DEG_MAX) { c0 = v; break; }
    }
    if (c0 < 0) return 0;
    stampv++;
    int np = 0;
    stamp[c0] = stampv;
    pool[np++] = c0;
    for (int i = 0; i < deg[c0]; i++) {
        int u = adj[c0][i];
        for (int j = 0; j < deg[u]; j++) {
            int w = adj[u][j];
            if (stamp[w] != stampv && deg[w] < DEG_MAX) {
                stamp[w] = stampv;
                pool[np++] = w;
            }
        }
    }
    if (np < 2) return 0;
    int kmax = np < DEG_MAX ? np : DEG_MAX;
    int k = rndint(2) ? kmax : 2 + rndint(kmax - 1);
    if (k > kmax) k = kmax;
    int nb[MAXD];
    for (int i = 0; i < k; i++) {
        int j = i + rndint(np - i);
        int t = pool[i]; pool[i] = pool[j]; pool[j] = t;
        nb[i] = pool[i];
    }
    return try_new(s, k, nb);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    DIA = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], 0, 10);
    double tl = atof(argv[4]);
    DEG_MAX = d < 1 ? 1 : (d > MAXD ? MAXD : d);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd64();
    clock_t t0 = clock();

    int n, m;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXV - 1 || m < 0) {
        printf("0 0\n");
        return 0;
    }
    N = n;
    int ok = 1;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { ok = 0; break; }
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) { ok = 0; break; }
        if (deg[u] >= DEG_MAX || deg[v] >= DEG_MAX || adjacent(u, v)) { ok = 0; break; }
        link(u, v);
    }
    if (!ok) { printf("0 0\n"); return 0; }

    /* Sides by BFS 2-colouring. */
    static int stk[MAXV];
    int bip = 1;
    for (int v = 0; v < N; v++) side[v] = -1;
    for (int s0 = 0; s0 < N; s0++) {
        if (side[s0] != -1) continue;
        side[s0] = 0;
        int sp = 0;
        stk[sp++] = s0;
        while (sp) {
            int u = stk[--sp];
            for (int i = 0; i < deg[u]; i++) {
                int w = adj[u][i];
                if (side[w] == -1) { side[w] = 1 - side[u]; stk[sp++] = w; }
                else if (side[w] == side[u]) bip = 0;
            }
        }
    }
    if (!bip || !diam_ok()) { printf("0 0\n"); return 0; }

    long it = 0;
    for (;;) {
        if ((it & 31) == 0) {
            double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
            if (el >= tl) break;
        }
        it++;
        if (rndint(2)) twin_move();
        else pool_move();
    }

    long M = 0;
    for (int u = 0; u < N; u++) M += deg[u];
    M /= 2;
    printf("%d %ld\n", N, M);
    for (int u = 0; u < N; u++)
        for (int i = 0; i < deg[u]; i++)
            if (adj[u][i] > u) printf("%d %d\n", u, adj[u][i]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Constructions (Python).
#
# Arc-extended projective plane incidence graph (diameter 3). Start from PG(2,q);
# every vertex has degree q+1, so with d = q+1+s it has spare capacity s. Pick a
# point set S that is an arc (<= s points per line) and a line set S that is a
# dual arc (<= s lines through any point). Add one new point-side vertex per
# element of S (joined to the lines through it) and one new line-side vertex per
# line of S (joined to its points). The diameter stays 3, and the order is
# 2(q^2+q+1) + 2|S|. For d = 16 (q = 13, s = 2) |S| <= 14, giving 394.
#
# Analysis for the target: within this family every new vertex is a "pencil"
# or a "line", and the load constraints force both S and the dual set to be
# 2-arcs, so 394 is the maximum for PG(2,13) plus one layer. Beating 394 needs
# a different global structure; the C engine below explores insertions beyond
# that layer, and the Python fallback keeps the best valid graph found so far.
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
    """Conic (plus nucleus for even q): an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    """Old PG incidence plus a point-side vertex per element of S and a line-side vertex per element of S."""
    k = len(S)
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        y = 2 * m + k + t
        for Q in line_points[j]:
            E.append((Q, y))
    return 2 * m + 2 * k, E


def _arc_extensions(d, deadline, rng):
    """Return a list of (n, edges) arc-extended graphs, one per usable prime power q."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        if s < 1:
            continue
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        cands = [_greedy_arc(m, s, point_lines, line_points, rng, 40, deadline)]
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len)
        if not S or not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) (D = 4 baseline).
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

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    if not lib.is_valid(best[0], best[1], d, D):
        best = (2, [(0, 1)]) if d >= 1 and lib.is_valid(2, [(0, 1)], d, D) else (1, [])
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Arc-extended projective plane graphs (valid for D >= 3).
    if D >= 3:
        rng = random.Random(seed * 7919 + d)
        for n_c, e_c in _arc_extensions(d, t0 + 0.2 * time_limit, rng):
            consider(n_c, e_c)

    # Generalized quadrangle (valid for D >= 4).
    if D >= 4 and time.monotonic() - t0 < 0.2 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Native search from the best graph so far. The engine only keeps valid states,
    # so its output is either valid or rejected here.
    elapsed = time.monotonic() - t0
    cbudget = 0.9 * time_limit - elapsed - 3.0
    if cbudget >= 1.0 and best_n > 1:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, f"{cbudget:.2f}"],
                             stdin_graph=best, timeout=cbudget + 4.0)
            n, e = lib.parse_graph_text(text)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
