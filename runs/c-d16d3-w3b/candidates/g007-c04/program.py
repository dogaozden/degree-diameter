import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C search engine.
#
# Works on any bipartite start graph (given on stdin) with max degree d and
# diameter D. Repeatedly:
#   1. adds one vertex on a random side, greedily joined to opposite-side
#      vertices with spare degree (maximising new distance-2 coverage);
#   2. runs simulated annealing over edge moves (add a random cross non-edge,
#      evicting random edges at full endpoints). Cost = number of ordered
#      (vertex, vertex) pairs at distance > D, computed with bitset BFS;
#   3. if cost reaches 0, the graph is valid and becomes the new base;
#      otherwise restart from the base with a different new vertex.
# Output is the largest valid graph found (or "0 0" if none, which the caller
# treats as "keep fallback").
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1200
#define MAXD 40
#define MAXW ((MAXN + 63) / 64)
#define MAXM (MAXN * MAXD / 2)

static int N, Dia, Dcap;
static int side[MAXN];
static int deg[MAXN];
static int adj[MAXN][MAXD];
static uint64_t bufA[MAXN][MAXW];
static uint64_t bufB[MAXN][MAXW];

static int bestN;
static int bestDeg[MAXN];
static int bestAdj[MAXN][MAXD];
static int bestSide[MAXN];

typedef struct { int type, a, b; } Op;
static Op logv[4096];
static int nlog;

static uint64_t rs = 88172645463325252ULL;
static clock_t T_START;

static uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double elapsed(void) { return (double)(clock() - T_START) / CLOCKS_PER_SEC; }

static int popc(uint64_t x) {
#if defined(__GNUC__) || defined(__clang__)
    return __builtin_popcountll(x);
#else
    int c = 0;
    while (x) { x &= x - 1; c++; }
    return c;
#endif
}

static int has_edge(int a, int b) {
    for (int k = 0; k < deg[a]; k++) if (adj[a][k] == b) return 1;
    return 0;
}

static void raw_add(int a, int b) {
    adj[a][deg[a]++] = b;
    adj[b][deg[b]++] = a;
}

static void raw_del(int a, int b) {
    for (int k = 0; k < deg[a]; k++)
        if (adj[a][k] == b) { adj[a][k] = adj[a][--deg[a]]; break; }
    for (int k = 0; k < deg[b]; k++)
        if (adj[b][k] == a) { adj[b][k] = adj[b][--deg[b]]; break; }
}

static void add_e(int a, int b) {
    raw_add(a, b);
    if (nlog < 4000) { logv[nlog].type = 0; logv[nlog].a = a; logv[nlog].b = b; nlog++; }
}

static void del_e(int a, int b) {
    raw_del(a, b);
    if (nlog < 4000) { logv[nlog].type = 1; logv[nlog].a = a; logv[nlog].b = b; nlog++; }
}

static void undo(void) {
    for (int i = nlog - 1; i >= 0; i--) {
        if (logv[i].type == 0) raw_del(logv[i].a, logv[i].b);
        else raw_add(logv[i].a, logv[i].b);
    }
    nlog = 0;
}

/* Number of ordered pairs (v, w) with dist(v, w) > Dia. Zero means valid. */
static long long cost_eval(void) {
    int n = N;
    int w = (n + 63) >> 6;
    uint64_t (*cur)[MAXW] = bufA;
    uint64_t (*nxt)[MAXW] = bufB;
    for (int v = 0; v < n; v++) {
        for (int j = 0; j < w; j++) cur[v][j] = 0;
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < Dia; r++) {
        for (int v = 0; v < n; v++) {
            for (int j = 0; j < w; j++) nxt[v][j] = cur[v][j];
            for (int k = 0; k < deg[v]; k++) {
                const uint64_t *cu = cur[adj[v][k]];
                for (int j = 0; j < w; j++) nxt[v][j] |= cu[j];
            }
        }
        uint64_t (*t)[MAXW] = cur;
        cur = nxt;
        nxt = t;
    }
    long long total = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int j = 0; j < w; j++) c += popc(cur[v][j]);
        total += n - c;
    }
    return total;
}

static void save_best(void) {
    bestN = N;
    memcpy(bestDeg, deg, sizeof(int) * N);
    memcpy(bestSide, side, sizeof(int) * N);
    for (int v = 0; v < N; v++) memcpy(bestAdj[v], adj[v], sizeof(int) * deg[v]);
}

static void restore_best(void) {
    N = bestN;
    nlog = 0;
    memcpy(deg, bestDeg, sizeof(int) * N);
    memcpy(side, bestSide, sizeof(int) * N);
    for (int v = 0; v < N; v++) memcpy(adj[v], bestAdj[v], sizeof(int) * deg[v]);
}

/* Add one vertex on a random side, joined greedily to opposite-side vertices. */
static void add_vertex(void) {
    int v = N++;
    int s = rndint(2);
    side[v] = s;
    deg[v] = 0;
    int cand[MAXN];
    int nc = 0;
    for (int u = 0; u < v; u++)
        if (side[u] != s && deg[u] < Dcap) cand[nc++] = u;
    for (int i = nc - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = cand[i]; cand[i] = cand[j]; cand[j] = t;
    }
    char used[MAXN];
    char cov[MAXN];
    memset(used, 0, sizeof(used));
    memset(cov, 0, sizeof(cov));
    nlog = 0;
    for (int step = 0; step < Dcap; step++) {
        int best = -1, bestg = -1;
        for (int c = 0; c < nc; c++) {
            if (used[c]) continue;
            int u = cand[c];
            if (deg[u] >= Dcap) continue;
            int g = 0;
            for (int k = 0; k < deg[u]; k++) {
                int x = adj[u][k];
                if (!cov[x]) g++;
            }
            if (g > bestg) { bestg = g; best = c; }
        }
        if (best < 0) break;
        used[best] = 1;
        int u = cand[best];
        add_e(v, u);
        for (int k = 0; k < deg[u]; k++) cov[adj[u][k]] = 1;
    }
    nlog = 0;
}

static int propose(void) {
    int a = rndint(N), b;
    do { b = rndint(N); } while (side[b] == side[a]);
    if (has_edge(a, b)) return 0;
    if (deg[a] >= Dcap) { int x = adj[a][rndint(deg[a])]; del_e(a, x); }
    if (deg[b] >= Dcap) { int y = adj[b][rndint(deg[b])]; del_e(b, y); }
    add_e(a, b);
    return 1;
}

static int eu[MAXM], ev[MAXM];

int main(int argc, char **argv) {
    T_START = clock();
    if (argc < 5) return 1;
    Dcap = atoi(argv[1]);
    Dia = atoi(argv[2]);
    uint64_t seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) rnd64();

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 < 2 || n0 > MAXN - 2 || m0 < 0 || m0 > MAXM ||
        Dcap < 1 || Dcap > MAXD - 2 || Dia < 1) {
        printf("0 0\n");
        return 0;
    }
    int ok = 1;
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { ok = 0; break; }
        if (u < 0 || v < 0 || u >= n0 || v >= n0 || u == v) { ok = 0; break; }
        eu[i] = u; ev[i] = v;
    }

    N = n0;
    nlog = 0;
    for (int v = 0; v < N; v++) deg[v] = 0;
    if (ok) {
        for (int i = 0; i < m0; i++) {
            int u = eu[i], v = ev[i];
            if (deg[u] >= Dcap || deg[v] >= Dcap || has_edge(u, v)) { ok = 0; break; }
            raw_add(u, v);
        }
    }
    if (ok) {
        for (int v = 0; v < N; v++) side[v] = -1;
        static int queue[MAXN];
        for (int s = 0; s < N && ok; s++) {
            if (side[s] >= 0) continue;
            side[s] = 0;
            int qh = 0, qt = 0;
            queue[qt++] = s;
            while (qh < qt && ok) {
                int u = queue[qh++];
                for (int k = 0; k < deg[u]; k++) {
                    int v = adj[u][k];
                    if (side[v] < 0) {
                        side[v] = 1 - side[u];
                        queue[qt++] = v;
                    } else if (side[v] == side[u]) {
                        ok = 0;
                        break;
                    }
                }
            }
        }
    }
    if (!ok) { printf("0 0\n"); return 0; }
    if (cost_eval() != 0) { printf("0 0\n"); return 0; }
    save_best();

    const double T0 = 1.5, T1 = 0.05;
    const int MOVES = 12000;
    while (elapsed() < tl) {
        if (bestN >= MAXN - 1) break;
        restore_best();
        add_vertex();
        long long cur = cost_eval();
        for (int it = 0; it < MOVES && cur > 0; it++) {
            if ((it & 63) == 0 && elapsed() >= tl) break;
            double T = T0 * pow(T1 / T0, (double)it / MOVES);
            nlog = 0;
            if (!propose()) continue;
            long long c2 = cost_eval();
            long long delta = c2 - cur;
            if (delta <= 0 || rnd01() < exp(-(double)delta / T)) cur = c2;
            else undo();
        }
        if (cur == 0) save_best();
    }

    long long m = 0;
    for (int v = 0; v < bestN; v++) m += bestDeg[v];
    printf("%d %lld\n", bestN, m / 2);
    for (int v = 0; v < bestN; v++)
        for (int k = 0; k < bestDeg[v]; k++) {
            int u = bestAdj[v][k];
            if (v < u) printf("%d %d\n", v, u);
        }
    return 0;
}
"""


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
# Build: best algebraic start, then C growth-and-annealing search.
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

    if D >= 3:
        cands = _arc_extensions(d, start + 0.2 * time_limit, random.Random(seed * 7919 + d))
        for n_c, e_c in sorted(cands, key=lambda t: -t[0]):
            consider(n_c, e_c)

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Already at the Moore bound (calibration cases): nothing to search for.
    if best_n >= lib.moore_bound(d, D) or d > 36 or D > 12:
        return best

    # Bold search: C growth + simulated annealing over general bipartite graphs.
    deadline = start + 0.88 * time_limit
    remaining = deadline - time.monotonic()
    budget = remaining - 3.0
    if budget >= 2.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                            stdin_graph=best, timeout=remaining)
            n2, e2 = lib.parse_graph_text(out)
            consider(n2, e2)
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
