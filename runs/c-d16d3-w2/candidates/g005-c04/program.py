import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: plateau search over valid bipartite graphs with a ball-cover
# insertion move.
#
# Let R = D-1. A new vertex w joined to a set N on the opposite colour class
# is within distance D of every current vertex x lying in the R-ball of some
# u in N, so the graph stays valid after insertion. Adding a cross edge only
# shortens distances, so it also preserves validity.
#
# Phase 1: greedy insertion from the start graph, with random cross edges as
#          perturbation when insertion stalls.
# Phase 2: plateau / annealing-like search. Remove a random vertex, check that
#          the graph is still valid, then re-insert greedily. Keep the result if
#          the order did not drop (small chance to accept a loss); otherwise
#          restore the snapshot. The best valid graph seen is returned.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXN 4096
#define MAXD 64
#define MAXW (MAXN / 64)

static int n, d, D, W;
static int deg[MAXN];
static int adj[MAXN][MAXD];
static int col[MAXN];
static uint64_t reach[MAXN][MAXW];
static uint64_t nxt[MAXN][MAXW];
static uint64_t rs = 88172645463325252ULL;

static int sn, bn;
static int sdeg[MAXN], scol[MAXN], sadj[MAXN][MAXD];
static int bdeg[MAXN], bcol[MAXN], badj[MAXN][MAXD];

static uint32_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return (uint32_t)(rs >> 16);
}

static int popc(uint64_t x) {
    int c = 0;
    while (x) { x &= x - 1; c++; }
    return c;
}

static int has_edge(int u, int v) {
    for (int i = 0; i < deg[u]; i++) if (adj[u][i] == v) return 1;
    return 0;
}

static void add_edge(int u, int v) {
    adj[u][deg[u]++] = v;
    adj[v][deg[v]++] = u;
}

static void drop_entry(int u, int x) {
    for (int i = 0; i < deg[u]; i++) {
        if (adj[u][i] == x) {
            adj[u][i] = adj[u][deg[u] - 1];
            deg[u]--;
            return;
        }
    }
}

static void replace_entry(int u, int from, int to) {
    for (int i = 0; i < deg[u]; i++) {
        if (adj[u][i] == from) { adj[u][i] = to; return; }
    }
}

/* Delete vertex x; the last vertex is moved into slot x. */
static void remove_vertex(int x) {
    int last = n - 1;
    for (int i = 0; i < deg[x]; i++) drop_entry(adj[x][i], x);
    deg[x] = 0;
    if (x != last) {
        for (int i = 0; i < deg[last]; i++) replace_entry(adj[last][i], last, x);
        for (int i = 0; i < deg[last]; i++) adj[x][i] = adj[last][i];
        deg[x] = deg[last];
        col[x] = col[last];
    }
    deg[last] = 0;
    n--;
}

static void compute_balls(int R) {
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) reach[v][w] = 0;
        reach[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < R; r++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < W; w++) nxt[v][w] = reach[v][w];
            for (int i = 0; i < deg[v]; i++) {
                int u = adj[v][i];
                for (int w = 0; w < W; w++) nxt[v][w] |= reach[u][w];
            }
        }
        for (int v = 0; v < n; v++)
            for (int w = 0; w < W; w++) reach[v][w] = nxt[v][w];
    }
}

static int covers_all(const uint64_t *cov) {
    for (int w = 0; w < W; w++) {
        uint64_t want;
        if (w < W - 1) {
            want = ~0ULL;
        } else {
            int r = n - 64 * (W - 1);
            want = (r >= 64) ? ~0ULL : ((1ULL << r) - 1);
        }
        if ((cov[w] & want) != want) return 0;
    }
    return 1;
}

/* True iff every pair of vertices is within distance D. */
static int valid_full(void) {
    W = (n + 63) >> 6;
    compute_balls(D);
    for (int v = 0; v < n; v++)
        if (!covers_all(reach[v])) return 0;
    return 1;
}

static int try_insert(int side) {
    int cand[MAXN];
    int nc = 0;
    for (int u = 0; u < n; u++)
        if (col[u] == 1 - side && deg[u] < d) cand[nc++] = u;
    if (nc == 0) return 0;
    for (int i = nc - 1; i > 0; i--) {
        int j = (int)(rnd() % (uint32_t)(i + 1));
        int t = cand[i]; cand[i] = cand[j]; cand[j] = t;
    }
    static int used[MAXN];
    for (int i = 0; i < n; i++) used[i] = 0;
    uint64_t cov[MAXW];
    for (int w = 0; w < W; w++) cov[w] = 0;
    int chosen[MAXD];
    int nch = 0;
    while (nch < d && !covers_all(cov)) {
        int best = -1, bg = 0;
        for (int i = 0; i < nc; i++) {
            int u = cand[i];
            if (used[u]) continue;
            int g = 0;
            for (int w = 0; w < W; w++) g += popc(reach[u][w] & ~cov[w]);
            if (g > bg) { bg = g; best = u; }
        }
        if (best < 0) break;
        used[best] = 1;
        chosen[nch++] = best;
        for (int w = 0; w < W; w++) cov[w] |= reach[best][w];
    }
    if (!covers_all(cov)) return 0;
    if (n >= MAXN) return 0;
    int w = n;
    n++;
    col[w] = side;
    deg[w] = 0;
    for (int i = 0; i < nch; i++) add_edge(chosen[i], w);
    return 1;
}

/* Greedily insert vertices until `misses` consecutive attempts fail. */
static int insert_burst(int misses_allowed) {
    int added = 0, misses = 0;
    while (misses < misses_allowed && n < MAXN) {
        W = (n + 63) >> 6;
        compute_balls(D - 1);
        int sides[2] = {0, 1};
        if (rnd() & 1u) { sides[0] = 1; sides[1] = 0; }
        int ok = 0;
        for (int k = 0; k < 2 && !ok; k++) ok = try_insert(sides[k]);
        if (ok) { added++; misses = 0; }
        else misses++;
    }
    return added;
}

static void random_cross_edge(void) {
    if (n < 2) return;
    for (int t = 0; t < 50; t++) {
        int u = (int)(rnd() % (uint32_t)n);
        int v = (int)(rnd() % (uint32_t)n);
        if (u == v || col[u] == col[v]) continue;
        if (deg[u] >= d || deg[v] >= d || has_edge(u, v)) continue;
        add_edge(u, v);
        return;
    }
}

static void save_to(int *pn, int *pdeg, int *pcol, int (*padj)[MAXD]) {
    *pn = n;
    for (int i = 0; i < n; i++) {
        pdeg[i] = deg[i];
        pcol[i] = col[i];
        memcpy(padj[i], adj[i], sizeof(int) * (size_t)deg[i]);
    }
}

static void load_from(int pn, const int *pdeg, const int *pcol, int (*padj)[MAXD]) {
    n = pn;
    for (int i = 0; i < n; i++) {
        deg[i] = pdeg[i];
        col[i] = pcol[i];
        memcpy(adj[i], padj[i], sizeof(int) * (size_t)deg[i]);
    }
}

static double secs(clock_t t0) {
    return (double)(clock() - t0) / CLOCKS_PER_SEC;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXD || D < 2) { printf("0 0\n"); return 0; }

    int N0, M0;
    if (scanf("%d %d", &N0, &M0) != 2) { printf("0 0\n"); return 0; }
    if (N0 < 1 || N0 > MAXN || M0 < 0) { printf("0 0\n"); return 0; }
    n = N0;
    for (int i = 0; i < M0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) continue;
        if (deg[u] >= d || deg[v] >= d || has_edge(u, v)) continue;
        add_edge(u, v);
    }

    static int queue[MAXN];
    for (int s = 0; s < n; s++) col[s] = -1;
    for (int s = 0; s < n; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int qh = 0, qt = 0;
        queue[qt++] = s;
        while (qh < qt) {
            int u = queue[qh++];
            for (int i = 0; i < deg[u]; i++) {
                int v = adj[u][i];
                if (col[v] < 0) {
                    col[v] = 1 - col[u];
                    queue[qt++] = v;
                }
            }
        }
    }

    if (!valid_full()) { printf("0 0\n"); return 0; }

    clock_t t0 = clock();

    /* Phase 1: greedy growth with perturbation. */
    int fails = 0;
    while (fails < 40 && n < MAXN && secs(t0) < 0.25 * budget) {
        if (insert_burst(3) > 0) {
            fails = 0;
        } else {
            fails++;
            random_cross_edge();
        }
    }

    /* Phase 2: remove-and-reinsert plateau search. */
    save_to(&bn, bdeg, bcol, badj);
    int best_n = n;
    while (secs(t0) < budget) {
        if (n < 2) break;
        int old_n = n;
        save_to(&sn, sdeg, scol, sadj);
        int x = (int)(rnd() % (uint32_t)n);
        remove_vertex(x);
        if (!valid_full()) {
            load_from(sn, sdeg, scol, sadj);
            continue;
        }
        insert_burst(12);
        if (n < old_n) {
            if (n < best_n - 2 || (rnd() % 100u) >= 3u) {
                load_from(sn, sdeg, scol, sadj);
                continue;
            }
        } else if (n == old_n) {
            if ((rnd() & 3u) == 0u) random_cross_edge();
        }
        if (n > best_n) {
            best_n = n;
            save_to(&bn, bdeg, bcol, badj);
        }
    }

    load_from(bn, bdeg, bcol, badj);

    int m2 = 0;
    for (int u = 0; u < n; u++)
        for (int i = 0; i < deg[u]; i++)
            if (adj[u][i] > u) m2++;
    printf("%d %d\n", n, m2);
    for (int u = 0; u < n; u++)
        for (int i = 0; i < deg[u]; i++)
            if (adj[u][i] > u) printf("%d %d\n", u, adj[u][i]);
    return 0;
}
"""


def _c_search(graph, d, D, seed, budget):
    """Run the C plateau search from graph; return (n, edges) or None on any failure."""
    if graph is None or budget < 0.5 or d > 64:
        return None
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                        stdin_graph=(graph[0], graph[1]), timeout=budget + 5.0)
        n2, e2 = lib.parse_graph_text(out)
    except Exception:
        return None
    if n2 < 1:
        return None
    return n2, e2


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from PG(2, q) incidence (points 0..m-1, lines m..2m-1), each vertex of
# degree q+1, spare s = d - q - 1. A-side: new vertices attached to the q+1
# lines through each chosen point, each line hit at most s times. B-side is
# the dual. The two sides are independent.
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


def _loads_ok(S, s, m, nbr):
    """True if every target is hit by <= s elements of S."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomized greedy choice so that every target is hit <= s times."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        load = [0] * m
        S = []
        for x in order:
            if all(load[t] < s for t in nbr[x]):
                S.append(x)
                for t in nbr[x]:
                    load[t] += 1
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


def _arc_graph(m, edges, point_lines, line_points, SA, SB):
    """Old PG incidence plus one new A-vertex per SA point and one new B-vertex per SB line."""
    na, nb = len(SA), len(SB)
    n = 2 * m + na + nb
    E = list(edges)
    for t, P in enumerate(SA):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(SB):
        b = 2 * m + na + t
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

        SA = _greedy_side(m, s, point_lines, rng, 40, deadline)
        SB = _greedy_side(m, s, line_points, rng, 40, deadline)
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if len(cs) > len(SA) and _loads_ok(cs, s, m, point_lines):
                SA = cs
            if len(cs) > len(SB) and _loads_ok(cs, s, m, line_points):
                SB = cs

        if not (_loads_ok(SA, s, m, point_lines) and _loads_ok(SB, s, m, line_points)):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, SA, SB))
    return out


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) (diameter 4), used only when D >= 4.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of W(q); diameter 4."""
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Driver.
#   0.00-0.08  arc-extended PG graphs (A and B sets chosen independently)
#   0.08-0.15  optional GQ baseline (D >= 4)
#   up to 0.85 C plateau search from the best graph found so far
# ----------------------------------------------------------------------------

def _c_search_safe(best, d, D, seed, time_limit, start):
    rem = 0.85 * time_limit - (time.monotonic() - start) - 1.0
    if rem < 0.5:
        return None
    return _c_search(best, d, D, seed, rem)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def elapsed():
        return time.monotonic() - start

    def consider(g):
        nonlocal best, best_n
        if g is None:
            return
        n, e = g
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

    if D >= 3:
        arcs = _arc_extensions(d, start + 0.08 * time_limit,
                               random.Random(seed * 7919 + d))
        arcs.sort(key=lambda t: -t[0])
        for g in arcs:
            consider(g)

    if D >= 4 and elapsed() < 0.15 * time_limit:
        consider(_best_gq(d))

    consider(_c_search_safe(best, d, D, seed, time_limit, start))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
