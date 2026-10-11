import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing over bipartite graphs with vertex insertion.
#
# State: a bipartite graph (colour classes fixed per vertex) with max degree d.
# Cost = number of unordered vertex pairs at distance > D. Valid iff cost = 0.
#
# Loop:
#   1. fill spare degree with random cross edges (never hurts distances),
#   2. insert a new vertex on a random side, greedily joined to a cover of
#      the old vertices (radius D-1 balls),
#   3. anneal with degree-preserving double-edge swaps (keep bipartiteness),
#      cross-edge additions, and occasional removals (to create slack),
#   4. on success snapshot the graph; on failure roll back to the snapshot.
# Output: the last valid snapshot.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 2048
#define MAXD 64
#define MAXW (MAXN / 64)

static int n, d, D;
static int deg[MAXN];
static int adj[MAXN][MAXD];
static unsigned char A[MAXN][MAXN];
static int col[MAXN];
static uint64_t reach[MAXN][MAXW];
static uint64_t nxt[MAXN][MAXW];
static int bn;
static int bdeg[MAXN];
static int badj[MAXN][MAXD];
static int bcol[MAXN];
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndi(int k) { return (int)(rnd64() % (uint64_t)k); }

static double rndu(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void add_edge(int u, int v) {
    adj[u][deg[u]++] = v;
    adj[v][deg[v]++] = u;
    A[u][v] = 1;
    A[v][u] = 1;
}

static void del_from(int u, int v) {
    for (int i = 0; i < deg[u]; i++) {
        if (adj[u][i] == v) {
            adj[u][i] = adj[u][--deg[u]];
            return;
        }
    }
}

static void remove_edge(int u, int v) {
    del_from(u, v);
    del_from(v, u);
    A[u][v] = 0;
    A[v][u] = 0;
}

/* Fill reach[v] with the ball of radius R around each vertex; return word count. */
static int compute_balls(int R) {
    int W = (n + 63) >> 6;
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
    return W;
}

/* Number of unordered pairs at distance > D (unreachable counts). */
static long long bad_pairs(void) {
    int W = compute_balls(D);
    long long bad = 0;
    for (int v = 0; v < n; v++) {
        int cnt = 0;
        for (int w = 0; w < W; w++) cnt += popc(reach[v][w]);
        bad += n - cnt;
    }
    return bad / 2;
}

static void fill_spare(long long tries) {
    for (long long t = 0; t < tries; t++) {
        int a = rndi(n), b = rndi(n);
        if (col[a] == col[b] || deg[a] >= d || deg[b] >= d || A[a][b]) continue;
        add_edge(a, b);
    }
}

/* Insert a new vertex on `side`, greedily joined to a cover of the old vertices. */
static void insert_vertex(int side) {
    int old_n = n;
    int W = compute_balls(D - 1);
    uint64_t cov[MAXW];
    for (int w = 0; w < W; w++) cov[w] = 0;
    static char used[MAXN];
    memset(used, 0, sizeof(used));
    int chosen[MAXD];
    int nch = 0;
    while (nch < d) {
        int best = -1, bg = 0;
        int off = rndi(old_n);
        for (int k = 0; k < old_n; k++) {
            int u = (off + k) % old_n;
            if (col[u] != 1 - side || deg[u] >= d || used[u]) continue;
            int g = 0;
            for (int w = 0; w < W; w++) g += popc(reach[u][w] & ~cov[w]);
            if (g > bg) { bg = g; best = u; }
        }
        if (best < 0) break;
        used[best] = 1;
        chosen[nch++] = best;
        for (int w = 0; w < W; w++) cov[w] |= reach[best][w];
    }
    int wn = n;
    n++;
    col[wn] = side;
    deg[wn] = 0;
    for (int i = 0; i < nch; i++) add_edge(chosen[i], wn);
}

static int anneal(long long iters, double T0, double T1, clock_t tend) {
    long long cur = bad_pairs();
    if (cur == 0) return 1;
    for (long long it = 0; it < iters; it++) {
        if ((it & 255) == 0 && clock() > tend) break;
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        double r = rndu();
        if (r < 0.6) {
            /* degree-preserving double-edge swap */
            int u = rndi(n), x = rndi(n);
            if (deg[u] == 0 || deg[x] == 0) continue;
            int v = adj[u][rndi(deg[u])];
            int y = adj[x][rndi(deg[x])];
            int a1, b1, a2, b2;
            if (col[u] == 0) { a1 = u; b1 = v; } else { a1 = v; b1 = u; }
            if (col[x] == 0) { a2 = x; b2 = y; } else { a2 = y; b2 = x; }
            if (a1 == a2 || b1 == b2) continue;
            if (A[a1][b2] || A[a2][b1]) continue;
            remove_edge(a1, b1);
            remove_edge(a2, b2);
            add_edge(a1, b2);
            add_edge(a2, b1);
            long long c2 = bad_pairs();
            long long delta = c2 - cur;
            if (delta <= 0 || rndu() < exp(-(double)delta / T)) {
                cur = c2;
            } else {
                remove_edge(a1, b2);
                remove_edge(a2, b1);
                add_edge(a1, b1);
                add_edge(a2, b2);
            }
        } else if (r < 0.9) {
            /* add a cross edge between spare vertices (never increases cost) */
            int a = rndi(n), b = rndi(n);
            if (col[a] == col[b] || deg[a] >= d || deg[b] >= d || A[a][b]) continue;
            add_edge(a, b);
            cur = bad_pairs();
        } else {
            /* remove an edge to create slack, accept by Metropolis */
            int u = rndi(n);
            if (deg[u] == 0) continue;
            int v = adj[u][rndi(deg[u])];
            remove_edge(u, v);
            long long c2 = bad_pairs();
            long long delta = c2 - cur;
            if (delta <= 0 || rndu() < exp(-(double)delta / T)) {
                cur = c2;
            } else {
                add_edge(u, v);
            }
        }
        if (cur == 0) return 1;
    }
    return cur == 0;
}

static void save_snap(void) {
    bn = n;
    for (int v = 0; v < n; v++) {
        bdeg[v] = deg[v];
        bcol[v] = col[v];
        for (int i = 0; i < deg[v]; i++) badj[v][i] = adj[v][i];
    }
}

static void restore_snap(void) {
    for (int v = 0; v < n; v++) memset(A[v], 0, (size_t)n);
    n = bn;
    for (int v = 0; v < n; v++) {
        deg[v] = bdeg[v];
        col[v] = bcol[v];
        for (int i = 0; i < deg[v]; i++) {
            adj[v][i] = badj[v][i];
            A[v][adj[v][i]] = 1;
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 10; i++) rnd64();

    if (d < 1 || d > MAXD || D < 2) { printf("0 0\n"); return 0; }

    int N0, M0;
    if (scanf("%d %d", &N0, &M0) != 2 || N0 < 1 || N0 > MAXN) { printf("0 0\n"); return 0; }
    n = N0;
    for (int i = 0; i < M0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) continue;
        if (deg[u] >= d || deg[v] >= d || A[u][v]) continue;
        add_edge(u, v);
    }

    /* 2-colour by BFS */
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

    clock_t t0 = clock();
    clock_t tend = t0 + (clock_t)(budget * (double)CLOCKS_PER_SEC);

    if (bad_pairs() == 0) {
        fill_spare(200000);
        save_snap();
        int fails = 0;
        while (clock() < tend && n < MAXN - 2) {
            insert_vertex(rndi(2));
            if (anneal(15000, 1.0, 0.05, tend)) {
                save_snap();
                fails = 0;
            } else {
                restore_snap();
                if (++fails > 40) break;
            }
        }
        restore_snap();
    }

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


def _c_improve(graph, d, D, seed, budget):
    """Run the C annealer from graph; return (n, edges) or None on any failure."""
    if graph is None or budget < 1.0 or graph[0] > 1900 or d > 64:
        return None
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                        stdin_graph=(graph[0], graph[1]), timeout=budget + 8.0)
        n2, e2 = lib.parse_graph_text(out)
    except Exception:
        return None
    if n2 < 1:
        return None
    return n2, e2


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
    """Conic (plus nucleus for even q) as a point-index set: an arc."""
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Driver.
#   0.00-0.15  arc-extended PG graphs and GQ (D >= 4) as starting points
#   0.15-0.85  C annealing with vertex insertion, started from the best graph
#   always     K_{d,d} fallback, validated before returning
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()

    def elapsed():
        return time.monotonic() - start

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(g):
        nonlocal best, best_n
        if g is None:
            return
        n, e = g
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        for g in _arc_extensions(d, start + 0.15 * time_limit,
                                 random.Random(seed * 7919 + d)):
            consider(g)
    if D >= 4:
        consider(_best_gq(d))

    if D >= 3:
        budget = 0.82 * time_limit - elapsed()
        consider(_c_improve(best, d, D, seed, budget))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
