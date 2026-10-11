import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine A (general D, used for D >= 4): greedy vertex insertion with
# ball-cover certificates. Kept from the parent for D != 3.
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
    int w = n;
    n++;
    col[w] = side;
    deg[w] = 0;
    for (int i = 0; i < nch; i++) add_edge(chosen[i], w);
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;

    if (d < 1 || d > MAXD || D < 2) { printf("0 0\n"); return 0; }

    int N0, M0;
    if (scanf("%d %d", &N0, &M0) != 2) { printf("0 0\n"); return 0; }
    if (N0 < 1 || N0 > MAXN) { printf("0 0\n"); return 0; }
    n = N0;
    W = (n + 63) >> 6;
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

    clock_t t0 = clock();
    int fails = 0;
    const int maxfails = 200;
    while (fails < maxfails && n < MAXN) {
        if ((double)(clock() - t0) / CLOCKS_PER_SEC > budget) break;
        W = (n + 63) >> 6;
        compute_balls(D - 1);
        int sides[2] = {0, 1};
        if (rnd() & 1u) { sides[0] = 1; sides[1] = 0; }
        int ok = 0;
        for (int k = 0; k < 2 && !ok; k++) ok = try_insert(sides[k]);
        if (ok) { fails = 0; continue; }
        fails++;
        for (int t = 0; t < 50; t++) {
            int u = (int)(rnd() % (uint32_t)n);
            int v = (int)(rnd() % (uint32_t)n);
            if (u == v || col[u] == col[v]) continue;
            if (deg[u] >= d || deg[v] >= d || has_edge(u, v)) continue;
            add_edge(u, v);
            break;
        }
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


def _c_augment(graph, d, D, seed, budget):
    """Run the C insertion engine on graph; return (n, edges) or None on any failure."""
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
# C engine B (D = 3, new in this version): edge-based simulated annealing on
# the "common neighbour" formulation.
#
# For a bipartite graph, if every two vertices on the same side have a common
# neighbour, then the diameter is at most 3: same-side pairs are at distance 2,
# and for a cross pair (P, L) pick any neighbour Q of L; P and Q share a
# neighbour l, giving the path P - l - Q - L. So the state is valid iff
# U = 0, where U counts same-side pairs with no common neighbour.
#
# The search keeps all degrees <= d and maintains common-neighbour counts
# incrementally. Moves: move an edge endpoint to another vertex on the same
# side (SA with Metropolis acceptance), add a spare edge, or remove an edge.
# Rounds add one new vertex (greedy coverage), anneal to U = 0, and either
# save the new valid state or restore the last valid one.
# ----------------------------------------------------------------------------

C_SA_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>

#define MAXN 1024
#define MAXD 64
#define ROUND_ITERS 600000L

static int n, d;
static int col[MAXN];
static int deg[MAXN];
static int adj[MAXN][MAXD];
static int cnt[MAXN][MAXN];
static long U;
static int snap_n;
static int snap_deg[MAXN];
static int snap_adj[MAXN][MAXD];
static uint64_t rs = 88172645463325252ULL;
static clock_t T_START;
static double BUDGET;

static uint32_t rnd32(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return (uint32_t)(rs >> 11);
}

static int rndint(int m) { return (int)(rnd32() % (uint32_t)m); }

static double rnd01(void) { return (double)(rnd32() & 0xFFFFFFu) / 16777216.0; }

static double elapsed(void) { return (double)(clock() - T_START) / CLOCKS_PER_SEC; }

static int is_adj(int a, int b) {
    for (int i = 0; i < deg[a]; i++) if (adj[a][i] == b) return 1;
    return 0;
}

static void arc_add(int a, int b) { adj[a][deg[a]++] = b; }

static void arc_del(int a, int b) {
    for (int i = 0; i < deg[a]; i++) {
        if (adj[a][i] == b) {
            adj[a][i] = adj[a][--deg[a]];
            return;
        }
    }
}

/* a, b are on the same side. */
static void inc_pair(int a, int b) {
    if (cnt[a][b]++ == 0) U--;
    cnt[b][a] = cnt[a][b];
}

static void dec_pair(int a, int b) {
    if (--cnt[a][b] == 0) U++;
    cnt[b][a] = cnt[a][b];
}

/* x and y on opposite sides, not adjacent, both with spare degree. */
static void edge_add(int x, int y) {
    for (int i = 0; i < deg[y]; i++) {
        int z = adj[y][i];
        if (z != x) inc_pair(x, z);
    }
    for (int i = 0; i < deg[x]; i++) {
        int w = adj[x][i];
        if (w != y) inc_pair(y, w);
    }
    arc_add(x, y);
    arc_add(y, x);
}

static void edge_del(int x, int y) {
    arc_del(x, y);
    arc_del(y, x);
    for (int i = 0; i < deg[y]; i++) {
        int z = adj[y][i];
        if (z != x) dec_pair(x, z);
    }
    for (int i = 0; i < deg[x]; i++) {
        int w = adj[x][i];
        if (w != y) dec_pair(y, w);
    }
}

static void rebuild(void) {
    for (int i = 0; i < n; i++)
        for (int j = 0; j < n; j++) cnt[i][j] = 0;
    for (int y = 0; y < n; y++)
        for (int i = 0; i < deg[y]; i++)
            for (int j = 0; j < deg[y]; j++)
                if (i != j) cnt[adj[y][i]][adj[y][j]]++;
    U = 0;
    for (int a = 0; a < n; a++)
        for (int b = a + 1; b < n; b++)
            if (col[a] == col[b] && cnt[a][b] == 0) U++;
}

static void add_vertex(int c) {
    int v = n++;
    col[v] = c;
    deg[v] = 0;
    for (int j = 0; j < n; j++) {
        cnt[v][j] = 0;
        cnt[j][v] = 0;
    }
    for (int j = 0; j < v; j++)
        if (col[j] == c) U++;
}

static void greedy_connect(int v) {
    for (int k = 0; k < d; k++) {
        if (deg[v] >= d) break;
        long bestkey = -1;
        int best = -1;
        int start = rndint(n);
        for (int t = 0; t < n; t++) {
            int y = start + t;
            if (y >= n) y -= n;
            if (col[y] == col[v] || deg[y] >= d || is_adj(v, y)) continue;
            long g = 0;
            for (int i = 0; i < deg[y]; i++) {
                int z = adj[y][i];
                if (cnt[v][z] == 0) g++;
            }
            long key = g * 4096 + rndint(4096);
            if (key > bestkey) {
                bestkey = key;
                best = y;
            }
        }
        if (best < 0) break;
        edge_add(v, best);
    }
}

static void save_snap(void) {
    snap_n = n;
    for (int i = 0; i < n; i++) {
        snap_deg[i] = deg[i];
        memcpy(snap_adj[i], adj[i], sizeof(int) * (size_t)deg[i]);
    }
}

static void restore_snap(void) {
    n = snap_n;
    for (int i = 0; i < n; i++) {
        deg[i] = snap_deg[i];
        memcpy(adj[i], snap_adj[i], sizeof(int) * (size_t)deg[i]);
    }
    rebuild();
}

/* Returns 1 when U == 0 (valid state), 0 on iteration or time exhaustion. */
static int anneal(long iters, double T0, double T1) {
    double T = T0;
    double lr = log(T1 / T0);
    for (long it = 0; it < iters; it++) {
        if (U == 0) return 1;
        if ((it & 1023) == 0) {
            if (elapsed() > BUDGET) return 0;
            T = T0 * exp(lr * (double)it / (double)iters);
        }
        int r = rndint(100);
        long before = U;
        if (r < 60) {
            int x = rndint(n);
            if (deg[x] == 0) continue;
            int y = adj[x][rndint(deg[x])];
            int y2 = rndint(n);
            if (y2 == y || col[y2] != col[y] || deg[y2] >= d || is_adj(x, y2)) continue;
            edge_del(x, y);
            edge_add(x, y2);
            long delta = U - before;
            if (!(delta <= 0 || rnd01() < exp(-(double)delta / T))) {
                edge_del(x, y2);
                edge_add(x, y);
            }
        } else if (r < 90) {
            int x = rndint(n);
            int y = rndint(n);
            if (col[x] == col[y] || deg[x] >= d || deg[y] >= d || is_adj(x, y)) continue;
            edge_add(x, y);
        } else {
            int x = rndint(n);
            if (deg[x] == 0) continue;
            int y = adj[x][rndint(deg[x])];
            edge_del(x, y);
            long delta = U - before;
            if (!(delta <= 0 || rnd01() < exp(-(double)delta / T))) edge_add(x, y);
        }
    }
    return U == 0;
}

int main(int argc, char **argv) {
    if (argc < 4) return 1;
    d = atoi(argv[1]);
    unsigned long seed = strtoul(argv[2], NULL, 10);
    BUDGET = atof(argv[3]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) rnd32();

    if (d < 1 || d > MAXD) { printf("0 0\n"); return 0; }

    int N0, M0;
    if (scanf("%d %d", &N0, &M0) != 2) { printf("0 0\n"); return 0; }
    if (N0 < 1 || N0 > MAXN - 8) { printf("0 0\n"); return 0; }
    n = N0;
    for (int i = 0; i < M0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) continue;
        if (deg[u] >= d || deg[v] >= d || is_adj(u, v)) continue;
        arc_add(u, v);
        arc_add(v, u);
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
    /* Keep only cross-side edges (input is bipartite, so this is a no-op). */
    for (int u = 0; u < n; u++) {
        int k = 0;
        for (int i = 0; i < deg[u]; i++)
            if (col[adj[u][i]] != col[u]) adj[u][k++] = adj[u][i];
        deg[u] = k;
    }

    T_START = clock();
    rebuild();
    int have = 0;
    if (U == 0) {
        save_snap();
        have = 1;
    } else if (anneal(ROUND_ITERS, 1.0, 0.05)) {
        save_snap();
        have = 1;
    }
    if (!have) { printf("0 0\n"); return 0; }

    int fails = 0;
    while (elapsed() < BUDGET && n < MAXN - 2) {
        add_vertex(rndint(2));
        greedy_connect(n - 1);
        if (anneal(ROUND_ITERS, 1.0, 0.05)) {
            save_snap();
            fails = 0;
        } else {
            restore_snap();
            if (++fails > 300) break;
        }
    }
    if (U != 0) restore_snap();

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


def _c_sa(graph, d, seed, budget):
    """Run the D = 3 annealing engine from graph; return (n, edges) or None on failure."""
    if graph is None or budget < 1.0 or d > 64:
        return None
    try:
        out = lib.run_c(C_SA_SOURCE, [d, seed, round(budget, 2)],
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
# Start from PG(2, q) incidence (points 0..m-1, lines m..2m-1). Each old vertex
# has degree q+1, so spare s = d - q - 1.
#
# A-side: a set SA of points; each P in SA gets a new vertex joined to the q+1
# lines through P. Every line may hold at most s points of SA.
# B-side: a set SB of lines; each j in SB gets a new vertex joined to the q+1
# points on j. Every point may lie on at most s lines of SB.
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
    """True if every target is hit by <= s elements of S, where element x hits nbr[x]."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomized greedy choice of elements so that every target is hit <= s times."""
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
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Simulated annealing over bi-Cayley voltage lifts (general D, parent's code).
# Vertices: A_i,g = i*G + g and B_j,h = (k+j)*G + h.
# Dart (i, j, s) joins A_i,g to B_j,mul(g,s) for every g in the group.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    for _ in range(80):
        k2 = rng.choice([1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12])
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in rng.sample(range(1, m), min(m - 1, 60))
                     if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def _right_perm(mul, G, s):
    """Permutation g -> mul(g, s) of the group."""
    return [mul(g, s) for g in range(G)]


def _cost(k, G, D, darts, perms):
    """Number of (representative, vertex) pairs not reached within distance D. Zero means valid."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        base_a = i * G
        base_b = (k + j) * G
        for g in range(G):
            a = base_a + g
            b = base_b + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in reps:
        seen = [False] * N
        seen[src] = True
        frontier = [src]
        count = 1
        for _ in range(D):
            nx = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = True
                        nx.append(v)
            count += len(nx)
            frontier = nx
            if not frontier:
                break
        total += N - count
    return total


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    """Simulated annealing over voltages and per-layer B-assignments."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

    T = 1.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.997)

        if rng.random() < 0.7 or k == 1:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_perm = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = _right_perm(mul, G, new_s)
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_perm
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _edges(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# Driver.
#
# D = 3 (the targets): arc-extended PG graphs, then the C common-neighbour
# annealer grows the best arc graph for ~90% of the budget. Every candidate
# is checked with lib.is_valid, and the largest valid graph is returned.
#
# D != 3: the parent's plan (C insertion, GQ baseline, voltage annealing).
# ----------------------------------------------------------------------------

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

    if D >= 3:
        arcs = _arc_extensions(d, start + 0.10 * time_limit,
                               random.Random(seed * 7919 + d))
        arcs.sort(key=lambda t: -t[0])
        for g in arcs:
            consider(g)

    if D == 3:
        # Bold path: annealing on the common-neighbour formulation.
        # Skip when the Moore bound is already met (e.g. d = 3, D = 3 gives 14).
        moore = lib.moore_bound(d, D)
        if best_n < moore:
            rem = 0.90 * time_limit - elapsed() - 2.0
            consider(_c_sa(best, d, seed, rem))
    else:
        if D >= 3:
            consider(_c_augment(best, d, D, seed,
                                max(0.5, 0.30 * time_limit - elapsed())))

        if D >= 4 and elapsed() < 0.40 * time_limit:
            gq = _best_gq(d)
            if gq is not None:
                consider(gq)

        anneal_end = start + 0.70 * time_limit
        ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
        while time.monotonic() < anneal_end:
            k = rng.choice(ks)
            base = best_n // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, anneal_end, iters=400)
            if res is not None:
                consider(res)

        if D >= 3:
            rem = 0.86 * time_limit - elapsed()
            if rem > 1.0:
                consider(_c_augment(best, d, D, seed + 1, rem))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
