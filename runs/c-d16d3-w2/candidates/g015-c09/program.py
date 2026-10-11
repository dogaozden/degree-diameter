import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: greedy ball-cover insertion, then annealed vertex growth.
#
# State: a valid bipartite graph with max degree d and diameter <= D.
# Growth step:
#   1. Try greedy ball-cover insertion (R = D-1 balls, spare-degree neighbours).
#   2. If that fails, add a vertex of random side and run simulated annealing
#      on the cost B = number of unordered vertex pairs at distance > D.
#      Moves: move one endpoint of an edge to another vertex of the opposite
#      class, add a cross edge, or delete a cross edge. Bipartiteness and the
#      degree cap are maintained by construction.
#   3. If cost reaches 0, snapshot the graph. Otherwise restore the snapshot.
# The output is always the last snapshot (a verified valid graph).
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>

#define MAXN 1024
#define MAXD 64
#define MAXW (MAXN / 64)
#define MAXM (MAXN * MAXD / 2)

static int n, d, D, W;
static int deg[MAXN];
static int adj[MAXN][MAXD];
static int col[MAXN];
static uint64_t reach[MAXN][MAXW];
static uint64_t nxt[MAXN][MAXW];
static uint64_t rs = 88172645463325252ULL;

static int bn;
static int bcol[MAXN];
static int bm;
static int bE[MAXM][2];

static double budget;
static clock_t t0;

static uint32_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return (uint32_t)(rs >> 16);
}

static double u01(void) {
    return (rnd() % 1000000u) / 1000000.0;
}

static double elapsed(void) {
    return (double)(clock() - t0) / CLOCKS_PER_SEC;
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

static void remove_half(int u, int v) {
    for (int i = 0; i < deg[u]; i++) {
        if (adj[u][i] == v) {
            adj[u][i] = adj[u][--deg[u]];
            return;
        }
    }
}

static void remove_edge(int u, int v) {
    remove_half(u, v);
    remove_half(v, u);
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

/* Number of unordered pairs at distance > D (unreachable pairs included). */
static long cost_now(void) {
    compute_balls(D);
    long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(reach[v][w]);
        bad += n - c;
    }
    return bad / 2;
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

/* Greedy insertion of a new vertex of class `side` whose neighbours cover all
   vertices within distance D-1. Requires compute_balls(D-1) to be current. */
static int try_insert(int side) {
    static int cand[MAXN];
    static int used[MAXN];
    int nc = 0;
    for (int u = 0; u < n; u++)
        if (col[u] == 1 - side && deg[u] < d) cand[nc++] = u;
    if (nc == 0) return 0;
    for (int i = nc - 1; i > 0; i--) {
        int j = (int)(rnd() % (uint32_t)(i + 1));
        int t = cand[i]; cand[i] = cand[j]; cand[j] = t;
    }
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
    W = (n + 63) >> 6;
    col[w] = side;
    deg[w] = 0;
    for (int i = 0; i < nch; i++) add_edge(chosen[i], w);
    return 1;
}

static void snapshot(void) {
    bn = n;
    bm = 0;
    for (int v = 0; v < n; v++) bcol[v] = col[v];
    for (int u = 0; u < n; u++)
        for (int i = 0; i < deg[u]; i++)
            if (adj[u][i] > u && bm < MAXM) {
                bE[bm][0] = u;
                bE[bm][1] = adj[u][i];
                bm++;
            }
}

static void restore(void) {
    n = bn;
    W = (n + 63) >> 6;
    for (int v = 0; v < n; v++) {
        deg[v] = 0;
        col[v] = bcol[v];
    }
    for (int i = 0; i < bm; i++) add_edge(bE[i][0], bE[i][1]);
}

/* Simulated annealing on bad-pair cost. Returns 1 when cost reaches 0. */
static int sa_steps(long steps) {
    long cur = cost_now();
    if (cur == 0) return 1;
    for (long t = 0; t < steps; t++) {
        if (elapsed() > budget) return 0;
        double T = 0.25 + 1.0 * (1.0 - (double)t / (double)steps);
        int mv = (int)(rnd() % 10u);
        if (mv < 6) {
            /* move one endpoint of an existing edge */
            int u = (int)(rnd() % (uint32_t)n);
            if (deg[u] == 0) continue;
            int v = adj[u][rnd() % (uint32_t)deg[u]];
            int x = -1;
            for (int k = 0; k < 30 && x < 0; k++) {
                int c = (int)(rnd() % (uint32_t)n);
                if (col[c] == col[u] || c == v || deg[c] >= d || has_edge(u, c)) continue;
                x = c;
            }
            if (x < 0) continue;
            remove_edge(u, v);
            add_edge(u, x);
            long nc = cost_now();
            if (nc <= cur || u01() < exp(-(double)(nc - cur) / T)) {
                cur = nc;
                if (cur == 0) return 1;
            } else {
                remove_edge(u, x);
                add_edge(u, v);
            }
        } else if (mv < 9) {
            /* add a cross edge between spare vertices */
            int u = (int)(rnd() % (uint32_t)n);
            if (deg[u] >= d) continue;
            int x = -1;
            for (int k = 0; k < 30 && x < 0; k++) {
                int c = (int)(rnd() % (uint32_t)n);
                if (c == u || col[c] == col[u] || deg[c] >= d || has_edge(u, c)) continue;
                x = c;
            }
            if (x < 0) continue;
            add_edge(u, x);
            long nc = cost_now();
            if (nc <= cur || u01() < exp(-(double)(nc - cur) / T)) {
                cur = nc;
                if (cur == 0) return 1;
            } else {
                remove_edge(u, x);
            }
        } else {
            /* delete a cross edge */
            int u = (int)(rnd() % (uint32_t)n);
            if (deg[u] == 0) continue;
            int v = adj[u][rnd() % (uint32_t)deg[u]];
            remove_edge(u, v);
            long nc = cost_now();
            if (nc <= cur || u01() < exp(-(double)(nc - cur) / T)) {
                cur = nc;
                if (cur == 0) return 1;
            } else {
                add_edge(u, v);
            }
        }
    }
    return cur == 0;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    budget = atof(argv[4]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int k = 0; k < 5; k++) rnd();

    if (d < 1 || d > MAXD || D < 2) { printf("0 0\n"); return 0; }

    int N0, M0;
    if (scanf("%d %d", &N0, &M0) != 2) { printf("0 0\n"); return 0; }
    if (N0 < 1 || N0 > MAXN - 2) { printf("0 0\n"); return 0; }
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

    t0 = clock();
    if (cost_now() != 0) { printf("0 0\n"); return 0; }
    snapshot();

    int fails = 0;
    while (elapsed() < budget && fails < 40 && n < MAXN - 2) {
        W = (n + 63) >> 6;
        compute_balls(D - 1);
        int s0 = (int)(rnd() & 1u);
        if (try_insert(s0) || try_insert(1 - s0)) {
            if (cost_now() == 0) {
                snapshot();
                fails = 0;
            } else {
                restore();
            }
            continue;
        }
        int side = (int)(rnd() & 1u);
        col[n] = side;
        deg[n] = 0;
        n++;
        W = (n + 63) >> 6;
        long steps = 4000 + (long)(rnd() % 4000u);
        if (sa_steps(steps)) {
            snapshot();
            fails = 0;
        } else {
            fails++;
            restore();
        }
    }

    printf("%d %d\n", bn, bm);
    for (int i = 0; i < bm; i++) printf("%d %d\n", bE[i][0], bE[i][1]);
    return 0;
}
"""


def _c_grow(graph, d, D, seed, budget):
    """Run the C growth engine from graph; return (n, edges) or None on any failure."""
    if graph is None or budget < 1.0:
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
#
# Start from PG(2, q) incidence (points 0..m-1, lines m..2m-1), degree q+1,
# spare s = d - q - 1. Choose point set SA (each line holds <= s of them) and
# line set SB (each point lies on <= s of them). Each chosen point gets a new
# A-vertex joined to its q+1 lines; each chosen line gets a new B-vertex joined
# to its q+1 points.
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
    """Conic plus (0,0,1): an arc with q+1 points, no three collinear."""
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
# Driver: arc-extended PG graph first, then C annealed growth from the best
# verified graph. Falls back to K_{d,d} (diameter 2, valid for D >= 2).
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    if D >= 3:
        cands = _arc_extensions(d, start + 0.05 * time_limit,
                                random.Random(seed * 7919 + d))
        for g in sorted(cands, key=lambda t: -t[0]):
            if g[0] > best_n and lib.is_valid(g[0], g[1], d, D):
                best, best_n = g, g[0]
                break

    left = 0.80 * time_limit - (time.monotonic() - start) - 1.0
    if left >= 1.0:
        g = _c_grow(best, d, D, seed, left)
        if g is not None and g[0] > best_n and lib.is_valid(g[0], g[1], d, D):
            best, best_n = g, g[0]

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
