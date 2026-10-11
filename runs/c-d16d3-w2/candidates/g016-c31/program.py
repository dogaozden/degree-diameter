import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: validity-preserving ruin-and-recreate local search.
#
# Start from a valid graph. Each iteration saves the state, deletes 1-3 random
# vertices, then greedily re-inserts vertices (ball-cover insertion, as in the
# parent engine) with random cross edges between rounds to reshape the spare
# degree pattern. The result is kept only if a full all-pairs check (radius D
# bitsets) passes and the order did not drop. Plateau moves are accepted, so
# the search can drift across equal-order graphs. Adding a cross edge never
# breaks validity, so those edges are applied freely. The best valid graph
# seen is printed at the end.
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

static int sn;
static int sdeg[MAXN];
static int scol[MAXN];
static int sadj[MAXN][MAXD];

static int bn;
static int bdeg[MAXN];
static int badj[MAXN][MAXD];

static clock_t T0;

static double elapsed(void) {
    return (double)(clock() - T0) / CLOCKS_PER_SEC;
}

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
    col[w] = side;
    deg[w] = 0;
    for (int i = 0; i < nch; i++) add_edge(chosen[i], w);
    return 1;
}

/* Full validity: every vertex reaches all n vertices within distance D. */
static int full_ok(void) {
    W = (n + 63) >> 6;
    compute_balls(D);
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(reach[v][w]);
        if (c != n) return 0;
    }
    return 1;
}

static void save_state(void) {
    sn = n;
    memcpy(sdeg, deg, sizeof(int) * (size_t)n);
    memcpy(scol, col, sizeof(int) * (size_t)n);
    memcpy(sadj, adj, sizeof(adj[0]) * (size_t)n);
}

static void restore_state(void) {
    n = sn;
    memcpy(deg, sdeg, sizeof(int) * (size_t)n);
    memcpy(col, scol, sizeof(int) * (size_t)n);
    memcpy(adj, sadj, sizeof(adj[0]) * (size_t)n);
}

static void save_best(void) {
    bn = n;
    memcpy(bdeg, deg, sizeof(int) * (size_t)n);
    memcpy(badj, adj, sizeof(adj[0]) * (size_t)n);
}

/* Delete vertex v; the last vertex is moved into slot v. */
static void remove_vertex(int v) {
    for (int i = 0; i < deg[v]; i++) {
        int u = adj[v][i];
        for (int j = 0; j < deg[u]; j++) {
            if (adj[u][j] == v) {
                adj[u][j] = adj[u][deg[u] - 1];
                deg[u]--;
                break;
            }
        }
    }
    deg[v] = 0;
    int L = n - 1;
    if (v != L) {
        for (int i = 0; i < deg[L]; i++) {
            int u = adj[L][i];
            for (int j = 0; j < deg[u]; j++) {
                if (adj[u][j] == L) { adj[u][j] = v; break; }
            }
        }
        deg[v] = deg[L];
        memcpy(adj[v], adj[L], sizeof(int) * (size_t)deg[L]);
        col[v] = col[L];
    }
    deg[L] = 0;
    n--;
}

/* Adding cross edges never increases distances, so validity is kept. */
static void random_edges(int tries) {
    if (n < 2) return;
    for (int t = 0; t < tries; t++) {
        int u = (int)(rnd() % (uint32_t)n);
        int v = (int)(rnd() % (uint32_t)n);
        if (u == v || col[u] == col[v]) continue;
        if (deg[u] >= d || deg[v] >= d || has_edge(u, v)) continue;
        add_edge(u, v);
    }
}

static void print_graph(int nn, const int *dg, int (*ad)[MAXD]) {
    int m2 = 0;
    for (int u = 0; u < nn; u++)
        for (int i = 0; i < dg[u]; i++)
            if (ad[u][i] > u) m2++;
    printf("%d %d\n", nn, m2);
    for (int u = 0; u < nn; u++)
        for (int i = 0; i < dg[u]; i++)
            if (ad[u][i] > u) printf("%d %d\n", u, ad[u][i]);
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

    T0 = clock();
    if (!full_ok()) { print_graph(n, deg, adj); return 0; }
    save_best();
    save_state();

    /* Phase 1: greedy insertion. */
    int fails = 0;
    while (fails < 60 && n < MAXN && elapsed() < 0.3 * budget) {
        W = (n + 63) >> 6;
        compute_balls(D - 1);
        int sides[2] = {0, 1};
        if (rnd() & 1u) { sides[0] = 1; sides[1] = 0; }
        int ok = 0;
        for (int k = 0; k < 2 && !ok; k++) ok = try_insert(sides[k]);
        if (ok) { fails = 0; continue; }
        fails++;
        random_edges(20);
    }
    if (!full_ok()) restore_state();
    if (n > bn) save_best();

    /* Phase 2: ruin and recreate with plateau acceptance. */
    while (elapsed() < budget && n < MAXN) {
        save_state();
        int oldn = n;
        int k = 1 + (int)(rnd() % 3u);
        for (int i = 0; i < k && n > 2; i++)
            remove_vertex((int)(rnd() % (uint32_t)n));

        int f = 0;
        while (f < 3 && n < MAXN && elapsed() < budget) {
            W = (n + 63) >> 6;
            compute_balls(D - 1);
            int sides[2] = {0, 1};
            if (rnd() & 1u) { sides[0] = 1; sides[1] = 0; }
            int ok = 0;
            for (int q = 0; q < 2 && !ok; q++) ok = try_insert(sides[q]);
            if (ok) {
                f = 0;
            } else {
                f++;
                random_edges(8);
            }
        }

        int accept = 0;
        if (n >= oldn) {
            accept = full_ok();
        } else if (n == oldn - 1 && rnd() % 100u < 2u) {
            accept = full_ok();
        }
        if (!accept) {
            restore_state();
        } else {
            random_edges(10);
            if (n > bn) save_best();
        }
    }

    print_graph(bn, bdeg, badj);
    return 0;
}
"""


def _c_ils(graph, d, D, seed, budget):
    """Run the C ruin-and-recreate engine on graph; return (n, edges) or None on any failure."""
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
# Driver. Time plan (fractions of time_limit):
#   0.00-0.08  arc-extended PG graphs (A and B sets chosen independently)
#   0.08-0.15  generalized quadrangle baseline (D >= 4)
#   0.15-0.90  C ruin-and-recreate search from the best graph so far
# Calibration cases already at the Moore bound return immediately.
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

    def consider(g):
        nonlocal best
        if g is None:
            return
        n, e = g
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        for g in _arc_extensions(d, start + 0.08 * time_limit,
                                 random.Random(seed * 7919 + d)):
            consider(g)
    if D >= 4 and time.monotonic() - start < 0.15 * time_limit:
        consider(_best_gq(d))

    if best[0] < lib.moore_bound(d, D):
        budget = 0.90 * time_limit - (time.monotonic() - start) - 1.0
        consider(_c_ils(best, d, D, seed, budget))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
