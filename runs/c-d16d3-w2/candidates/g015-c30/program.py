import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: local search over valid bipartite graphs.
#
# State: a valid graph (every pair within distance D). Moves:
#   * degree-preserving 2-switch on cross edges, then a full distance check;
#   * adding a spare cross edge (always keeps validity, distances only shrink).
# After each move, greedy insertion adds vertices. A new vertex w joined to a
# set N on the opposite side is within distance D of every old vertex x that
# lies in the (D-1)-ball of some u in N, so insertion keeps validity. A move is
# accepted if the vertex count does not drop; small drops are accepted rarely.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXN 1024
#define MAXD 40
#define MAXW (MAXN / 64)

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    int col[MAXN];
} State;

static State g, snap, best;
static int d, D, W;
static uint64_t reach[MAXN][MAXW];
static uint64_t nxt[MAXN][MAXW];
static int used[MAXN];
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
    for (int i = 0; i < g.deg[u]; i++) if (g.adj[u][i] == v) return 1;
    return 0;
}

static void add_edge(int u, int v) {
    g.adj[u][g.deg[u]++] = v;
    g.adj[v][g.deg[v]++] = u;
}

static void drop_from(int u, int v) {
    for (int i = 0; i < g.deg[u]; i++) {
        if (g.adj[u][i] == v) {
            g.adj[u][i] = g.adj[u][g.deg[u] - 1];
            g.deg[u]--;
            return;
        }
    }
}

static void remove_edge(int u, int v) {
    drop_from(u, v);
    drop_from(v, u);
}

static void copy_state(State *dst, const State *src) {
    dst->n = src->n;
    memcpy(dst->deg, src->deg, sizeof(int) * src->n);
    memcpy(dst->col, src->col, sizeof(int) * src->n);
    for (int v = 0; v < src->n; v++)
        memcpy(dst->adj[v], src->adj[v], sizeof(int) * MAXD);
}

static void compute_balls(int R) {
    W = (g.n + 63) >> 6;
    for (int v = 0; v < g.n; v++) {
        for (int w = 0; w < W; w++) reach[v][w] = 0;
        reach[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < R; r++) {
        for (int v = 0; v < g.n; v++) {
            for (int w = 0; w < W; w++) nxt[v][w] = reach[v][w];
            for (int i = 0; i < g.deg[v]; i++) {
                int u = g.adj[v][i];
                for (int w = 0; w < W; w++) nxt[v][w] |= reach[u][w];
            }
        }
        for (int v = 0; v < g.n; v++)
            for (int w = 0; w < W; w++) reach[v][w] = nxt[v][w];
    }
}

static uint64_t wmask(int w) {
    if (w < W - 1) return ~0ULL;
    int r = g.n - 64 * (W - 1);
    return (r >= 64) ? ~0ULL : ((1ULL << r) - 1);
}

static int covered(const uint64_t *cov) {
    for (int w = 0; w < W; w++)
        if ((cov[w] & wmask(w)) != wmask(w)) return 0;
    return 1;
}

static int full_check(void) {
    compute_balls(D);
    for (int v = 0; v < g.n; v++)
        for (int w = 0; w < W; w++)
            if ((reach[v][w] & wmask(w)) != wmask(w)) return 0;
    return 1;
}

static int try_insert(int side) {
    static int cand[MAXN];
    int nc = 0;
    for (int u = 0; u < g.n; u++)
        if (g.col[u] == 1 - side && g.deg[u] < d) cand[nc++] = u;
    if (nc == 0) return 0;
    for (int i = nc - 1; i > 0; i--) {
        int j = (int)(rnd() % (uint32_t)(i + 1));
        int t = cand[i]; cand[i] = cand[j]; cand[j] = t;
    }
    for (int i = 0; i < g.n; i++) used[i] = 0;
    uint64_t cov[MAXW];
    for (int w = 0; w < W; w++) cov[w] = 0;
    int chosen[MAXD];
    int nch = 0;
    while (nch < d && !covered(cov)) {
        int bu = -1, bg = 0;
        for (int i = 0; i < nc; i++) {
            int u = cand[i];
            if (used[u]) continue;
            int gain = 0;
            for (int w = 0; w < W; w++) gain += popc(reach[u][w] & ~cov[w]);
            if (gain > bg) { bg = gain; bu = u; }
        }
        if (bu < 0) break;
        used[bu] = 1;
        chosen[nch++] = bu;
        for (int w = 0; w < W; w++) cov[w] |= reach[bu][w];
    }
    if (nch == 0 || !covered(cov)) return 0;
    int w = g.n;
    g.n++;
    g.col[w] = side;
    g.deg[w] = 0;
    for (int i = 0; i < nch; i++) add_edge(chosen[i], w);
    return 1;
}

static void fill(void) {
    int fails = 0;
    while (fails < 2 && g.n < MAXN - 1) {
        compute_balls(D - 1);
        int first = (int)(rnd() & 1u);
        if (try_insert(first) || try_insert(1 - first)) fails = 0;
        else fails++;
    }
}

/* Degree-preserving 2-switch on cross edges (a,b),(c,e) -> (a,e),(c,b). */
static int swap_move(void) {
    for (int t = 0; t < 30; t++) {
        int a = (int)(rnd() % (uint32_t)g.n);
        if (g.col[a] != 0 || g.deg[a] == 0) continue;
        int b = g.adj[a][rnd() % (uint32_t)g.deg[a]];
        int c = (int)(rnd() % (uint32_t)g.n);
        if (g.col[c] != 0 || g.deg[c] == 0) continue;
        int e = g.adj[c][rnd() % (uint32_t)g.deg[c]];
        if (a == c || b == e) continue;
        if (has_edge(a, e) || has_edge(c, b)) continue;
        remove_edge(a, b);
        remove_edge(c, e);
        add_edge(a, e);
        add_edge(c, b);
        return 1;
    }
    return 0;
}

static void add_random_edge(void) {
    for (int t = 0; t < 50; t++) {
        int u = (int)(rnd() % (uint32_t)g.n);
        int v = (int)(rnd() % (uint32_t)g.n);
        if (g.col[u] != 0 || g.col[v] != 1) continue;
        if (g.deg[u] >= d || g.deg[v] >= d || has_edge(u, v)) continue;
        add_edge(u, v);
        return;
    }
}

static int qbuf[MAXN];

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;

    if (d < 1 || d > MAXD - 1 || D < 1) { printf("0 0\n"); return 0; }

    int N0, M0;
    if (scanf("%d %d", &N0, &M0) != 2) { printf("0 0\n"); return 0; }
    if (N0 < 1 || N0 > MAXN - 2) { printf("0 0\n"); return 0; }
    g.n = N0;
    for (int i = 0; i < M0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= N0 || v >= N0 || u == v) continue;
        if (g.deg[u] >= d || g.deg[v] >= d || has_edge(u, v)) continue;
        add_edge(u, v);
    }

    for (int s = 0; s < g.n; s++) g.col[s] = -1;
    for (int s = 0; s < g.n; s++) {
        if (g.col[s] >= 0) continue;
        g.col[s] = 0;
        int qh = 0, qt = 0;
        qbuf[qt++] = s;
        while (qh < qt) {
            int u = qbuf[qh++];
            for (int i = 0; i < g.deg[u]; i++) {
                int v = g.adj[u][i];
                if (g.col[v] < 0) {
                    g.col[v] = 1 - g.col[u];
                    qbuf[qt++] = v;
                }
            }
        }
    }
    for (int u = 0; u < g.n; u++)
        for (int i = 0; i < g.deg[u]; i++)
            if (g.col[g.adj[u][i]] == g.col[u]) { printf("0 0\n"); return 0; }

    if (!full_check()) { printf("0 0\n"); return 0; }

    fill();
    copy_state(&best, &g);

    clock_t t0 = clock();
    while ((double)(clock() - t0) / CLOCKS_PER_SEC < budget) {
        copy_state(&snap, &g);
        int cur = g.n;
        int nm = 1 + (int)(rnd() % 3u);
        int swapped = 0;
        for (int k = 0; k < nm; k++) {
            if (rnd() % 4u == 0) add_random_edge();
            else swapped |= swap_move();
        }
        if (swapped && !full_check()) { copy_state(&g, &snap); continue; }
        fill();
        if (g.n < cur) {
            if (g.n < best.n - 2 || (rnd() % 100u) >= 2u) {
                copy_state(&g, &snap);
                continue;
            }
        }
        if (g.n > best.n) copy_state(&best, &g);
    }

    int m2 = 0;
    for (int u = 0; u < best.n; u++)
        for (int i = 0; i < best.deg[u]; i++)
            if (best.adj[u][i] > u) m2++;
    printf("%d %d\n", best.n, m2);
    for (int u = 0; u < best.n; u++)
        for (int i = 0; i < best.deg[u]; i++)
            if (best.adj[u][i] > u) printf("%d %d\n", u, best.adj[u][i]);
    return 0;
}
"""


def _c_improve(graph, d, D, seed, budget):
    """Run the C local search from graph; return (n, edges) or None on any failure."""
    if graph is None or budget < 1.0 or d > 39:
        return None
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                        stdin_graph=(graph[0], graph[1]), timeout=budget + 6.0)
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
# spare s = d - q - 1. New A-vertices (joined to the q+1 lines through a point
# in SA) and new B-vertices (joined to the q+1 points on a line in SB) are
# added. Each line may carry at most s A-attachments; each point at most s
# B-attachments. The two sides are independent.
#
# The sets SA and SB are found by a local search that swaps a single blocker
# out for a new element, rather than the one-shot greedy used before.
# ----------------------------------------------------------------------------

def _pg_data(q):
    """Return (m, edges, point_lines, line_points, index) for PG(2, q)."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    pts = lib.projective_points(q)
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, point_lines, line_points, index


def _loads_ok(S, s, m, nbr):
    """True if every target is hit by at most s elements of S."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _pack(m, s, nbr, rng, deadline, iters):
    """Largest-ish set S with every target hit <= s times, via greedy plus 1-for-1 swaps."""
    if s <= 0:
        return []
    holders = [set() for _ in range(m)]
    inS = [False] * m
    S = set()

    def add(x):
        inS[x] = True
        S.add(x)
        for t in nbr[x]:
            holders[t].add(x)

    def rem(x):
        inS[x] = False
        S.discard(x)
        for t in nbr[x]:
            holders[t].discard(x)

    order = list(range(m))
    rng.shuffle(order)
    for x in order:
        if all(len(holders[t]) < s for t in nbr[x]):
            add(x)
    best = list(S)
    for it in range(iters):
        if (it & 1023) == 0 and time.monotonic() > deadline:
            break
        x = rng.randrange(m)
        if inS[x]:
            continue
        full = [t for t in nbr[x] if len(holders[t]) >= s]
        if not full:
            add(x)
        else:
            swap_out = None
            for y in holders[full[0]]:
                if all(y in holders[t] for t in full):
                    swap_out = y
                    break
            if swap_out is None:
                continue
            rem(swap_out)
            add(x)
        if len(S) > len(best):
            best = list(S)
    return best


def _conic_set(q, index):
    """Conic (plus nucleus for even q): an arc with no three collinear."""
    F = lib.GF(q)
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


def _arc_candidates(d, deadline, rng):
    """Return (n, edges) candidates for each prime power q with q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        if s < 0:
            continue
        m, edges, point_lines, line_points, index = _pg_data(q)
        SA = _pack(m, s, point_lines, rng, deadline, 15000)
        SB = _pack(m, s, line_points, rng, deadline, 15000)
        if s >= 2:
            cs = _conic_set(q, index)
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

    covered_pairs = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered_pairs:
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
                        covered_pairs.add((p, r))

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
#   0.00-0.12  arc-extended PG graphs (local-search side selection)
#   0.12-0.20  GQ baseline (D >= 4 only)
#   0.20-0.80  C local search from the best valid graph found so far
# ----------------------------------------------------------------------------

def _build(d, D, seed, time_limit):
    start = time.monotonic()
    T = float(time_limit)
    rng = random.Random(seed)

    best = lib.haar_graph(d, range(d))  # K_{d,d}: diameter 2, valid for D >= 2
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
        try:
            for g in _arc_candidates(d, start + 0.12 * T, random.Random(seed * 7919 + d)):
                consider(g)
        except Exception:
            pass
    if D >= 4 and elapsed() < 0.2 * T:
        try:
            consider(_best_gq(d))
        except Exception:
            pass

    remaining = 0.80 * T - elapsed() - 1.0
    if remaining >= 2.0:
        consider(_c_improve(best, d, D, seed, remaining))

    return best


def build(d, D, seed, time_limit):
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    try:
        n, e = _build(d, D, seed, time_limit)
        if lib.is_valid(n, e, d, D):
            return n, e
    except Exception:
        pass
    fallback = lib.haar_graph(d, range(d))
    if lib.is_valid(fallback[0], fallback[1], d, D):
        return fallback
    return 1, []
